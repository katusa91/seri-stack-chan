"""
xiaozhi_bridge.py - M5Stack 스택찬(xiaozhi 프로토콜) <-> token_server.py의 /pipe 모드 브리지

스택찬 펌웨어(xiaozhi 계열)는 서버와 두 가지로 통신한다.
  1) OTA 주소(POST/GET)  : 부팅 때 한 번. 응답에 '음성 WebSocket 주소'가 들어 있다.
  2) WebSocket           : JSON 제어 메시지(hello/listen/abort/tts/stt/llm) + Opus 오디오 프레임(바이너리)

이 모듈은 위 두 문을 token_server.py(Flask) 안에 달고, 한 턴을 이렇게 처리한다.
  기기 Opus(16kHz) -> PCM -> (서버 VAD로 말 끝 감지) -> WAV
  -> /api/pipe/chat (Gemini가 음성을 직접 듣고 대답, 기억/주식/타로/노래 함수 그대로)
  -> 문장 단위로 /api/tts (타입캐스트, 효과음 대체, 저장된 '알았어' 음성 그대로)
  -> 24kHz PCM -> Opus 60ms 프레임 -> 실시간 속도로 기기에 전송

taeyeon-pipe.html이 브라우저에서 하던 일(문장 자르기, TTS 병렬 요청, 순서대로 재생,
노래는 음성이 끝난 뒤 재생)을 서버 안에서 똑같이 한다. 라우트는 서버 안에서 직접 호출하므로
(Flask test_client) 별도 네트워크 왕복이 없고, 기존 로그인(GOOGLE_CLIENT_ID) 설정도 그대로 통과한다.

켜는 법: 환경변수 XIAOZHI_KEY(긴 임의 문자열)를 설정하면 켜진다. 비어 있으면 아무 라우트도 열지 않는다.
  기기의 Custom OTA URL:  https://<railway도메인>/xiaozhi/ota/?key=<XIAOZHI_KEY>
"""
import base64
import hashlib
import hmac
import json
import logging
import math
import os
import queue
import re
import struct
import subprocess
import threading
import time
import uuid
from collections import deque
from concurrent.futures import ThreadPoolExecutor

try:
    import opuslib
except Exception:  # libopus가 없으면 가져오기부터 실패한다
    opuslib = None
try:
    import webrtcvad
except Exception:
    webrtcvad = None
try:
    from flask import Response, jsonify, request
    from flask_sock import Sock
except Exception:
    Sock = None

log = logging.getLogger("xiaozhi")


def _env(name, default=""):
    return os.environ.get(name, default).strip()


def _env_int(name, default):
    try:
        return int(_env(name, str(default)))
    except ValueError:
        return default


def _env_float(name, default):
    try:
        return float(_env(name, str(default)))
    except ValueError:
        return default


# ----- 설정 (모두 환경변수, 기본값으로 바로 동작) -----
XZ_KEY = _env("XIAOZHI_KEY")                              # 필수. 비어 있으면 브리지 전체가 꺼진다
XZ_DEVICE_IDS = {d.strip().lower() for d in _env("XIAOZHI_DEVICE_IDS").split(",") if d.strip()}   # 기기 MAC 허용 목록 (선택)
XZ_WS_URL = _env("XIAOZHI_WS_URL")                        # 비우면 요청 주소로 wss://<host>/xiaozhi/v1/ 를 만든다
XZ_LAT, XZ_LNG = _env("XIAOZHI_LAT"), _env("XIAOZHI_LNG")  # 스택찬엔 GPS가 없어서 고정 위치(집)를 쓴다 (선택)
XZ_VOICE_ID = _env("XIAOZHI_VOICE_ID")                    # 비우면 서버 기본 목소리
VAD_KIND = _env("XIAOZHI_VAD", "webrtc").lower()         # webrtc | energy
VAD_MODE = max(0, min(3, _env_int("XIAOZHI_VAD_MODE", 2)))
VAD_END_MS = _env_int("XIAOZHI_VAD_END_MS", 900)          # 이만큼 조용하면 말이 끝난 것
MIN_SPEECH_MS = _env_int("XIAOZHI_MIN_SPEECH_MS", 300)    # 이보다 짧은 소리는 잡음으로 버림
MAX_UTT_S = _env_int("XIAOZHI_MAX_UTT_S", 30)
ENERGY_RMS = _env_int("XIAOZHI_ENERGY_RMS", 600)          # VAD=energy일 때 '말하는 중' 기준 크기
OUT_RATE = 24000                                          # /api/tts 출력 = 24kHz 16bit mono PCM
OUT_FRAME_MS = 60
OUT_FRAME_SAMPLES = OUT_RATE * OUT_FRAME_MS // 1000
PREBUFFER_FRAMES = _env_int("XIAOZHI_PREBUFFER", 5)       # 기기 큐가 약 2.4초라서 너무 앞서 보내면 버려진다
SONG_MAX_S = _env_int("XIAOZHI_SONG_MAX_S", 600)
MAX_TURNS_KEPT = 40
MIN_FIRST, MIN_NEXT = 8, 70                               # taeyeon-pipe.html과 같은 문장 자르기 기준

_pool = ThreadPoolExecutor(max_workers=6, thread_name_prefix="xz-tts")


# ===================== 보조 함수 =====================
def _device_token(device_id: str) -> str:
    return hmac.new(XZ_KEY.encode(), (device_id or "").lower().encode(), hashlib.sha256).hexdigest()[:32]


def _wav16k(pcm: bytes) -> bytes:
    n = len(pcm)
    return (b"RIFF" + struct.pack("<I", 36 + n) + b"WAVEfmt " + struct.pack("<IHHIIHH", 16, 1, 1, 16000, 32000, 2, 16)
            + b"data" + struct.pack("<I", n) + pcm)


def _rms(frame: bytes) -> float:
    s = memoryview(frame[:len(frame) - len(frame) % 2]).cast("h")
    return math.sqrt(sum(x * x for x in s) / len(s)) if len(s) else 0.0


_EMOJI = re.compile("[\U0001F000-\U0001FAFF\u2600-\u27BF\u2B00-\u2BFF\uFE0F\u200D]")
_TAG = re.compile(r"\[[^\[\]]{1,30}\]")


def _clean(t: str) -> str:
    t = _EMOJI.sub("", t)
    t = re.sub(r"[*_`#]+", "", t)
    return re.sub(r"\s+", " ", t).strip()


_CUT_RE = re.compile(r"[.!?~…。！？]+[\"'”’)\]]*(?=\s)|\n")


def _find_cut(s: str, first: bool) -> int:
    """taeyeon-pipe.html의 findCut과 같은 규칙: 첫 조각은 짧게(첫 소리 빨리), 이후는 3~4문장씩."""
    need = MIN_FIRST if first else MIN_NEXT
    for m in _CUT_RE.finditer(s):
        if len(s[:m.end()].strip()) >= need:
            return m.end()
    if first:
        m = re.search(r"[,，、](?=\s)", s)
        if m and m.start() >= 14:
            return m.start() + 1
    if len(s) > 160:
        sp = s.rfind(" ", 0, 161)
        if sp > 40:
            return sp
    return 0


_EMO = (  # (정규식, xiaozhi 감정 이름) - 첫 문장만 보고 얼굴 표정을 고르는 아주 단순한 규칙
    (re.compile(r"ㅋㅋ|하하|웃|\[laugh"), "laughing"),
    (re.compile(r"ㅠㅠ|ㅜㅜ|슬프|눈물|\[sob|\[cry"), "sad"),
    (re.compile(r"화나|짜증|\[angry"), "angry"),
    (re.compile(r"헉|깜짝|놀랐|\[gasp"), "surprised"),
    (re.compile(r"사랑|좋아해|보고 싶"), "loving"),
    (re.compile(r"고마|행복|좋아|기뻐|다행|\[happy"), "happy"),
)


def _guess_emotion(text: str) -> str:
    for rx, name in _EMO:
        if rx.search(text):
            return name
    return ""


# ===================== 말 끝 감지 (서버 VAD) =====================
class Endpointer:
    """16kHz mono PCM을 먹여서 '한 마디가 끝났는지' 판단한다. manual=True면 VAD 없이 모으기만 한다."""
    FR = 320  # 20ms

    def __init__(self, manual=False):
        self.manual = manual
        self.buf = bytearray()
        self.pre = deque(maxlen=15)       # 말 시작 앞 300ms (첫 음절이 잘리지 않게)
        self.recent = deque(maxlen=8)
        self.utt = bytearray()
        self.started = False
        self.voiced_ms = 0
        self.silence_ms = 0
        self.vad = webrtcvad.Vad(VAD_MODE) if (VAD_KIND == "webrtc" and webrtcvad) else None

    def _voiced(self, fr: bytes) -> bool:
        if self.vad:
            try:
                return self.vad.is_speech(fr, 16000)
            except Exception:
                pass
        return _rms(fr) >= ENERGY_RMS

    def feed(self, pcm: bytes):
        """끝났으면 PCM(bytes), 잡음이라 버렸으면 b"", 아직이면 None"""
        self.buf += pcm
        while len(self.buf) >= self.FR * 2:
            fr = bytes(self.buf[:self.FR * 2])
            del self.buf[:self.FR * 2]
            if self.manual:
                self.utt += fr
                if len(self.utt) >= MAX_UTT_S * 32000:
                    return self.finish()
                continue
            v = self._voiced(fr)
            if not self.started:
                self.pre.append(fr)
                self.recent.append(v)
                if sum(self.recent) >= 5:
                    self.started = True
                    self.utt = bytearray(b"".join(self.pre))
                    self.voiced_ms, self.silence_ms = sum(self.recent) * 20, 0
            else:
                self.utt += fr
                if v:
                    self.voiced_ms += 20
                    self.silence_ms = 0
                else:
                    self.silence_ms += 20
                if self.silence_ms >= VAD_END_MS or len(self.utt) >= MAX_UTT_S * 32000:
                    return self.finish()
        return None

    def finish(self):
        pcm = bytes(self.utt)
        ok = len(pcm) >= 0.4 * 32000 and (self.manual or self.voiced_ms >= MIN_SPEECH_MS)
        self.__init__(self.manual)
        return pcm if ok else b""


# ===================== 실시간 속도로 프레임 내보내기 =====================
class Pacer:
    """기기는 받은 프레임을 바로 재생 큐에 쌓고(약 2.4초 한도, 넘치면 버림), 서버가 앞서 보내면 안 된다.
    첫 PREBUFFER 프레임은 바로, 그 뒤는 재생 시간에 맞춰 보낸다. 합성이 늦어 소리가 끊긴 뒤에는 시계를 다시 맞춘다."""

    def __init__(self):
        self.start = None
        self.n = 0
        self.fd = OUT_FRAME_MS / 1000.0

    def wait(self, cancel: threading.Event):
        now = time.monotonic()
        if self.start is None or now - self.start > self.n * self.fd + 0.3:   # 처음이거나, 기기 재생이 비었던 뒤
            self.start, self.n = now, 0
        due = self.start + self.n * self.fd - PREBUFFER_FRAMES * self.fd
        if due > now:
            cancel.wait(due - now)
        self.n += 1


# ===================== 한 턴의 음성 출력 =====================
class Speaker:
    """/api/pipe/chat이 흘려주는 글자를 문장으로 잘라 /api/tts로 합성하고, 순서대로 Opus로 보낸다."""

    def __init__(self, sess, cancel):
        self.s, self.cancel = sess, cancel
        self.buf, self.sent, self.prev, self.carry = "", 0, "", ""
        self.q = queue.Queue()
        self.started = False
        self.last_emo = ""
        self.pacer = Pacer()
        self.enc = opuslib.Encoder(OUT_RATE, 1, opuslib.APPLICATION_AUDIO)
        self.th = threading.Thread(target=self._sender, daemon=True, name="xz-send")
        self.th.start()

    # --- 글자 입력 ---
    def feed(self, text):
        self.buf += text
        while True:
            cut = _find_cut(self.buf, self.sent == 0)
            if cut <= 0:
                break
            piece = self.buf[:cut]
            if piece.count("[") != piece.count("]"):
                break
            self.buf = self.buf[cut:]
            self._speak(piece)

    def filler(self, text):      # '잠시만요' 같은 한마디: 버퍼에 갇히지 않게 바로 읽는다
        rest, self.buf = self.buf, ""
        if rest.strip():
            self._speak(rest)
        self._speak(text)
        self.sent = 0

    def flush(self):
        rest, self.buf = self.buf, ""
        if rest.strip():
            self._speak(rest)
        self.sent, self.prev, self.carry = 0, "", ""

    def _speak(self, raw):
        text = _clean(raw)
        if not text or not re.search(r"\w", _TAG.sub(" ", text)):
            if text and _TAG.search(text):        # 태그([sighs])만 있는 조각은 다음 조각 앞에 붙인다
                self.carry = (self.carry + " " + text).strip()
            return
        if self.carry:
            text, self.carry = self.carry + " " + text, ""
        prev, self.prev = self.prev, text
        self.sent += 1
        self.q.put((text, _pool.submit(self.s.synth, text, prev)))

    # --- 소리 출력 ---
    def _begin(self):
        if not self.started:
            self.started = True
            self.s.send_json({"type": "tts", "state": "start"})

    def _sender(self):
        while True:
            item = self.q.get()
            if item is None:
                return
            if self.cancel.is_set():
                continue
            text, fut = item
            try:
                pcm = fut.result(timeout=50)
            except Exception as e:
                log.warning("[xiaozhi] 음성 합성 실패, 이 문장은 건너뜀: %s", e)
                continue
            if not pcm or self.cancel.is_set():
                continue
            self._begin()
            emo = _guess_emotion(text)      # 문장마다 보고, 표정이 바뀔 때만 보낸다 (기기 얼굴이 문장에 맞춰 변한다)
            if emo and emo != self.last_emo:
                self.last_emo = emo
                self.s.send_json({"type": "llm", "emotion": emo, "text": ""})
            self.s.send_json({"type": "tts", "state": "sentence_start", "text": _TAG.sub("", text).strip()})
            self.emit_pcm(pcm)

    def emit_pcm(self, pcm: bytes):
        fb = OUT_FRAME_SAMPLES * 2
        for off in range(0, len(pcm), fb):
            if self.cancel.is_set() or self.s.closed:
                return
            fr = pcm[off:off + fb]
            if len(fr) < fb:
                fr += b"\0" * (fb - len(fr))
            opus = self.enc.encode(fr, OUT_FRAME_SAMPLES)
            self.pacer.wait(self.cancel)
            if self.cancel.is_set():
                return
            self.s.send_audio(opus)

    def close(self):
        """남은 글자를 모두 읽고(소리를 다 보내고) 돌아온다."""
        self.q.put(None)
        self.th.join(timeout=300)

    def play_song(self, play: dict):
        title = " - ".join(x for x in (str(play.get("title") or ""), str(play.get("artist") or "")) if x) or "노래"
        self._begin()
        self.s.send_json({"type": "tts", "state": "sentence_start", "text": "♪ " + title})
        log.info("[xiaozhi] 노래 재생 시작: %s", title)
        try:
            for chunk in self.s.song_pcm(play, self.cancel):
                self.emit_pcm(chunk)
                if self.cancel.is_set():
                    break
        except Exception as e:
            log.warning("[xiaozhi] 노래 재생 실패: %s", e)

    def end(self):
        # 취소된 턴(끼어들기/abort)은 보내지 않는다: 이미 새 턴이 시작됐을 수 있어서, 늦게 도착한 stop이 새 대답을 끊는다
        if self.started and not self.cancel.is_set():
            self.s.send_json({"type": "tts", "state": "stop"})


# ===================== 기기 한 대(연결 한 번) =====================
class Session:
    def __init__(self, ws, app, device_id, version, auth_headers, error_text):
        self.ws, self.app, self.device_id = ws, app, device_id
        self.version = version if version in (1, 2, 3) else 1
        self.auth_headers = auth_headers
        self.error_text = error_text
        self.closed = False
        self.send_lock = threading.Lock()
        self.session_id = uuid.uuid4().hex
        self.dec = None
        self.in_rate, self.in_frame_ms = 16000, 60
        self.mode = "auto"
        self.ep = None
        self.busy = False
        self.cancel = threading.Event()
        self.turns = []
        self.ctx, self.sig, self.model_tags = "", "", False
        self.ctx_ready = threading.Event()
        self.t0 = time.monotonic()

    # --- 전송 ---
    def send_json(self, obj):
        if self.closed:
            return
        try:
            with self.send_lock:
                self.ws.send(json.dumps(obj, ensure_ascii=False))
        except Exception:
            self.closed = True

    def send_audio(self, opus: bytes):
        if self.closed:
            return
        ts = int((time.monotonic() - self.t0) * 1000) & 0xFFFFFFFF
        if self.version == 2:
            data = struct.pack(">HHIII", 2, 0, 0, ts, len(opus)) + opus
        elif self.version == 3:
            data = struct.pack(">BBH", 0, 0, len(opus)) + opus
        else:
            data = opus
        try:
            with self.send_lock:
                self.ws.send(data)
        except Exception:
            self.closed = True

    def _unpack(self, data: bytes) -> bytes:
        if self.version == 2:
            return data[16:] if len(data) > 16 and struct.unpack_from(">H", data, 2)[0] == 0 else b""
        if self.version == 3:
            return data[4:] if len(data) > 4 and data[0] == 0 else b""
        return data

    # --- 내부 라우트 호출 (같은 서버 안에서, 네트워크 없이) ---
    def _client(self):
        return self.app.test_client()

    def _prepare(self):
        try:
            r = self._client().post("/api/pipe/start", json={}, headers=self.auth_headers())
            d = r.get_json(silent=True) or {}
            self.ctx, self.sig, self.model_tags = d.get("ctx") or "", d.get("sig") or "", bool(d.get("modelTags"))
            log.info("[xiaozhi] 직전 대화 블록 준비 (%s자, status=%s)", len(self.ctx), r.status_code)
        except Exception as e:
            log.warning("[xiaozhi] /api/pipe/start 실패 - 이전 대화 블록 없이 진행: %s", e)
        finally:
            self.ctx_ready.set()

    def synth(self, text: str, prev: str) -> bytes:
        body = {"text": text}
        if prev:
            body["previous_text"] = prev
        if XZ_VOICE_ID:
            body["voice_id"] = XZ_VOICE_ID
        if self.model_tags:
            body["model_tags"] = True
        r = self._client().post("/api/tts", json=body, headers=self.auth_headers())
        if r.status_code != 200:
            raise RuntimeError(f"/api/tts {r.status_code}: {r.get_data(as_text=True)[:120]}")
        b = r.get_data()
        return b[:len(b) - len(b) % 2]

    def song_pcm(self, play: dict, cancel: threading.Event):
        """곡 파일(mp3 등)을 ffmpeg로 24kHz mono PCM으로 풀어 흘려준다. 받는 대로 바로 재생이 시작된다."""
        url = str(play.get("url") or "")
        if not url:
            return
        if url.startswith("/"):
            resp = self._client().get(url, headers=self.auth_headers(), buffered=False)
            if resp.status_code != 200:
                raise RuntimeError(f"곡 파일 {resp.status_code}")
            src = resp.iter_encoded()
        else:
            import requests
            rr = requests.get(url, stream=True, timeout=(5, 30))
            rr.raise_for_status()
            src = rr.iter_content(65536)
        p = subprocess.Popen(["ffmpeg", "-v", "error", "-i", "pipe:0", "-t", str(SONG_MAX_S), "-f", "s16le",
                              "-ar", str(OUT_RATE), "-ac", "1", "pipe:1"],
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)

        def _feed():
            try:
                for ch in src:
                    if cancel.is_set():
                        break
                    p.stdin.write(ch)
            except Exception:
                pass
            finally:
                try:
                    p.stdin.close()
                except Exception:
                    pass
        threading.Thread(target=_feed, daemon=True).start()
        try:
            while not cancel.is_set():
                chunk = p.stdout.read(OUT_FRAME_SAMPLES * 2 * 10)
                if not chunk:
                    break
                yield chunk
        finally:
            try:
                p.kill()
            except Exception:
                pass

    # --- 수신 ---
    def on_text(self, obj: dict):
        t = obj.get("type")
        if t == "hello":
            ap = obj.get("audio_params") or {}
            self.in_rate = int(ap.get("sample_rate") or 16000)
            self.in_frame_ms = int(ap.get("frame_duration") or 60)
            if self.version == 1 and obj.get("version") in (2, 3):
                self.version = obj["version"]
            self.dec = opuslib.Decoder(self.in_rate, 1)
            self.send_json({"type": "hello", "transport": "websocket", "session_id": self.session_id,
                            "audio_params": {"format": "opus", "sample_rate": OUT_RATE, "channels": 1,
                                             "frame_duration": OUT_FRAME_MS}})
            threading.Thread(target=self._prepare, daemon=True).start()
            log.info("[xiaozhi] 기기 연결 device=%s ver=%s 입력=%sHz/%sms", self.device_id, self.version, self.in_rate, self.in_frame_ms)
        elif t == "listen":
            st = obj.get("state")
            if st == "start":
                self.abort()
                self.mode = str(obj.get("mode") or "auto")
                self.ep = Endpointer(manual=(self.mode == "manual"))
            elif st == "stop":
                if self.ep is not None and self.ep.manual:
                    self._on_utterance(self.ep.finish())
                    self.ep = None
            elif st == "detect":
                log.info("[xiaozhi] 웨이크워드 감지: %r", obj.get("text"))
        elif t == "abort":
            self.abort()
            self.send_json({"type": "tts", "state": "stop"})
        # mcp / goodbye 등은 지금은 쓰지 않는다

    def on_audio(self, data: bytes):
        if self.dec is None or self.ep is None or self.busy:
            return
        pkt = self._unpack(data)
        if not pkt:
            return
        try:
            pcm = self.dec.decode(pkt, self.in_rate * 120 // 1000)
        except Exception:
            return
        if self.in_rate != 16000:            # 기기 입력은 16kHz가 기본이다. 다르면 거칠게 맞춘다 (정수배만)
            k = self.in_rate // 16000
            if k > 1:
                pcm = memoryview(pcm).cast("h")[::k].tobytes()
        out = self.ep.feed(pcm)
        if out is not None:
            self.ep = None if self.ep.manual else Endpointer()
            self._on_utterance(out)

    def abort(self):
        """말하던 것(대답/노래)을 멈춘다."""
        if self.busy:
            self.cancel.set()
            self.busy = False      # 이전 턴 스레드가 정리되길 기다리지 않고 바로 다음 말을 받는다

    def _on_utterance(self, pcm: bytes):
        if not pcm or self.busy:
            return
        self.busy = True
        self.cancel = threading.Event()
        threading.Thread(target=self._turn, args=(pcm, self.cancel), daemon=True, name="xz-turn").start()

    # --- 한 턴 ---
    def _turn(self, pcm: bytes, cancel: threading.Event):
        speaker = None
        t_start = time.monotonic()
        try:
            self.ctx_ready.wait(timeout=5)
            tid = "x" + uuid.uuid4().hex[:15]
            payload = {"audio": base64.b64encode(_wav16k(pcm)).decode(), "mime": "audio/wav",
                       "turns": self.turns[-30:], "ctx": self.ctx, "sig": self.sig, "tid": tid}
            if XZ_LAT and XZ_LNG:
                payload["lat"], payload["lng"] = XZ_LAT, XZ_LNG
            speaker = Speaker(self, cancel)
            real, user_text, song, stopped, got_error = [], "", None, False, False
            resp = self._client().post("/api/pipe/chat", json=payload, headers=self.auth_headers(), buffered=False)
            if resp.status_code != 200:
                raise RuntimeError(f"/api/pipe/chat {resp.status_code}")
            buf = b""
            for chunk in resp.iter_encoded():
                if cancel.is_set():
                    break
                buf += chunk
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    if not line.strip():
                        continue
                    try:
                        ev = json.loads(line)
                    except ValueError:
                        continue
                    kind = ev.get("type")
                    if kind == "delta":
                        txt = ev.get("text") or ""
                        if ev.get("filler"):
                            speaker.filler(txt)
                        else:
                            real.append(txt)
                            speaker.feed(txt)
                    elif kind == "user":
                        user_text = ev.get("text") or ""
                        self.send_json({"type": "stt", "text": user_text})
                    elif kind == "song":
                        song = ev.get("play") or None
                    elif kind == "stop":
                        stopped = True
                    elif kind == "error":
                        got_error = True
                        log.warning("[xiaozhi] pipe 오류: %s", ev.get("message"))
            try:
                resp.close()
            except Exception:
                pass
            if got_error and not real and self.error_text():
                speaker.filler(self.error_text())
            speaker.flush()
            speaker.close()
            if song and not stopped and not cancel.is_set():      # 노래는 안내 음성이 다 끝난 뒤에 재생
                speaker.play_song(song)
            speaker.end()
            reply = "".join(real).strip()
            if reply and not cancel.is_set():                     # 필러/사과 한마디는 기록하지 않는다 (웹 화면과 같은 규칙)
                self.turns += [{"role": "user", "text": user_text or "(음성 메시지)"}, {"role": "model", "text": reply}]
                self.turns = self.turns[-MAX_TURNS_KEPT:]
            log.info("[xiaozhi] 턴 완료 %.1fs 취소=%s 입력=%r", time.monotonic() - t_start, cancel.is_set(), user_text[:30])
        except Exception as e:
            log.exception("[xiaozhi] 턴 처리 실패")
            try:
                if speaker is not None:
                    speaker.flush()
                    if self.error_text():
                        speaker.filler(self.error_text())
                    speaker.close()
                    speaker.end()
            except Exception:
                pass
        finally:
            if self.cancel is cancel:        # 중간에 abort되고 새 턴이 시작됐다면 그 턴의 상태를 건드리지 않는다
                self.busy = False
                if not self.closed and self.mode != "manual":
                    self.ep = Endpointer()      # 다음 말을 새로 듣는다 (기기가 listen start를 다시 보내면 거기서 한 번 더 초기화된다)


# ===================== Flask에 달기 =====================
def install(app, auth_headers=None, error_text=None):
    """token_server.py의 app에 /xiaozhi/ota/, /xiaozhi/v1/(WebSocket), /xiaozhi/healthz 를 등록한다.
    auth_headers: () -> dict  (GOOGLE_CLIENT_ID 로그인을 쓰는 서버일 때 내부 호출에 붙일 Authorization 헤더)
    error_text:   () -> str   (오류 때 읽어줄 미리 저장된 안내 문구, 없으면 읽지 않음)"""
    if not XZ_KEY:
        log.info("[xiaozhi] XIAOZHI_KEY가 없어서 스택찬 브리지는 꺼져 있습니다")
        return False
    if Sock is None or opuslib is None:
        log.error("[xiaozhi] flask-sock 또는 opuslib(libopus)를 불러오지 못해 브리지를 켜지 못했습니다")

        @app.get("/xiaozhi/healthz")
        def xz_health_broken():      # Railway에서 무엇이 빠졌는지 주소 하나로 확인할 수 있게 한다
            return jsonify({"enabled": False, "flask_sock": Sock is not None, "opus": opuslib is not None,
                            "ffmpeg": bool(_which("ffmpeg")),
                            "hint": "requirements.txt에 flask-sock, opuslib 추가 + 시스템 패키지 libopus0, ffmpeg 필요"}), 503
        return False
    auth_headers = auth_headers or (lambda: {})
    error_text = error_text or (lambda: "")
    app.config.setdefault("SOCK_SERVER_OPTIONS", {"ping_interval": 25})      # 프록시(Railway)가 조용한 연결을 끊지 않게 주기적으로 ping
    sock = Sock(app)

    def _ok_device(device_id: str) -> bool:
        return not XZ_DEVICE_IDS or (device_id or "").lower() in XZ_DEVICE_IDS

    @app.route("/xiaozhi/ota/", methods=["GET", "POST"])
    def xz_ota():
        key = request.args.get("key", "")
        if not hmac.compare_digest(key.encode(), XZ_KEY.encode()):
            return jsonify({"error": "unauthorized"}), 401
        device_id = request.headers.get("Device-Id", "") or request.headers.get("device-id", "")
        if not _ok_device(device_id):
            log.warning("[xiaozhi] 허용 목록에 없는 기기의 OTA 요청 거부: %r (XIAOZHI_DEVICE_IDS에 추가하면 됩니다)", device_id)
            return jsonify({"error": "unauthorized"}), 401
        body = request.get_json(silent=True) or {}
        cur_ver = str((body.get("application") or {}).get("version") or "1.0.0")
        if XZ_WS_URL:
            ws_url = XZ_WS_URL
        else:
            scheme = "wss" if request.headers.get("X-Forwarded-Proto", request.scheme) == "https" else "ws"
            ws_url = f"{scheme}://{request.host}/xiaozhi/v1/"
        log.info("[xiaozhi] OTA 요청 device=%s ver=%s -> %s", device_id, cur_ver, ws_url)
        return jsonify({
            "server_time": {"timestamp": int(time.time() * 1000), "timezone_offset": 540},
            "firmware": {"version": cur_ver, "url": ""},         # 지금 버전을 그대로 돌려줘서 자동 업데이트를 하지 않는다
            "websocket": {"url": ws_url, "token": _device_token(device_id), "version": 1},
        })

    @app.get("/xiaozhi/healthz")
    def xz_health():
        return jsonify({"enabled": True, "opus": opuslib is not None,
                        "vad": "webrtc" if (VAD_KIND == "webrtc" and webrtcvad) else "energy",
                        "ffmpeg": bool(_which("ffmpeg"))})

    @sock.route("/xiaozhi/v1/")
    def xz_ws(ws):
        device_id = request.headers.get("Device-Id", "")
        token = request.headers.get("Authorization", "").removeprefix("Bearer ").strip()
        if not (_ok_device(device_id) and hmac.compare_digest(token.encode(), _device_token(device_id).encode())):
            log.warning("[xiaozhi] WebSocket 인증 실패 device=%r", device_id)
            ws.close(reason=1008, message="unauthorized")
            return
        try:
            version = int(request.headers.get("Protocol-Version", "1"))
        except ValueError:
            version = 1
        sess = Session(ws, app, device_id, version, auth_headers, error_text)
        try:
            while True:
                msg = ws.receive(timeout=60)
                if msg is None:
                    continue
                if isinstance(msg, (bytes, bytearray)):
                    sess.on_audio(bytes(msg))
                else:
                    try:
                        sess.on_text(json.loads(msg))
                    except ValueError:
                        pass
        except Exception as e:      # ConnectionClosed 포함
            log.info("[xiaozhi] 연결 종료 device=%s (%s)", device_id, type(e).__name__)
        finally:
            sess.closed = True
            sess.cancel.set()

    log.info("[xiaozhi] 스택찬 브리지 켜짐 - OTA: /xiaozhi/ota/?key=...  WS: /xiaozhi/v1/  (VAD=%s)",
             "webrtc" if (VAD_KIND == "webrtc" and webrtcvad) else "energy")
    return True


def _which(name):
    from shutil import which
    return which(name)
