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
import functools
import json
import logging
import math
import os
import queue
import random
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


# ----- 설정 (환경변수는 키/허용 기기/주소/위치/목소리 ID만 읽고, 나머지는 모두 고정값) -----
XZ_KEY = _env("XIAOZHI_KEY")                              # 필수. 비어 있으면 브리지 전체가 꺼진다
XZ_DEVICE_IDS = {d.strip().lower() for d in _env("XIAOZHI_DEVICE_IDS").split(",") if d.strip()}   # 기기 MAC 허용 목록 (선택)
XZ_WS_URL = _env("XIAOZHI_WS_URL")                        # 비우면 요청 주소로 wss://<host>/xiaozhi/v1/ 를 만든다
XZ_LAT, XZ_LNG = _env("XIAOZHI_LAT"), _env("XIAOZHI_LNG")  # 스택찬엔 GPS가 없어서 고정 위치(집)를 쓴다 (선택)
XZ_VOICE_ID = _env("XIAOZHI_VOICE_ID")                    # 비우면 서버 기본 목소리
MAX_UTT_S = 30
END_SILENCE_MS = 900                                      # 이만큼 조용하면 말이 끝난 것 (고정값)
OUT_RATE = 24000                                          # /api/tts 출력 = 24kHz 16bit mono PCM
OUT_FRAME_MS = 60
OUT_FRAME_SAMPLES = OUT_RATE * OUT_FRAME_MS // 1000
PREBUFFER_FRAMES = 5                                      # 기기 큐가 약 2.4초라서 너무 앞서 보내면 버려진다
SONG_MAX_S = 600
IDLE = True                                               # 대기 중에 가끔 고개/표정을 움직이고, 오래 두면 잠든다
IDLE_MIN_S = 12                                           # 대기 중 동작 간격 (초, 최소~최대 사이 무작위)
IDLE_MAX_S = 35
SLEEP_AFTER_S = 180                                       # 이만큼 아무 말이 없으면 잠든 표정으로
SLEEP_EMOTION = "sleepy"
SLEEP_TILT = -18                                          # 잘 때 고개를 떨구는 각도
IDLE_EMOTIONS = ["neutral", "happy", "thinking", "relaxed", "winking"]
TURN_MAX_S = 120                                          # 대답 생성/재생에서 이만큼 아무 진전이 없으면 멈춘 것으로 보고 풀어 준다 (먹통 방지)
MOTION = True                                             # 고개 움직임 (self.robot.set_head_angles / center_head 사용)
# 호출어: 쉬는 동안엔 이 말로 시작해야 대답한다. 한 번 부르면 WAKE_WINDOW_S초 동안은 호출어 없이 이어서 대화한다.
MCP_ON = True
WAKE_ON = True
WAKE_WORDS = ["쎄리야", "쌔리야", "세리야", "새리야", "쎄리", "쌔리"]
WAKE_WINDOW_S = 60
MAX_TURNS_KEPT = 40
MIN_FIRST, MIN_NEXT = 8, 70                               # taeyeon-pipe.html과 같은 문장 자르기 기준

def _make_beep() -> bytes:
    """대화모드 진입 알림: 짧은 두 음(880Hz -> 1320Hz), 24kHz 16bit mono PCM. 파일 없이 코드로 만든다."""
    out = bytearray()
    for freq, ms in ((880, 70), (1320, 90)):
        n = OUT_RATE * ms // 1000
        fade = max(1, OUT_RATE * 8 // 1000)          # 8ms 페이드로 '딱' 소리 방지
        for i in range(n):
            env = min(1.0, i / fade, (n - i) / fade)
            out += struct.pack("<h", int(9000 * env * math.sin(2 * math.pi * freq * i / OUT_RATE)))
    return bytes(out)


BEEP_PCM = _make_beep()

_pool = ThreadPoolExecutor(max_workers=6, thread_name_prefix="xz-tts")


# ===================== 보조 함수 =====================
def _device_token(device_id: str) -> str:
    return hmac.new(XZ_KEY.encode(), (device_id or "").lower().encode(), hashlib.sha256).hexdigest()[:32]


def _wav16k(pcm: bytes) -> bytes:
    n = len(pcm)
    return (b"RIFF" + struct.pack("<I", 36 + n) + b"WAVEfmt " + struct.pack("<IHHIIHH", 16, 1, 1, 16000, 32000, 2, 16)
            + b"data" + struct.pack("<I", n) + pcm)


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
        self.vad = webrtcvad.Vad() if webrtcvad else None     # 라이브러리 기본값 그대로 (감도 조절 없음)

    def _voiced(self, fr: bytes) -> bool:
        if not self.vad:
            return False
        try:
            return self.vad.is_speech(fr, 16000)
        except Exception:
            return False

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
                if self.silence_ms >= END_SILENCE_MS or len(self.utt) >= MAX_UTT_S * 32000:
                    return self.finish()
        return None

    def finish(self):
        pcm = bytes(self.utt)
        ok = len(pcm) >= 0.4 * 32000
        if not self.manual:
            log.info("[xiaozhi] 소리 감지 %s: 말소리 %dms / 전체 %dms",
                     "→ 대화로 보냄" if ok else "→ 소음으로 버림", self.voiced_ms, len(pcm) // 32)
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
            self.s.motion_speak(emo or self.last_emo)
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

    def beep(self):
        """대화모드로 전환됐다는 짧은 부저음."""
        self._begin()
        self.emit_pcm(BEEP_PCM)

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
            self.s.center_head()


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
        self.last_active = time.monotonic()     # 마지막으로 대화/말소리가 있던 때 (대기 동작과 잠들기 기준)
        self.asleep = False
        self._web = None                        # 웹 화면에서 보낸 글을 읽는 중인 대답 (say_chunk)
        self._say_lock = threading.Lock()
        self.turn_progress = time.monotonic()   # 마지막으로 대답이 진전된 때 (소리 전송/서버 응답 조각)
        self.has_robot = False
        self._mute_until = 0.0                  # 대기 동작 중 모터 소리를 말로 오인하지 않게 잠깐 듣지 않는다

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
        self.turn_progress = time.monotonic()
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
            if not getattr(self, "_idle_started", False):
                self._idle_started = True
                threading.Thread(target=self._idle_loop, daemon=True, name="xz-idle").start()
            # --- 진단용: 기기가 MCP(움직임 등 도구)를 지원하면 도구 목록을 요청해서 로그로 찍는다 ---
            feats = obj.get("features") or {}
            log.info("[xiaozhi] 기기 features=%s", json.dumps(feats, ensure_ascii=False)[:300])
            if feats.get("mcp") and MCP_ON:
                self._mcp_id = 0
                self._mcp_call("initialize", {"protocolVersion": "2024-11-05", "capabilities": {},
                                              "clientInfo": {"name": "serri-bridge", "version": "0.1"}})
                self._mcp_call("tools/list", {"cursor": ""})
        elif t == "listen":
            st = obj.get("state")
            log.info("[xiaozhi] 기기 listen 신호: %s (mode=%s)", st, obj.get("mode"))
            if st == "start":
                self.abort()
                self.touch()
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
        elif t == "mcp":
            # 진단용: 기기가 보낸 MCP 응답(도구 목록 등)을 그대로 로그에 남긴다
            pl = obj.get("payload") or {}
            if isinstance(pl, dict) and "error" in pl:
                log.warning("[xiaozhi] MCP 오류 응답: %s", json.dumps(pl, ensure_ascii=False)[:400])
            elif isinstance(pl, dict) and "method" in pl:
                # 기기가 먼저 보낸 MCP 요청/알림 (예: 터치/쓰다듬기 이벤트가 여기로 올 수 있다)
                log.info("[xiaozhi] 기기가 보낸 MCP 메시지: %s", json.dumps(pl, ensure_ascii=False)[:600])
            elif isinstance(pl, dict) and pl.get("id") in getattr(self, "_tools_ids", {2}):
                res = pl.get("result") or {}
                try:
                    tl = res.get("tools") or []
                    self._tool_names = getattr(self, "_tool_names", []) + [t_.get("name") for t_ in tl]
                    if "self.robot.set_head_angles" in self._tool_names and not self.has_robot:
                        self.has_robot = True
                        log.info("[xiaozhi] 로봇 고개 도구 확인됨 - 움직임 켜짐")
                    nc = res.get("nextCursor")
                    if nc:                      # 도구가 많으면 여러 쪽으로 나눠 온다
                        self._mcp_call("tools/list", {"cursor": nc}, quiet=True)
                        self._tools_ids = getattr(self, "_tools_ids", {2}) | {self._mcp_id}
                    else:
                        log.info("[xiaozhi] 기기 MCP 도구 %d개: %s", len(self._tool_names), ", ".join(map(str, self._tool_names)))
                except Exception:
                    log.exception("[xiaozhi] 도구 목록 처리 실패")
            else:
                log.debug("[xiaozhi] MCP 수신: %s", json.dumps(pl, ensure_ascii=False)[:300])
        elif t not in ("hello", "listen", "abort", "mcp", "goodbye"):
            # 쓰다듬기 같은 기기 이벤트가 어떤 이름으로 오는지 알아내기 위한 진단 로그
            log.info("[xiaozhi] 처리하지 않은 기기 메시지: %s", json.dumps(obj, ensure_ascii=False)[:600])
        # goodbye 등은 지금은 쓰지 않는다

    def _mcp_call(self, method, params, quiet=False):
        self._mcp_id = getattr(self, "_mcp_id", 0) + 1
        self.send_json({"session_id": self.session_id, "type": "mcp",
                        "payload": {"jsonrpc": "2.0", "method": method, "params": params, "id": self._mcp_id}})
        if not quiet:
            log.info("[xiaozhi] MCP 요청 전송: %s", method)

    # --- 고개 움직임 (기기가 알려 준 MCP 도구: self.robot.set_head_angles / center_head) ---
    def move_head(self, pan=0, tilt=0, dur=500, min_gap=0.7):
        if not MOTION or self.closed or not getattr(self, "has_robot", False):
            return
        now = time.monotonic()
        if now - getattr(self, "_last_move", 0.0) < min_gap:
            return
        self._last_move = now
        pan = max(-70, min(70, int(pan)))
        tilt = max(-35, min(35, int(tilt)))
        dur = max(120, min(5000, int(dur)))
        self._mcp_call("tools/call", {"name": "self.robot.set_head_angles",
                                      "arguments": {"pan": pan, "tilt": tilt, "duration_ms": dur}}, quiet=True)

    def center_head(self):
        if not MOTION or self.closed or not getattr(self, "has_robot", False):
            return
        self._last_move = time.monotonic()
        if "self.robot.center_head" in getattr(self, "_tool_names", []):
            self._mcp_call("tools/call", {"name": "self.robot.center_head", "arguments": {}}, quiet=True)
        else:
            # 공장 펌웨어에는 center_head가 없다 -> 정면(0, 0)으로 set_head_angles
            self._mcp_call("tools/call", {"name": "self.robot.set_head_angles",
                                          "arguments": {"pan": 0, "tilt": 0, "duration_ms": 600}}, quiet=True)

    # --- 대기 모드: 가끔 고개/표정, 오래 두면 잠든다 ---
    def _awake(self) -> bool:
        """호출어 없이 바로 대답해도 되는 상태인가 (호출어를 끄면 항상 True, 아니면 부른 뒤 WAKE_WINDOW_S초 동안만 True)."""
        if not (WAKE_ON and WAKE_WORDS):
            return True
        return time.monotonic() < getattr(self, "awake_until", 0.0)

    def touch(self):
        """대화/말소리가 있었다: 깨어나고 대기 시간을 다시 센다."""
        self.last_active = time.monotonic()
        if self.asleep:
            self.asleep = False
            self.send_json({"type": "llm", "emotion": "neutral", "text": ""})
            self.move_head(0, 6, 600, min_gap=0)

    def fall_asleep(self):
        """잠든 모습: 고개를 천천히 떨구고 잠든 표정으로. (말소리가 들리면 touch()가 깨운다)"""
        self.asleep = True
        self._mute_until = time.monotonic() + 3.5
        self.send_json({"type": "llm", "emotion": SLEEP_EMOTION, "text": ""})
        if SLEEP_TILT:
            self.move_head(0, SLEEP_TILT, 2500, min_gap=0)
        else:
            self.center_head()
        log.info("[xiaozhi] 한참 조용해서 잠든 모습으로 (표정=%s, 고개 %d도)", SLEEP_EMOTION, SLEEP_TILT)

    def _idle_loop(self):
        nxt = time.monotonic() + random.uniform(IDLE_MIN_S, IDLE_MAX_S)
        while not self.closed:
            time.sleep(1.0)
            now = time.monotonic()
            if self.busy and now - self.turn_progress > TURN_MAX_S:
                # 대답이 멈춰 버린 경우(예: 서버가 응답을 안 줌): 계속 '처리 중'으로 두면 이후 모든 말을 무시하게 된다
                log.warning("[xiaozhi] 대답이 %ds 넘게 진전이 없어 이번 턴을 취소하고 다시 듣습니다", TURN_MAX_S)
                self.cancel.set()
                self.busy = False
                if self.mode != "manual":
                    self.ep = Endpointer()
                self.send_json({"type": "tts", "state": "stop"})
                self.last_active = now
                continue
            if self.busy or (self.ep is not None and self.ep.started):
                if self._awake():
                    self.touch()              # 말소리가 들리면 잠에서 깬다 (호출어를 기다리는 중이면 깨지 않는다)
                nxt = now + random.uniform(IDLE_MIN_S, IDLE_MAX_S)
                continue
            if not IDLE or self.asleep:
                continue
            if SLEEP_AFTER_S > 0 and now - self.last_active >= SLEEP_AFTER_S:
                self.fall_asleep()
                continue
            if now >= nxt:
                nxt = now + random.uniform(IDLE_MIN_S, IDLE_MAX_S)
                dur = random.randint(900, 1600)
                self._mute_until = now + dur / 1000.0 + 0.6
                self.move_head(random.randint(-30, 30), random.randint(-4, 12), dur, min_gap=0)
                if IDLE_EMOTIONS and random.random() < 0.6:
                    self.send_json({"type": "llm", "emotion": random.choice(IDLE_EMOTIONS), "text": ""})

    def motion_think(self):
        """사용자의 말이 끝나고 대답을 기다리는 동안: 살짝 고개를 갸웃한다."""
        self.move_head(random.choice((-12, 12)), 8, 700, min_gap=0)

    def motion_speak(self, emo=""):
        """문장 하나를 말하기 시작할 때: 표정에 맞는 작은 동작."""
        if emo == "laughing":
            self.move_head(random.choice((-15, 15)), 14, 300)
        elif emo == "sad":
            self.move_head(0, -18, 1200)
        elif emo == "angry":
            self.move_head(0, -6, 300)
        elif emo == "surprised":
            self.move_head(0, 16, 200)
        elif emo in ("happy", "loving"):
            self.move_head(random.randint(-12, 12), 10, 500)
        else:
            self.move_head(random.randint(-10, 10), random.randint(0, 8), random.randint(500, 900))

    def on_audio(self, data: bytes):
        if self.dec is None or self.ep is None or self.busy:
            return
        if time.monotonic() < self._mute_until:     # 대기 동작 중 모터 소리
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

    # --- 웹 화면에서 글로 물은 대답을 이 기기 스피커로 읽는다 ---
    def say_chunk(self, tid, text, final):
        """웹 화면이 대답 글자를 조각조각 보내 준다. 같은 tid의 조각은 하나의 '말하기 턴'으로 이어서 읽는다.
        반환: True(받음) / False(기기가 지금 다른 대답을 하는 중이라 받지 못함)"""
        with self._say_lock:
            w = self._web
            if w is None or w["tid"] != tid:
                if self.busy:
                    return False
                self.busy = True
                cancel = threading.Event()
                self.cancel = cancel
                self.turn_progress = time.monotonic()
                self.touch()
                w = self._web = {"tid": tid, "cancel": cancel, "sp": Speaker(self, cancel), "t0": time.monotonic(), "n": 0}
            sp = w["sp"]
            if final:
                self._web = None
        if text:
            w["n"] += len(text)
            self.turn_progress = time.monotonic()
            sp.feed(text)
        if final:
            threading.Thread(target=self._say_finish, args=(w,), daemon=True, name="xz-say").start()
        return True

    def _say_finish(self, w):
        cancel, sp = w["cancel"], w["sp"]
        try:
            sp.flush()
            sp.close()
            sp.end()
            log.info("[xiaozhi] 웹에서 보낸 대답 읽기 완료 %.1fs %d자 취소=%s", time.monotonic() - w["t0"], w["n"], cancel.is_set())
        except Exception:
            log.exception("[xiaozhi] 웹 대답 읽기 실패")
        finally:
            self.last_active = time.monotonic()
            if self.cancel is cancel:
                self.busy = False
                if not self.closed and self.mode != "manual":
                    self.ep = Endpointer()

    def abort(self):
        """말하던 것(대답/노래)을 멈춘다."""
        if self.busy:
            self.cancel.set()
            self.busy = False      # 이전 턴 스레드가 정리되길 기다리지 않고 바로 다음 말을 받는다

    def _on_utterance(self, pcm: bytes):
        if not pcm or self.busy:
            return
        self.busy = True
        self.turn_progress = time.monotonic()
        self.cancel = threading.Event()
        gated = not self._awake()          # 호출어를 먼저 확인해야 하는 소리인가
        if not gated:
            self.touch()
            self.motion_think()
        threading.Thread(target=self._turn, args=(pcm, self.cancel, gated), daemon=True, name="xz-turn").start()

    # --- 한 턴 ---
    def _turn(self, pcm: bytes, cancel: threading.Event, gated: bool = False):
        speaker = None
        ignored = False
        t_start = time.monotonic()
        try:
            self.ctx_ready.wait(timeout=5)
            tid = "x" + uuid.uuid4().hex[:15]
            payload = {"audio": base64.b64encode(_wav16k(pcm)).decode(), "mime": "audio/wav",
                       "turns": self.turns[-30:], "ctx": self.ctx, "sig": self.sig, "tid": tid}
            if XZ_LAT and XZ_LNG:
                payload["lat"], payload["lng"] = XZ_LAT, XZ_LNG
            if gated:
                payload["wake"] = WAKE_WORDS
            speaker = Speaker(self, cancel)
            real, user_text, song, stopped, got_error = [], "", None, False, False
            resp = self._client().post("/api/pipe/chat", json=payload, headers=self.auth_headers(), buffered=False)
            if resp.status_code != 200:
                raise RuntimeError(f"/api/pipe/chat {resp.status_code}")
            buf = b""
            for chunk in resp.iter_encoded():
                if cancel.is_set():
                    break
                self.turn_progress = time.monotonic()
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
                    elif kind == "ignored":
                        ignored = True           # 호출어 없는 소리: 아무것도 하지 않는다
                    elif kind == "user":
                        user_text = ev.get("text") or ""
                        self.send_json({"type": "stt", "text": user_text})
                        if gated and not ignored:    # 호출어로 불렸다: 깨어나서 고개를 갸웃하고, 이제부터 한동안 호출어 없이 듣는다
                            self.awake_until = time.monotonic() + WAKE_WINDOW_S
                            self.touch()
                            self.motion_think()
                            speaker.beep()           # 대화모드 전환 부저음
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
            if ignored:
                log.info("[xiaozhi] 호출어 없는 소리라 무시했어요")
                return
            reply = "".join(real).strip()
            if reply and not cancel.is_set():                     # 필러/사과 한마디는 기록하지 않는다 (웹 화면과 같은 규칙)
                self.turns += [{"role": "user", "text": user_text or "(음성 메시지)"}, {"role": "model", "text": reply}]
                self.turns = self.turns[-MAX_TURNS_KEPT:]
            self.last_active = time.monotonic()
            if not gated or user_text:
                self.awake_until = time.monotonic() + WAKE_WINDOW_S      # 대답이 끝난 시점부터 다시 센다
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
def install(app, auth_headers=None, error_text=None, require_auth=None):
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

    def _key_auth(fn):      # 웹 로그인 데코레이터를 못 받았을 때: XIAOZHI_KEY를 X-Xiaozhi-Key 헤더나 ?key= 로 받는다
        @functools.wraps(fn)
        def w(*a, **k):
            given = request.headers.get("X-Xiaozhi-Key") or request.args.get("key", "")
            if not hmac.compare_digest(given.encode(), XZ_KEY.encode()):
                return jsonify({"error": "unauthorized"}), 401
            return fn(*a, **k)
        return w
    _web_auth = require_auth or _key_auth
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
                        "vad": bool(webrtcvad),
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
        with _SESSIONS_LOCK:
            _SESSIONS.append(sess)
        try:
            while True:
                msg = ws.receive(timeout=60)
                if msg is None:
                    continue
                if isinstance(msg, (bytes, bytearray)):
                    sess.n_audio = getattr(sess, "n_audio", 0) + 1
                    sess.on_audio(bytes(msg))
                else:
                    try:
                        _obj = json.loads(msg)
                        _k = str(_obj.get("type")) + (":" + str(_obj.get("state")) if _obj.get("state") else "")
                        sess.seen = getattr(sess, "seen", {})
                        sess.seen[_k] = sess.seen.get(_k, 0) + 1
                        sess.on_text(_obj)
                    except ValueError:
                        pass
        except Exception as e:      # ConnectionClosed 포함
            log.info("[xiaozhi] 연결 종료 device=%s (%s) | 연결 %.1f초, 받은 소리 %d프레임, 받은 메시지 %s", device_id, type(e).__name__,
                     time.monotonic() - sess.t0, getattr(sess, "n_audio", 0), getattr(sess, "seen", {}))
        finally:
            sess.closed = True
            sess.cancel.set()
            with _SESSIONS_LOCK:
                if sess in _SESSIONS:
                    _SESSIONS.remove(sess)

    def _live_session():
        with _SESSIONS_LOCK:
            live = [x for x in _SESSIONS if not x.closed]
        return live[-1] if live else None

    @app.get("/xiaozhi/status")
    @_web_auth
    def xz_status():
        """웹 화면이 '스택찬이 지금 연결돼 있나'를 물어보는 주소."""
        sess = _live_session()
        if not sess:
            return jsonify({"connected": False})
        return jsonify({"connected": True, "busy": bool(sess.busy), "asleep": bool(sess.asleep)})

    @app.post("/xiaozhi/say")
    @_web_auth
    def xz_say():
        """웹 화면에서 글로 물은 대답을 스택찬 스피커로 읽게 한다.
        body: {tid, text, final}  - 같은 tid의 조각을 이어서 읽고, final=true가 오면 마무리한다."""
        sess = _live_session()
        if not sess:
            return jsonify({"error": "no_device"}), 404
        d = request.get_json(force=True, silent=True) or {}
        tid = str(d.get("tid") or "")[:64]
        text = str(d.get("text") or "")[:4000]
        if not tid:
            return jsonify({"error": "tid가 필요해요"}), 400
        if not sess.say_chunk(tid, text, bool(d.get("final"))):
            return jsonify({"error": "busy"}), 409
        return jsonify({"ok": True})

    @app.get("/xiaozhi/test")
    def xz_test():
        """브라우저에서 기기를 직접 시험해 보는 주소 (키 필요).
        /xiaozhi/test?key=KEY&emotion=sleepy      표정 바꾸기 (이름 확인용)
        /xiaozhi/test?key=KEY&pan=20&tilt=-10     고개 움직이기 (pan -70~70, tilt -35~35, dur=ms)
        /xiaozhi/test?key=KEY&center=1            고개 정면
        /xiaozhi/test?key=KEY&sleep=1 / wake=1    잠들기 / 깨우기"""
        if not hmac.compare_digest(request.args.get("key", "").encode(), XZ_KEY.encode()):
            return jsonify({"error": "unauthorized"}), 401
        with _SESSIONS_LOCK:
            live = [x for x in _SESSIONS if not x.closed]
        if not live:
            return jsonify({"error": "연결된 기기가 없어요 (스택찬이 서버에 접속해 있어야 합니다)"}), 404
        sess = live[-1]
        done = []
        a = request.args
        if a.get("emotion"):
            sess.send_json({"type": "llm", "emotion": a["emotion"], "text": ""})
            done.append("emotion=" + a["emotion"])
        if a.get("pan") is not None or a.get("tilt") is not None:
            try:
                pan, tilt, dur = int(a.get("pan", 0)), int(a.get("tilt", 0)), int(a.get("dur", 800))
            except ValueError:
                return jsonify({"error": "pan/tilt/dur는 숫자여야 해요"}), 400
            sess.has_robot = True
            sess.move_head(pan, tilt, dur, min_gap=0)
            done.append(f"head pan={pan} tilt={tilt} dur={dur}")
        if a.get("center"):
            sess.has_robot = True
            sess.center_head()
            done.append("center")
        if a.get("sleep"):
            sess.has_robot = True
            sess.fall_asleep()
            done.append("sleep")
        if a.get("wake"):
            sess.asleep = True
            sess.touch()
            done.append("wake")
        return jsonify({"sent": done or ["(할 일이 없어요: emotion, pan/tilt, center, sleep, wake 중 하나를 붙이세요)"], "devices": len(live)})

    log.info("[xiaozhi] 스택찬 브리지 켜짐 - OTA: /xiaozhi/ota/?key=...  WS: /xiaozhi/v1/  (VAD=%s)",
             "webrtc" if webrtcvad else "없음")
    if not webrtcvad:
        log.error("[xiaozhi] webrtcvad 모듈이 없어 말 끝 감지가 동작하지 않습니다 (pip install webrtcvad)")
    return True


_SESSIONS = []           # 지금 연결된 기기들 (테스트 주소가 쓴다)
_SESSIONS_LOCK = threading.Lock()


def _which(name):
    from shutil import which
    return which(name)
