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

입력/출력 방식 (기본: 입력 = Gemini Live, 출력 = pipe):
  기기 마이크 -> Gemini Live (듣기/말 끝 감지/받아쓰기/생각/함수 호출) -> 대답 '글자'(전사)만 받아서
  -> 문장 단위로 /api/tts (타입캐스트) -> 24kHz PCM -> Opus -> 기기.  Live가 만든 목소리는 버린다.
  pipe 방식에서는 호출어("쎄리야")를 불러야 대화모드가 시작된다. 호출어 없는 말은 Live가 들어도 대답/도구/표정을 모두 무시하고,
  대화모드는 CONVO_IDLE_S(60초) 동안 조용하면 끝난다. XIAOZHI_WAKE=0 이면 호출어 없이 늘 대화한다.
  XIAOZHI_MODE=pipe(기본) = 위 방식 / XIAOZHI_MODE=live = 입력, 출력 모두 Live(Live 목소리 그대로).
  (Live 연결이 처음부터 계속 실패할 때만 예전 pipe 입력 방식으로 되돌아간다)

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
VAD_MODE = 1                                              # webrtcvad 강도 0~3 (낮을수록 작은 소리도 말로 인정, 2였던 것을 1로)
MIN_SPEECH_MS = 300                                       # 이보다 짧은 소리는 잡음으로 버림 (짧은 대답도 받도록 400에서 낮춤)
MIN_RMS = 250                                             # 이보다 작은 소리는 말로 치지 않음 (작은 목소리도 받도록 350에서 낮춤)
OUT_RATE = 24000                                          # /api/tts 출력 = 24kHz 16bit mono PCM
OUT_FRAME_MS = 60
OUT_FRAME_SAMPLES = OUT_RATE * OUT_FRAME_MS // 1000
PREBUFFER_FRAMES = 20                                     # 기기 큐가 약 2.4초라서 너무 앞서 보내면 버려진다
SONG_MAX_S = 600
IDLE = True                                               # 대기 중에 가끔 고개/표정을 움직이고, 오래 두면 잠든다
IDLE_MIN_S = 12                                           # 대기 중 동작 간격 (초, 최소~최대 사이 무작위)
IDLE_MAX_S = 35
SLEEP_AFTER_S = 180                                       # 이만큼 아무 말이 없으면 잠든 표정으로
SLEEP_EMOTION = "sleepy"
SLEEP_TILT = -18                                          # 잘 때 고개를 떨구는 각도
IDLE_EMOTIONS = ["neutral", "happy", "thinking", "relaxed", "winking"]
TURN_MAX_S = 120                                          # 대답 생성/재생에서 이만큼 아무 진전이 없으면 멈춘 것으로 보고 풀어 준다 (먹통 방지)
MOTION = _env("XIAOZHI_MOTION", "1") != "0"   # XIAOZHI_MOTION=0 이면 고개 움직임 끔 (소리 끊김 원인 가려내기용)                                              # 고개 움직임 (self.robot.set_head_angles / center_head 사용)
MCP_ON = True
MAX_TURNS_KEPT = 40
MIN_FIRST, MIN_NEXT = 20, 70                               # taeyeon-pipe.html과 같은 문장 자르기 기준
STOP_EXTRA_S = 0.3                                          # 마지막 소리 재생이 끝난 뒤 이만큼 더 기다렸다가 tts stop을 보낸다

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


def _boost(pcm: bytes, target: int = 14000, max_gain: float = 6.0, min_peak: int = 600) -> bytes:
    """작게 녹음된 말을 모델이 더 잘 알아듣게 소리 크기를 키운다 (가장 큰 값이 target이 되도록, 최대 max_gain배).
    거의 무음이면(min_peak 미만) 잡음만 키우게 되니 그대로 둔다. 문제가 생기면 원본을 그대로 돌려준다."""
    try:
        from array import array
        a = array("h")
        a.frombytes(pcm[:len(pcm) - len(pcm) % 2])
        if not a:
            return pcm
        peak = max(max(a), -min(a))
        if peak < min_peak:
            return pcm
        g = min(max_gain, target / peak)
        if g < 1.1:
            return pcm
        return array("h", (max(-32768, min(32767, int(x * g))) for x in a)).tobytes()
    except Exception:
        return pcm


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
        self.peak = 0
        self.vad = webrtcvad.Vad(VAD_MODE) if webrtcvad else None

    def _voiced(self, fr: bytes) -> bool:
        if not self.vad:
            return False
        r = _rms(fr)
        if r < MIN_RMS:
            return False
        self.peak = max(self.peak, r)
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
        ok = len(pcm) >= 0.4 * 32000 and (self.manual or self.voiced_ms >= MIN_SPEECH_MS)
        if not self.manual:
            log.info("[xiaozhi] 소리 감지 %s: 말소리 %dms / 전체 %dms / 최대크기 %d",
                     "→ 대화로 보냄" if ok else "→ 소음으로 버림", self.voiced_ms, len(pcm) // 32, self.peak)
        self.__init__(self.manual)
        return pcm if ok else b""


# ===================== 실시간 속도로 프레임 내보내기 =====================
class Pacer:
    """기기는 받은 프레임을 바로 재생 큐에 쌓고(약 2.4초 한도, 넘치면 버림), 서버가 앞서 보내면 안 된다.
    첫 PREBUFFER 프레임은 바로, 그 뒤는 재생 시간에 맞춰 보낸다. 합성이 늦어 소리가 끊긴 뒤에는 시계를 다시 맞춘다."""

    def __init__(self, pre=None):
        self.start = None
        self.n = 0
        self.fd = OUT_FRAME_MS / 1000.0
        self.resets = 0
        self.pre = PREBUFFER_FRAMES if pre is None else pre

    def wait(self, cancel: threading.Event):
        now = time.monotonic()
        if self.start is None or now - self.start > self.n * self.fd + 0.3:   # 처음이거나, 기기 재생이 비었던 뒤
            if self.start is not None:
                self.resets += 1          # 서버가 소리를 제때 못 대서 기기 재생이 비었던 횟수
            self.start, self.n = now, 0
        due = self.start + self.n * self.fd - self.pre * self.fd
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
            self.nframes = getattr(self, "nframes", 0) + 1

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
            # [실험] 기기가 재생을 다 끝낸 뒤에 stop을 보낸다 (지금까지는 기기 큐에 최대 약 1.2초 분량이 남은 채로 stop이 갔다.
            #  로그상 기기가 멈추는 시점이 항상 tts stop 직후라서, stop 처리와 재생이 겹치는지 가려내려는 것)
            try:
                st = self.pacer.start
                left = (st + self.pacer.n * self.pacer.fd - time.monotonic() + STOP_EXTRA_S) if st else 0.0
            except Exception:
                left = 0.0
            if left > 0:
                self.cancel.wait(min(left, 5.0))
            if self.cancel.is_set():
                return
            self.s.send_json({"type": "tts", "state": "stop"})
            self.s.stop_at, self.s.n_audio_at_stop = time.monotonic(), getattr(self.s, "n_audio", 0)
            log.info("[xiaozhi] tts stop 전송 (소리 %d프레임 보냄, 연결 상태 closed=%s) | 진단: 재생 비었던 횟수=%d, 최대 프레임 간격=%.2fs, 최대 전송 막힘=%.2fs, 고개 움직임=%s",
                     getattr(self, "nframes", 0), self.s.closed, self.pacer.resets,
                     getattr(self.s, "max_gap", 0.0), getattr(self.s, "max_send", 0.0), "켜짐" if MOTION else "꺼짐")
            self.s.max_gap = self.s.max_send = 0.0
            threading.Timer(1.0, self.s.center_head).start()      # stop 처리와 고개 명령이 겹치지 않게 1초 뒤에


# ===================== Gemini Live 직접 연결 (파이프 모드 대신) =====================
# 파이프 모드: 말 끝 감지(0.9초) -> WAV 만들기 -> 받아쓰기/대답 생성(HTTP) -> 문장 자르기 -> 문장마다 TTS -> 재생
# Live 모드 : 기기 마이크 소리를 Gemini Live(WebSocket)로 바로 흘려보내고, 대답 소리(24kHz PCM)가 오는 대로 기기로 내보낸다.
#             말 끝 감지/받아쓰기/대답 생성/음성 합성이 모델 안에서 한 번에 일어나서 첫 소리까지 훨씬 빠르다.
XZ_MODE = _env("XIAOZHI_MODE", "pipe").lower()            # 입력은 항상 Gemini Live. live = 출력도 Live 목소리 / pipe(기본) = 출력은 문장별 TTS(타입캐스트)
LIVE_SILENCE_MS = 900                                     # Live 서버가 '말이 끝났다'고 보는 조용한 시간 (파이프의 END_SILENCE_MS=900보다 짧게)
LIVE_HANGOVER_MS = 1800                                   # 마지막 말소리 뒤로 이만큼은 조용한 소리도 계속 보낸다 (Live가 끝을 알아채야 해서)
LIVE_TAIL_MUTE_S = 0.5                                    # 대답이 끝난 뒤 스피커 잔향을 말로 오인하지 않게 잠깐 듣지 않는다
LIVE_GAIN = 1.8                                           # 작은 목소리를 모델이 더 잘 알아듣게 키우는 배수 (파이프의 _boost 대신 고정값)
LIVE_CONNECT_FAILS_MAX = 3                                # 처음부터 연속으로 이만큼 연결에 실패하면 파이프 모드로 되돌린다
LIVE_CLIENT = None
# 출력 방식은 XIAOZHI_MODE로 정한다 (입력은 두 경우 모두 Live):
#   pipe = Live가 만든 목소리는 버리고, 대답 글자(전사)를 문장마다 /api/tts(타입캐스트)로 읽는다
#   live = Live가 만든 목소리를 그대로 기기로 보낸다
LIVE_OUT_PIPE = XZ_MODE != "live"
XZ_WAKE = _env("XIAOZHI_WAKE", "1") != "0"                # pipe 출력일 때만 동작. 0이면 호출어 없이 늘 대화 (예전 방식)
CONVO_IDLE_S = 60                                         # 대화모드에서 이만큼 아무 말이 없으면 다시 호출어 대기로 돌아간다
WAKE_RE = re.compile(r"쎄\s*리|[세셰]\s*리\s*[야아]")       # 받아쓰기가 "세리야"처럼 적어도 호출어로 본다
KEEPALIVE_S = 20                                          # 조용한 동안에도 이만큼마다 기기에 가벼운 신호를 보낸다 (서버에서 오는 게 한참 없으면 기기가 연결을 닫고 대기로 갈 수 있어서)
LIVE_TEXT_TAIL_S = 0.6                                    # 턴이 끝난 뒤에도 마지막 대답 글자가 조금 늦게 오는 일이 있어서, 이만큼 더 기다렸다가 마무리한다


def _live_client():
    global LIVE_CLIENT
    if LIVE_CLIENT is None:
        from google import genai
        LIVE_CLIENT = genai.Client(api_key=_env("GEMINI_API_KEY"), http_options={"api_version": "v1beta"})
    return LIVE_CLIENT


def _live_available() -> bool:
    if not _env("GEMINI_API_KEY"):
        return False
    try:
        from google import genai  # noqa: F401
        from google.genai import types  # noqa: F401
        return True
    except Exception:
        return False


def _apply_gain(pcm: bytes, gain: float) -> bytes:
    if gain == 1.0 or not pcm:
        return pcm
    try:
        from array import array
        a = array("h")
        a.frombytes(pcm[:len(pcm) - len(pcm) % 2])
        return array("h", (max(-32768, min(32767, int(x * gain))) for x in a)).tobytes()
    except Exception:
        return pcm


class LiveGate:
    """마이크 소리를 Live로 보낼지 정하는 문. 말소리가 시작되면 열리고(시작 전 300ms 포함), 마지막 말소리 뒤 LIVE_HANGOVER_MS가
    지나면 닫힌다. 문이 닫혀 있는 동안의 잡음/배경소리는 Live로 보내지 않아서 엉뚱한 대답을 막는다.
    manual(화면을 눌러 말하는 방식)이거나 webrtcvad가 없으면 걸러내지 않고 그대로 통과시킨다."""
    FR = 320  # 20ms @16kHz

    def __init__(self, manual=False):
        self.manual = manual
        self.buf = bytearray()
        self.pre = deque(maxlen=15)
        self.recent = deque(maxlen=8)
        self.open = False
        self.quiet_ms = 0
        self.last_voiced = 0.0
        self.sent_ms = 0                # 이번에 문이 열려 있는 동안 Live로 보낸 소리 길이
        self.vad = webrtcvad.Vad(VAD_MODE) if webrtcvad else None

    def _voiced(self, fr: bytes) -> bool:
        if _rms(fr) < MIN_RMS:
            return False
        try:
            return self.vad.is_speech(fr, 16000)
        except Exception:
            return False

    def feed(self, pcm: bytes) -> bytes:
        if self.manual or not self.vad:
            return pcm
        self.buf += pcm
        out = bytearray()
        while len(self.buf) >= self.FR * 2:
            fr = bytes(self.buf[:self.FR * 2])
            del self.buf[:self.FR * 2]
            v = self._voiced(fr)
            if v:
                self.last_voiced = time.monotonic()
            if not self.open:
                self.pre.append(fr)
                self.recent.append(v)
                if sum(self.recent) >= 5:
                    self.open, self.quiet_ms = True, 0
                    out += b"".join(self.pre)
                    self.sent_ms = len(self.pre) * 20
                    self.pre.clear()
                    log.info("[xiaozhi] 말소리 감지 -> Live로 보내기 시작")
            else:
                out += fr
                self.sent_ms += 20
                self.quiet_ms = 0 if v else self.quiet_ms + 20
                if self.quiet_ms >= LIVE_HANGOVER_MS:
                    log.info("[xiaozhi] 말소리 끝 -> Live로 보낸 소리 %.1f초 (조용한 %.1f초 포함)", self.sent_ms / 1000, self.quiet_ms / 1000)
                    self.open = False
                    self.recent.clear()
        return bytes(out)


class LiveSpeaker(Speaker):
    """Speaker에서 문장 자르기/TTS 합성 부분은 빼고, 소리 내보내기(Opus 인코딩, 속도 맞추기, tts start/stop, 노래, 부저)만 쓴다."""

    def __init__(self, sess, cancel):
        self.s, self.cancel = sess, cancel
        self.started = False
        self.last_emo = ""
        self.pacer = Pacer()
        self.enc = opuslib.Encoder(OUT_RATE, 1, opuslib.APPLICATION_AUDIO)

    def close(self):
        pass


class _Turn:
    def __init__(self, sess):
        self.cancel = threading.Event()
        self.speaker = Speaker(sess, self.cancel) if LIVE_OUT_PIPE else LiveSpeaker(sess, self.cancel)
        self.done = False               # Live가 턴 끝을 알려 왔다 (pipe 출력: 늦게 오는 글자를 기다리는 중)
        self.fin = None                 # 마무리 예약 (loop.call_later 핸들)
        self.rem = b""                  # 아직 60ms 프레임으로 못 채운 소리 조각
        self.otext = ""                 # 대답 글자(전사)
        self.obuf = ""                  # 아직 문장으로 못 자른 대답 글자
        self.nsent = 0
        self.t0 = time.monotonic()


_SETUP_CACHE = {"d": None, "t": 0.0}


class LiveLink:
    """기기 한 대와 Gemini Live 사이의 서버 쪽 연결. asyncio 루프를 별도 스레드에서 돌리고,
    소리 입력(기기 -> Live)은 큐로, 소리 출력(Live -> 기기)은 출력 스레드로 넘긴다."""

    def __init__(self, sess):
        import asyncio
        self.asyncio = asyncio
        self.s = sess
        self.loop = asyncio.new_event_loop()
        self.in_q = None
        self.out_q = queue.Queue()
        self.connected = False
        self.dead = False
        self.handle = None
        self.setup = None
        self.fails = 0
        self.ever_ready = False
        self.main_task = None
        self.turn = None
        self.utext = ""
        self.gen_active = False
        self.discard = False
        self.pending_song = None
        self.want_reconnect = False
        self.thought_sent = False
        self.hold = ""                          # 호출어 확인 전에 받은 대답 글자
        threading.Thread(target=self._run, daemon=True, name="xz-live").start()
        threading.Thread(target=self._out_worker, daemon=True, name="xz-live-out").start()

    # ---------- 바깥(동기 스레드)에서 부르는 함수 ----------
    def feed(self, pcm: bytes):
        if self.dead or self.in_q is None or not pcm:
            return
        pcm = _apply_gain(pcm, LIVE_GAIN)      # 연결 전/재연결 중에 들어온 소리도 쌓아 뒀다가 연결되면 보낸다 (8초 넘은 것은 버림)
        self.loop.call_soon_threadsafe(self._put, ("audio", pcm, time.monotonic()))

    def _put(self, item):
        try:
            self.in_q.put_nowait(item)
        except self.asyncio.QueueFull:
            try:
                self.in_q.get_nowait()
                self.in_q.put_nowait(item)
            except Exception:
                pass

    def end_input(self):
        """화면을 눌러 말하는 방식에서 손을 뗐을 때: 조용한 소리를 덧붙여 Live가 말이 끝났음을 바로 알게 한다."""
        if self.in_q is not None and not self.dead:
            now = time.monotonic()
            self.loop.call_soon_threadsafe(self._put, ("audio", b"\0" * 32000, now))
            self.loop.call_soon_threadsafe(self._put, ("end", None, now))

    def interrupt(self):
        """기기가 abort/listen start를 보냈다: 말하던 것을 멈추고, 이미 만들어지는 중인 대답의 남은 소리는 버린다."""
        t = self.turn
        self.hold = ""
        if t is not None:
            t.cancel.set()
            if LIVE_OUT_PIPE:
                t.speaker.q.put(None)       # 합성/전송 스레드를 끝낸다
        if self.gen_active:
            self.discard = True
        self.turn = None
        while True:
            try:
                self.out_q.get_nowait()
            except queue.Empty:
                break

    def close(self):
        self.out_q.put(None)
        try:
            self.loop.call_soon_threadsafe(lambda: self.main_task and self.main_task.cancel())
        except Exception:
            pass

    # ---------- asyncio 쪽 ----------
    def _run(self):
        self.asyncio.set_event_loop(self.loop)
        self.in_q = self.asyncio.Queue(maxsize=400)
        self.main_task = self.loop.create_task(self._main())
        try:
            self.loop.run_until_complete(self.main_task)
        except BaseException:
            pass
        finally:
            try:
                self.loop.close()
            except Exception:
                pass

    async def _main(self):
        backoff = 1.0
        while not self.s.closed:
            try:
                await self._connect_once()
                backoff = 1.0
            except self.asyncio.CancelledError:
                return
            except Exception as e:
                if "inactivity" in str(e):          # 한동안 말이 없어서 Live가 세션을 닫은 것: 정상, 바로 다시 연결
                    log.info("[xiaozhi] Live가 조용한 연결을 닫음 - 다시 연결합니다")
                    self.connected = False
                    continue
                self.fails += 1
                log.warning("[xiaozhi] Live 연결/수신 오류 (%d회째, %s): %s", self.fails, type(e).__name__, str(e)[:300])
                if not self.ever_ready and self.fails >= LIVE_CONNECT_FAILS_MAX:
                    self.dead = True
                    log.error("[xiaozhi] Live 연결이 처음부터 %d번 연속 실패 - 파이프 모드로 되돌립니다", self.fails)
                    self.s.live_failed()
                    return
            finally:
                self.connected = False
            if self.s.closed:
                return
            await self.asyncio.sleep(min(backoff, 8.0))
            backoff *= 2

    def _fetch_setup(self):
        c = _SETUP_CACHE
        if c["d"] and time.monotonic() - c["t"] < 300:      # OTA 때 미리 받아 둔 설정이 있으면 바로 쓴다 (프롬프트 조립이 몇 초 걸린다)
            return c["d"]
        body = {}
        if XZ_LAT and XZ_LNG:
            body["lat"], body["lng"] = XZ_LAT, XZ_LNG
        r = self.s._client().post("/api/live/setup", json=body, headers=self.s.auth_headers())
        d = r.get_json(silent=True) or {}
        if r.status_code != 200 or not d.get("system_prompt"):
            raise RuntimeError(f"/api/live/setup {r.status_code}: {str(d)[:120]}")
        c["d"], c["t"] = d, time.monotonic()
        return d

    def _build_config(self, setup, minimal=False):
        from google.genai import types as T
        tools = []
        if setup.get("search"):
            tools.append(T.Tool(google_search=T.GoogleSearch()))
        decls = setup.get("functions") or []
        if decls:
            tools.append(T.Tool(function_declarations=[
                T.FunctionDeclaration(name=d["name"], description=d["description"], parameters=d["parameters"]) for d in decls]))
        kw = dict(
            response_modalities=["AUDIO"],
            system_instruction=setup["system_prompt"],
            speech_config=T.SpeechConfig(voice_config=T.VoiceConfig(
                prebuilt_voice_config=T.PrebuiltVoiceConfig(voice_name=setup.get("voice") or "Leda"))),
            input_audio_transcription=(T.AudioTranscriptionConfig() if minimal else T.AudioTranscriptionConfig(language_codes=["ko-KR"])),
            output_audio_transcription=T.AudioTranscriptionConfig(),
        )
        if tools:
            kw["tools"] = tools
        if not minimal:
            kw["realtime_input_config"] = T.RealtimeInputConfig(automatic_activity_detection=T.AutomaticActivityDetection(
                start_of_speech_sensitivity=T.StartSensitivity.START_SENSITIVITY_HIGH,
                end_of_speech_sensitivity=T.EndSensitivity.END_SENSITIVITY_LOW,
                prefix_padding_ms=200, silence_duration_ms=LIVE_SILENCE_MS))
            kw["context_window_compression"] = T.ContextWindowCompressionConfig(sliding_window=T.SlidingWindow())
            kw["session_resumption"] = T.SessionResumptionConfig(handle=self.handle)
        return T.LiveConnectConfig(**kw)

    async def _connect_once(self):
        loop = self.asyncio.get_running_loop()
        if self.setup is None or self.handle is None:      # 새 세션이면 직전 대화 블록까지 새로 받는다
            self.setup = await loop.run_in_executor(None, self._fetch_setup)
        minimal = self.fails >= 2                           # 이상 설정 때문에 거절되는 경우를 위한 최소 설정 재시도
        cfg = self._build_config(self.setup, minimal=minimal)
        model = self.setup.get("model") or "models/gemini-3.8-live"
        t0 = time.monotonic()
        self.want_reconnect = False
        async with _live_client().aio.live.connect(model=model, config=cfg) as session:
            self.connected = True
            self.ever_ready = True
            self.fails = 0
            log.info("[xiaozhi] Gemini Live 연결됨 model=%s voice=%s 도구=%s %s (%.1fs)", model, self.setup.get("voice"),
                     len(self.setup.get("functions") or []), "(최소 설정)" if minimal else "",
                     time.monotonic() - t0)
            sender = self.loop.create_task(self._sender(session))
            try:
                await self._receiver(session)
            finally:
                sender.cancel()
                self.connected = False

    async def _sender(self, session):
        from google.genai import types as T
        while True:
            kind, data, ts = await self.in_q.get()
            if kind == "audio":
                if time.monotonic() - ts > 8.0:
                    continue
                await session.send_realtime_input(audio=T.Blob(data=data, mime_type="audio/pcm;rate=16000"))
            elif kind == "end":
                await session.send_realtime_input(audio_stream_end=True)

    async def _receiver(self, session):
        from google.genai import types as T
        loop = self.asyncio.get_running_loop()
        while not self.s.closed:
            got = False
            async for msg in session.receive():      # 한 턴이 끝나면 이 반복이 끝나서, 바깥 while로 계속 받는다
                got = True
                if msg.session_resumption_update and getattr(msg.session_resumption_update, "new_handle", None):
                    self.handle = msg.session_resumption_update.new_handle
                if msg.go_away:
                    log.info("[xiaozhi] Live 서버가 곧 연결을 닫는다고 알려 옴 (%s) - 대답이 끝나면 다시 연결합니다",
                             getattr(msg.go_away, "time_left", None))
                    self.want_reconnect = True
                    if not self.gen_active:
                        return
                sc = msg.server_content
                if sc is not None:
                    if sc.interrupted:
                        self._on_interrupted()
                    if sc.input_transcription and sc.input_transcription.text:
                        self._on_input_text(sc.input_transcription.text)
                    if sc.model_turn and sc.model_turn.parts:          # 소리를 먼저 처리해야 턴이 만들어진 뒤 글자가 붙는다
                        for p in sc.model_turn.parts:
                            idata = getattr(p, "inline_data", None)
                            if idata and idata.data:
                                self._on_audio(idata.data)
                    if sc.output_transcription and sc.output_transcription.text:
                        self._on_output_text(sc.output_transcription.text)
                    if sc.turn_complete:
                        self._on_turn_complete()
                        if self.want_reconnect:
                            return
                if msg.tool_call and msg.tool_call.function_calls:
                    calls = list(msg.tool_call.function_calls)
                    if LIVE_OUT_PIPE and self.turn is not None:      # "잠시만요" 같은 앞말이 버퍼에 갇혀 있지 않게 바로 읽는다
                        self.turn.speaker.flush()
                    if self._wake_pending() and not self._check_wake():     # 호출하지 않은 말에는 도구(기억/노래 등)를 실행하지 않는다
                        resps = [{"found": False, "message": "호출되지 않은 말이라 실행하지 않았어요. 아무 말 없이 넘어가세요."} for _ in calls]
                    else:
                        resps = await self.asyncio.gather(*[loop.run_in_executor(None, self._run_tool, c) for c in calls])
                    await session.send_tool_response(function_responses=[
                        T.FunctionResponse(id=c.id, name=c.name, response=r) for c, r in zip(calls, resps)])
            if not got:
                await self.asyncio.sleep(0.05)

    # ---------- 모델이 보낸 것 처리 ----------
    def _wake_pending(self) -> bool:
        """호출어를 기다리는 중인가 (pipe 출력 + 호출어 켜짐 + 대화모드 아님)."""
        return LIVE_OUT_PIPE and XZ_WAKE and not self.s.in_convo()

    def _check_wake(self) -> bool:
        """지금까지 받아쓴 내 말에 호출어가 있으면 대화모드로 들어가고 True."""
        if not self._wake_pending():
            return True
        if WAKE_RE.search(self.utext):
            self.s.enter_convo("호출어: %r" % " ".join(self.utext.split())[:30])
            return True
        return False

    def _on_input_text(self, text):
        self.discard = False
        self.utext += text
        log.info("[xiaozhi] Live 받아쓰기: %r", text[:60])
        if self._wake_pending() and not self._check_wake():
            return                              # 호출어가 없는 말: 표정/고개도 반응하지 않는다
        self.s.touch()
        if self.hold and self.turn is None and self.gen_active:     # 받아쓰기가 대답 글자보다 늦게 와서 이제야 호출어가 확인됐다
            t = self._begin_turn()
            t.otext += self.hold
            t.speaker.feed(self.hold)
            self.hold = ""
        if not self.thought_sent:                 # 내 말이 들어오기 시작하면 '생각 중' 표정/고개
            self.thought_sent = True
            self.s.motion_think()
            self.s.send_json({"type": "llm", "emotion": "thinking", "text": ""})

    def _begin_turn(self):
        t = _Turn(self.s)
        self.s.busy = True
        self.s.cancel = t.cancel
        self.s.turn_t0 = self.s.turn_progress = time.monotonic()
        self.turn = t
        if LIVE_OUT_PIPE and XZ_WAKE and self.s.convo_until:
            self.s.convo_until = time.monotonic() + CONVO_IDLE_S
        if not LIVE_OUT_PIPE:           # pipe 출력은 첫 문장 소리가 합성돼 나올 때 Speaker가 tts start를 보낸다
            t.speaker._begin()
        user = " ".join(self.utext.split())
        if user:
            self.s.send_json({"type": "stt", "text": user})
        lv = getattr(self.s.gate, "last_voiced", 0.0) if self.s.gate else 0.0
        if lv:
            log.info("[xiaozhi] 마지막 말소리 뒤 %.2fs 만에 첫 대답 소리 도착 (입력=%r)", time.monotonic() - lv, user[:30])
        return t

    def _on_audio(self, data: bytes):
        if self.discard:
            return
        self.gen_active = True
        if self._wake_pending() and not self._check_wake():
            return                      # 호출어를 듣기 전에는 턴을 열지 않는다 (기기는 가만히 있는다)
        t = self.turn or self._begin_turn()
        self.s.turn_progress = time.monotonic()
        if LIVE_OUT_PIPE:
            return                      # Live의 목소리는 쓰지 않고 버린다 (대답 글자만 받아서 TTS로 읽는다)
        self.out_q.put(("pcm", t, data))

    def _on_output_text(self, text):
        if self.discard:
            return
        t = self.turn
        if t is None and self.gen_active and self._wake_pending():
            self.hold += text           # 호출어를 들었는지 확인될 때까지 글자를 쥐고 있는다
            if not self._check_wake():
                return
            t = self._begin_turn()
            text, self.hold = self.hold, ""
        if t is None:
            return
        if LIVE_OUT_PIPE:
            t.otext += text
            self.s.turn_progress = time.monotonic()
            if t.fin is not None:           # 턴 끝 뒤에 글자가 더 왔다: 마무리를 뒤로 미룬다
                self._arm_finalize(t)
            t.speaker.feed(text)            # 문장으로 잘라 /api/tts로 합성하고 순서대로 기기에 보낸다
            return
        t.otext += text
        t.obuf += text
        while True:
            cut = _find_cut(t.obuf, t.nsent == 0)
            if cut <= 0:
                break
            piece, t.obuf = t.obuf[:cut], t.obuf[cut:]
            self._sentence(t, piece)

    def _sentence(self, t, raw):
        txt = _clean(raw)
        if not txt:
            return
        t.nsent += 1
        emo = _guess_emotion(txt)
        if emo and emo != t.speaker.last_emo:
            t.speaker.last_emo = emo
            self.s.send_json({"type": "llm", "emotion": emo, "text": ""})
        self.s.send_json({"type": "tts", "state": "sentence_start", "text": _TAG.sub("", txt).strip()})
        self.s.motion_speak(emo or t.speaker.last_emo)

    def _on_turn_complete(self):
        self.gen_active = False
        self.thought_sent = False
        if self.discard:
            self.discard = False
            self.utext = ""
            if LIVE_OUT_PIPE and self.turn is not None:
                self.turn.cancel.set()
                self.turn.speaker.q.put(None)
                self.turn = None
            return
        t = self.turn
        if t is None and self._wake_pending():
            if self._check_wake():                # 호출어가 늦게 확인됐다: 쥐고 있던 글자를 지금 읽는다
                t = self._begin_turn()
                if self.hold:
                    t.otext += self.hold
                    t.speaker.feed(self.hold)
                    self.hold = ""
            else:                                 # 호출어가 없던 말: 조용히 넘어간다
                log.info("[xiaozhi] 대화모드가 아니라 호출어 없는 말은 무시: %r (XIAOZHI_WAKE=0 이면 호출어 없이 늘 대답)", " ".join(self.utext.split())[:40])
                self.hold, self.utext = "", ""
                return
        if t is None and self.pending_song:       # 말 없이 노래만 틀라고 한 경우
            t = self._begin_turn()
        if t is None:
            self.utext = ""
            return
        if LIVE_OUT_PIPE:
            self._arm_finalize(t)                 # 마지막 글자가 늦게 올 수 있어서 잠깐 기다렸다가 마무리
            return
        if t.obuf.strip():
            self._sentence(t, t.obuf)
            t.obuf = ""
        user, self.utext = " ".join(self.utext.split()), ""
        self.out_q.put(("end", t, user))
        self.turn = None

    def _arm_finalize(self, t):
        """(pipe 출력) Live 턴이 끝났다: LIVE_TEXT_TAIL_S 동안 더 오는 글자가 없으면 이 턴을 마무리한다. 글자가 오면 미뤄진다."""
        t.done = True
        if t.fin is not None:
            t.fin.cancel()
        t.fin = self.loop.call_later(LIVE_TEXT_TAIL_S, self._finalize_turn, t)

    def _finalize_turn(self, t):
        t.fin = None
        if self.turn is t:
            self.turn = None
        user, self.utext = " ".join(self.utext.split()), ""
        if t.cancel.is_set():
            return
        self.out_q.put(("end", t, user))

    def _on_interrupted(self):
        self.gen_active = False
        self.discard = False
        self.hold = ""
        t = self.turn
        self.turn = None
        if t is not None:
            t.cancel.set()
            if LIVE_OUT_PIPE:
                t.speaker.q.put(None)
            if self.s.cancel is t.cancel:
                self.s.busy = False
            self.s.send_json({"type": "tts", "state": "stop"})
        log.info("[xiaozhi] Live가 말을 끊었음(사용자가 말을 시작함)")

    def _run_tool(self, call) -> dict:
        name, args = call.name, dict(call.args or {})
        self.s.turn_progress = time.monotonic()
        try:
            body = {"name": name, "args": args}
            if XZ_LAT and XZ_LNG:
                body["lat"], body["lng"] = XZ_LAT, XZ_LNG
            r = self.s._client().post("/api/live/tool", json=body, headers=self.s.auth_headers())
            d = r.get_json(silent=True) or {}
            if d.get("play"):
                self.pending_song = d["play"]
            res = d.get("response")
            return res if isinstance(res, dict) else {"found": False, "message": "지금은 확인하지 못했어요"}
        except Exception as e:
            log.warning("[xiaozhi] 함수 %s 실행 실패: %s", name, e)
            return {"found": False, "message": "지금은 확인하지 못했어요"}

    # ---------- 출력 스레드 (기기로 실시간 속도에 맞춰 보낸다) ----------
    def _out_worker(self):
        fb = OUT_FRAME_SAMPLES * 2
        while True:
            item = self.out_q.get()
            if item is None:
                return
            kind, t, payload = item
            try:
                if t.cancel.is_set() or self.s.closed:
                    continue
                if kind == "pcm":
                    t.rem += payload
                    n = len(t.rem) // fb * fb
                    if n:
                        chunk, t.rem = t.rem[:n], t.rem[n:]
                        t.speaker.emit_pcm(chunk)         # 속도 맞추느라 여기서 기다린다. 그동안 새 소리는 큐에 쌓인다
                elif kind == "end":
                    self._finish(t, payload)
            except Exception:
                log.exception("[xiaozhi] Live 소리 내보내기 실패")

    def _finish(self, t, user_text):
        sp, s = t.speaker, self.s
        if LIVE_OUT_PIPE:
            sp.flush()
            sp.close()                  # 남은 문장 합성/전송이 다 끝날 때까지 기다린다
        elif t.rem:
            sp.emit_pcm(t.rem)
            t.rem = b""
        song, self.pending_song = self.pending_song, None
        if song and not t.cancel.is_set():
            sp.play_song(song)
        sp.end()
        reply = " ".join(_clean(t.otext).split())
        if reply and not t.cancel.is_set():
            s.turns += [{"role": "user", "text": user_text or "(음성 메시지)"}, {"role": "model", "text": reply}]
            s.turns = s.turns[-MAX_TURNS_KEPT:]
            if user_text:
                threading.Thread(target=s.save_turn, args=(user_text, reply), daemon=True).start()
        log.info("[xiaozhi] Live 턴 완료 %.1fs 취소=%s 입력=%r", time.monotonic() - t.t0, t.cancel.is_set(), user_text[:30])
        s.last_active = time.monotonic()
        if LIVE_OUT_PIPE and XZ_WAKE and s.convo_until:
            s.convo_until = time.monotonic() + CONVO_IDLE_S       # 대답이 끝난 때부터 다시 센다
        if s.cancel is t.cancel:
            s.busy = False
            s._mute_until = time.monotonic() + LIVE_TAIL_MUTE_S
            if not s.closed:
                s.gate = LiveGate(manual=(s.mode == "manual"))


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
        self.turn_t0 = time.monotonic()
        self.t0 = time.monotonic()
        self.last_active = time.monotonic()     # 마지막으로 대화/말소리가 있던 때 (대기 동작과 잠들기 기준)
        self.asleep = False
        self._web = None                        # 웹 화면에서 보낸 글을 읽는 중인 대답 (say_chunk)
        self._say_lock = threading.Lock()
        self.turn_progress = time.monotonic()   # 마지막으로 대답이 진전된 때 (소리 전송/서버 응답 조각)
        self.has_robot = False
        self._mute_until = 0.0                  # 대기 동작 중 모터 소리를 말로 오인하지 않게 잠깐 듣지 않는다
        self.live = None                        # Gemini Live 연결 (live 모드일 때)
        self.gate = None                        # 마이크 소리를 Live로 보낼지 정하는 문
        self.convo_until = 0.0                  # 대화모드가 이어지는 시각 (0 = 호출어 대기 중)
        self._listened = False                  # 이 연결에서 기기가 listen start를 이미 보냈나

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
            t0 = time.monotonic()
            with self.send_lock:
                self.ws.send(data)
            t1 = time.monotonic()
            self.max_send = max(getattr(self, "max_send", 0.0), t1 - t0)       # 소켓 전송이 막힌 최대 시간 (Wi-Fi/기기가 못 받을 때 커진다)
            lt = getattr(self, "_last_send", None)
            if lt is not None and t1 - lt < 2.0:
                self.max_gap = max(getattr(self, "max_gap", 0.0), t1 - lt)     # 프레임 사이 최대 간격 (정상은 0.06초 이하)
            self._last_send = t1
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
            if self.live is None and self.gate is None and _live_available():
                self.gate = LiveGate()
                self.live = LiveLink(self)
                self.ctx_ready.set()
            elif self.live is None:
                threading.Thread(target=self._prepare, daemon=True).start()
            log.info("[xiaozhi] 기기 연결 (%s 모드) device=%s ver=%s 입력=%sHz/%sms", ("live→pipe" if LIVE_OUT_PIPE else "live") if self.live else "pipe", self.device_id, self.version, self.in_rate, self.in_frame_ms)
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
                if self.busy:
                    log.warning("[xiaozhi] 대답을 기다리는 중(%.1fs 경과)에 기기가 listen start를 보내 이번 턴을 취소합니다", time.monotonic() - self.turn_t0)
                self.abort()
                self.touch()
                self.mode = str(obj.get("mode") or "auto")
                if self.live and LIVE_OUT_PIPE and XZ_WAKE and (self.mode == "manual" or not self._listened):
                    # 대기 중에는 연결이 없으니, 새 연결의 첫 listen start는 화면을 터치했거나 기기 호출어로 깨운 것이다.
                    # (이후 auto 신호는 대답 뒤마다 오는 것이라 대화모드로 치지 않는다)
                    self.enter_convo("연결 직후 첫 listen start (mode=%s)" % self.mode)
                self._listened = True
                if self.live:
                    self.gate = LiveGate(manual=(self.mode == "manual"))
                else:
                    self.ep = Endpointer(manual=(self.mode == "manual"))
                if self.mode == "manual" and not self.busy:      # 화면을 눌러 시작한 대화: 바로 듣고 부저음
                    threading.Thread(target=self._beep_only, daemon=True, name="xz-beep").start()
            elif st == "stop":
                if self.live:
                    if self.gate is not None and self.gate.manual:
                        self.live.end_input()
                elif self.ep is not None and self.ep.manual:
                    self._on_utterance(self.ep.finish())
                    self.ep = None
            elif st == "detect":
                log.info("[xiaozhi] 웨이크워드 감지: %r", obj.get("text"))
                if self.live and LIVE_OUT_PIPE and XZ_WAKE:
                    self.enter_convo("기기 웨이크워드")
        elif t == "abort":
            if self.busy:
                log.warning("[xiaozhi] 대답을 기다리는 중(%.1fs 경과)에 기기가 abort를 보내 이번 턴을 취소합니다 (reason=%r)", time.monotonic() - self.turn_t0, obj.get("reason"))
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
                log.info("[xiaozhi] MCP 응답: %s", json.dumps(pl, ensure_ascii=False)[:600])
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

    def _beep_only(self):
        sp = Speaker(self, threading.Event())
        sp.beep()
        sp.close()
        sp.end()

    # --- 대기 모드: 가끔 고개/표정, 오래 두면 잠든다 ---
    def in_convo(self) -> bool:
        if self.convo_until and time.monotonic() >= self.convo_until:
            self.convo_until = 0.0
            log.info("[xiaozhi] 대화모드 종료 - 호출어를 기다립니다")
        return self.convo_until > 0

    def enter_convo(self, why=""):
        """대화모드로 들어간다 (호출어를 들었거나 화면을 눌렀을 때). 이후 말은 호출어 없이 계속 대답하고, CONVO_IDLE_S 동안 조용하면 끝난다."""
        was = self.in_convo()
        self.convo_until = time.monotonic() + CONVO_IDLE_S
        self.touch()
        if not was:
            log.info("[xiaozhi] 대화모드 시작 (%s)", why)

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
        last_ka = time.monotonic()
        while not self.closed:
            time.sleep(1.0)
            now = time.monotonic()
            if KEEPALIVE_S and now - last_ka >= KEEPALIVE_S:
                last_ka = now
                self.send_json({"session_id": self.session_id, "type": "keepalive"})      # 기기가 모르는 종류의 신호는 무시하고, 받았다는 사실만 남는다
            if self.busy and now - self.turn_progress > TURN_MAX_S:
                # 대답이 멈춰 버린 경우(예: 서버가 응답을 안 줌): 계속 '처리 중'으로 두면 이후 모든 말을 무시하게 된다
                log.warning("[xiaozhi] 대답이 %ds 넘게 진전이 없어 이번 턴을 취소하고 다시 듣습니다", TURN_MAX_S)
                self.cancel.set()
                if self.live:
                    self.live.interrupt()
                    self.gate = LiveGate(manual=(self.mode == "manual"))
                self.busy = False
                if self.mode != "manual" and not self.live:
                    self.ep = Endpointer()
                self.send_json({"type": "tts", "state": "stop"})
                self.last_active = now
                continue
            if self.busy or self._hearing():
                self.touch()                  # 말소리가 들리면 잠에서 깬다
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

    def _hearing(self) -> bool:
        """지금 사람 말소리가 들어오는 중인가 (대기 동작/잠들기 판단용)."""
        if self.live:
            if LIVE_OUT_PIPE and XZ_WAKE and not self.in_convo():
                return False            # 호출어 대기 중에는 주변 말소리로 깨어나지 않는다
            return bool(self.gate is not None and self.gate.open)
        return bool(self.ep is not None and self.ep.started)

    def live_failed(self):
        """Live 연결이 처음부터 계속 실패했다: 예전 파이프 방식으로 되돌린다."""
        self.live, self.gate = None, None
        self.ep = Endpointer(manual=(self.mode == "manual"))
        threading.Thread(target=self._prepare, daemon=True).start()

    def save_turn(self, user: str, reply: str):
        try:
            self._client().post("/api/live/log", json={"tid": "x" + uuid.uuid4().hex[:15], "user": user, "model": reply},
                                headers=self.auth_headers())
        except Exception as e:
            log.warning("[xiaozhi] 대화 기록 저장 실패: %s", e)

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
        if self.dec is None or self.busy or (self.live is None and self.ep is None):
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
        if self.live:                       # Live 모드: 말소리가 열린 동안만 Live로 흘려보낸다 (말 끝은 Live 서버가 판단)
            if self.gate is not None:
                sent = self.gate.feed(pcm)
                if sent:
                    self.live.feed(sent)
            return
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
            if self.live:
                self.live.interrupt()
            self.busy = False      # 이전 턴 스레드가 정리되길 기다리지 않고 바로 다음 말을 받는다

    def _on_utterance(self, pcm: bytes):
        if not pcm or self.busy:
            return
        self.busy = True
        self.turn_t0 = self.turn_progress = time.monotonic()
        self.cancel = threading.Event()
        self.touch()
        self.motion_think()
        self.send_json({"type": "llm", "emotion": "thinking", "text": ""})      # 대답을 기다리는 동안 기기 화면이 멈춘 것처럼 보이지 않게
        threading.Thread(target=self._turn, args=(pcm, self.cancel), daemon=True, name="xz-turn").start()

    # --- 한 턴 ---
    def _turn(self, pcm: bytes, cancel: threading.Event):
        speaker = None
        t_start = time.monotonic()
        try:
            self.ctx_ready.wait(timeout=5)
            tid = "x" + uuid.uuid4().hex[:15]
            payload = {"audio": base64.b64encode(_wav16k(_boost(pcm))).decode(), "mime": "audio/wav",
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
            self.last_active = time.monotonic()
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
        if _live_available():      # 기기는 OTA 뒤 곧 WebSocket에 붙는다: 그 사이에 Live 설정(프롬프트)을 미리 만들어 둔다
            def _prefetch():
                try:
                    class _P:
                        s = type("S", (), {"_client": lambda self_: app.test_client(), "auth_headers": staticmethod(auth_headers)})()
                    LiveLink._fetch_setup(_P)
                except Exception as e:
                    log.warning("[xiaozhi] Live 설정 미리 받기 실패: %s", e)
            threading.Thread(target=_prefetch, daemon=True).start()
        return jsonify({
            "server_time": {"timestamp": int(time.time() * 1000), "timezone_offset": 540},
            "firmware": {"version": cur_ver, "url": ""},         # 지금 버전을 그대로 돌려줘서 자동 업데이트를 하지 않는다
            "websocket": {"url": ws_url, "token": _device_token(device_id), "version": 1},
        })

    @app.get("/xiaozhi/healthz")
    def xz_health():
        return jsonify({"enabled": True, "mode": ("live→pipe" if LIVE_OUT_PIPE else "live") if _live_available() else "pipe", "opus": opuslib is not None,
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
            if sess.busy:
                log.warning("[xiaozhi] 대답을 기다리는 중(%.1fs 경과)에 기기 연결이 끊겼습니다", time.monotonic() - sess.turn_t0)
            log.info("[xiaozhi] 연결 종료 device=%s (%s) | 연결 %.1f초, 받은 소리 %d프레임, 받은 메시지 %s", device_id, type(e).__name__,
                     time.monotonic() - sess.t0, getattr(sess, "n_audio", 0), getattr(sess, "seen", {}))
            _sa = getattr(sess, "stop_at", None)
            log.info("[xiaozhi] 종료 상세: reason=%r message=%r | 마지막 tts stop 이후 %s, 그 뒤 받은 소리 %s프레임",
                     getattr(e, "reason", None), getattr(e, "message", None),
                     ("%.1f초 지남" % (time.monotonic() - _sa)) if _sa else "stop 보낸 적 없음",
                     (getattr(sess, "n_audio", 0) - sess.n_audio_at_stop) if _sa else "-")
        finally:
            sess.closed = True
            sess.cancel.set()
            if sess.live:
                sess.live.close()
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
        /xiaozhi/test?key=KEY&sleep=1 / wake=1    잠들기 / 깨우기
        /xiaozhi/test?key=KEY&tone=1[&secs=6&freq=440&pre=20]   일정한 소리를 같은 경로로 보내 스피커/전송 점검 (끝나면 로그에 진단 줄)
        /xiaozhi/test?key=KEY&volume=50           기기 볼륨 (0~100)
        /xiaozhi/test?key=KEY&status=1            기기 상태 요청 (응답은 서버 로그)"""
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
        if a.get("volume") is not None:
            try:
                vol = max(0, min(100, int(a["volume"])))
            except ValueError:
                return jsonify({"error": "volume은 0~100 숫자여야 해요"}), 400
            sess._mcp_call("tools/call", {"name": "self.audio_speaker.set_volume", "arguments": {"volume": vol}})
            done.append(f"volume={vol}")
        if a.get("status"):
            sess._mcp_call("tools/call", {"name": "self.get_device_status", "arguments": {}})
            done.append("status 요청 (결과는 서버 로그에 찍힘)")
        if a.get("tone"):
            try:
                secs = max(1, min(20, int(a.get("secs", 6))))
                freq = max(100, min(4000, int(a.get("freq", 440))))
                pre = max(0, min(40, int(a.get("pre", PREBUFFER_FRAMES))))
            except ValueError:
                return jsonify({"error": "secs/freq는 숫자여야 해요"}), 400

            def _tone():
                sess._mute_until = time.monotonic() + secs + 1.5
                sp = LiveSpeaker(sess, threading.Event())
                sp.pacer = Pacer(pre)
                n = OUT_RATE * secs
                fade = OUT_RATE // 50
                pcm = b"".join(struct.pack("<h", int(8000 * min(1.0, i / fade, (n - i) / fade) * math.sin(2 * math.pi * freq * i / OUT_RATE)))
                               for i in range(n))
                sess.max_gap = sess.max_send = 0.0
                sp._begin()
                sp.emit_pcm(pcm)
                sp.end()
            threading.Thread(target=_tone, daemon=True, name="xz-tone").start()
            done.append(f"tone {freq}Hz {secs}초 선행 {pre}프레임")
        if a.get("wake"):
            sess.asleep = True
            sess.touch()
            done.append("wake")
        return jsonify({"sent": done or ["(할 일이 없어요: emotion, pan/tilt, center, sleep, wake 중 하나를 붙이세요)"], "devices": len(live)})

    log.info("[xiaozhi] 스택찬 브리지 켜짐 - OTA: /xiaozhi/ota/?key=...  WS: /xiaozhi/v1/  (모드=%s, VAD=%s)",
             ("live→pipe" if LIVE_OUT_PIPE else "live") if _live_available() else "pipe", "webrtc" if webrtcvad else "없음")
    if not webrtcvad:
        log.error("[xiaozhi] webrtcvad 모듈이 없어 말 끝 감지가 동작하지 않습니다 (pip install webrtcvad)")
    return True


_SESSIONS = []           # 지금 연결된 기기들 (테스트 주소가 쓴다)
_SESSIONS_LOCK = threading.Lock()


def _which(name):
    from shutil import which
    return which(name)
