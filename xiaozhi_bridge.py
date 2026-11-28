"""
xiaozhi_bridge.py - M5Stack 스택찬(xiaozhi 프로토콜) <-> token_server.py의 /pipe 모드 브리지

스택찬 펌웨어(xiaozhi 계열)는 서버와 두 가지로 통신한다.
  1) OTA 주소(POST/GET)  : 부팅 때 한 번. 응답에 '음성 WebSocket 주소'가 들어 있다.
  2) WebSocket           : JSON 제어 메시지(hello/listen/abort/tts/stt/llm) + Opus 오디오 프레임(바이너리)

이 모듈은 위 두 문을 token_server.py(Flask) 안에 달고, 한 턴을 이렇게 처리한다.
  기기 Opus(16kHz) -> PCM -> (서버 VAD로 말 끝 감지) -> WAV
  -> /api/pipe/chat (Gemini가 음성을 직접 듣고 대답, 기억/주식/타로 함수 그대로)
  -> 문장 단위로 /api/tts (타입캐스트)
  -> 24kHz PCM -> Opus 60ms 프레임 -> 실시간 속도로 기기에 전송

taeyeon-pipe.html이 브라우저에서 하던 일(문장 자르기, TTS 병렬 요청, 순서대로 재생,
음성 재생)을 서버 안에서 똑같이 한다. 라우트는 서버 안에서 직접 호출하므로
(Flask test_client) 별도 네트워크 왕복이 없고, 기존 로그인(GOOGLE_CLIENT_ID) 설정도 그대로 통과한다.

입력/출력 방식 (기본: 입력 = Gemini Live, 출력 = pipe):
  기기 마이크 -> Gemini Live (듣기/말 끝 감지/받아쓰기/생각/함수 호출) -> 대답 '글자'(전사)만 받아서
  -> 문장 단위로 /api/tts (타입캐스트) -> 24kHz PCM -> Opus -> 기기.  Live가 만든 목소리는 버린다.
  호출어 없이 늘 대화한다 (말소리가 들리면 바로 대답). 서버는 호출어를 판단하지 않는다:
  연결은 기기가 호출어/터치로 깨울 때만 생기고, 대화가 끝나면(작별 인사 또는 일정 시간 무활동) 서버가 연결을 닫는다.
  XIAOZHI_MODE=pipe(기본) = 위 방식 / XIAOZHI_MODE=live = 입력, 출력 모두 Live(Live 목소리 그대로).
  live 모드에서는 TTS(타입캐스트)를 전혀 쓰지 않는다: 대화 중 첫 소리, 대기 전 작별 인사, 웹 화면에서 보낸 글 읽기 모두 Live 목소리로 나간다.
  (Live 연결이 처음부터 계속 실패해 pipe 입력으로 되돌아가는 비상 경로에서만 예외적으로 TTS를 쓴다)
  (Live 연결이 처음부터 계속 실패할 때만 예전 pipe 입력 방식으로 되돌아간다)
  XIAOZHI_INPUT=pipe 이면 Live를 아예 쓰지 않고 gemini-3.5-flash-lite(/api/pipe/chat)만으로 대화한다 (토큰 비용 최소, 첫 소리는 느려짐).

받아쓰기: Live가 해 주는 받아쓰기는 한국어를 엉뚱하게(중국어 등) 적을 때가 있어서, 같은 소리를 한국어 전용 전사 모델
(models/gemini-3.5-transcribe-live, ko-KR)에도 나란히 보내 그 결과를 화면 표시/대화 기록에 우선 쓴다.
대답을 만드는 건 여전히 Live(소리를 직접 듣는다)다. XIAOZHI_STT=0 이면 한국어 전용 받아쓰기를 끈다.
XIAOZHI_STT_TEXT=1 이면 (pipe 출력일 때) 대화 중 소리는 Live로 보내지 않고, 한국어 받아쓰기 '글자'만 Live에 넘긴다.
받아쓰기가 죽었거나 시간 안에 결과가 없으면 그 말의 소리를 Live로 대신 보낸다(대체 경로).

켜는 법: 환경변수 XIAOZHI_KEY(긴 임의 문자열)를 설정하면 켜진다. 비어 있으면 아무 라우트도 열지 않는다.
  기기의 Custom OTA URL:  https://<railway도메인>/xiaozhi/ota/?key=<XIAOZHI_KEY>
"""
import array
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
import urllib.parse
import urllib.request
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
def _env_gain(name, default=1.0):
    try:
        return max(0.0, min(2.0, float(_env(name, str(default)))))
    except ValueError:
        return default
XZ_OUT_GAIN = _env_gain("XIAOZHI_OUT_GAIN")               # 기기로 보내는 소리 배율 (1.0=그대로, 0.4=작게). 기기 볼륨은 최대로 두고 여기서 줄인다
MAX_UTT_S = 30
STICK_MUTE_MAX_S = float(_env("XIAOZHI_STICK_MUTE_MAX_S", "20") or 20)         # [XIAOZHI_STICK_MUTE_MAX_S] M5Stick mute 뒤 unmute가 안 오면 이만큼(초) 뒤 자동으로 마이크 복귀 (Stick의 최대 녹음 시간보다 길게)
STICK_UNMUTE_DELAY_S = float(_env("XIAOZHI_STICK_UNMUTE_DELAY_S", "0.3") or 0.3)   # [XIAOZHI_STICK_UNMUTE_DELAY_S] unmute 뒤에도 이만큼(초) 더 듣지 않는다 (말끝 잔향이 스택챈에 들어가지 않게)
END_SILENCE_MS = int(_env("XIAOZHI_END_SILENCE_MS", "900") or 900)                   # [XIAOZHI_END_SILENCE_MS] (pipe 입력) 이만큼 조용하면 말이 끝난 것. 말 중간에 쉬는 틈에서 끊겨 받아쓰기가 두 토막 나면 1200~1500으로 올린다 (대답은 그만큼 늦어짐)
PIPE_PREROLL_MS = max(300, min(2000, int(_env("XIAOZHI_PIPE_PREROLL_MS", "600") or 600)))   # [XIAOZHI_PIPE_PREROLL_MS] (pipe 입력) 말소리를 감지한 순간보다 이만큼 앞의 소리부터 받아쓰기에 넣는다 (첫 음절이 잘려 받아쓰기가 틀릴 때 올린다. 예전 고정값 300)
VAD_MODE = int(_env("XIAOZHI_VAD_MODE", "1") or 1)                                   # [XIAOZHI_VAD_MODE] webrtcvad 강도 0~3 (낮을수록 작은 소리도 말로 인정, 높을수록 잡음에 둔함)
MIN_SPEECH_MS = int(_env("XIAOZHI_MIN_SPEECH_MS", "300") or 300)                     # [XIAOZHI_MIN_SPEECH_MS] (예전 파이프 방식) 이보다 짧은 소리는 잡음으로 버림
MIN_RMS = int(_env("XIAOZHI_MIN_RMS", "200") or 200)                                # [XIAOZHI_MIN_RMS] 증폭(MIC_GAIN) 뒤 소리 크기가 이보다 작으면 말로 치지 않음 (낮을수록 민감)
OUT_RATE = 24000                                          # /api/tts 출력 = 24kHz 16bit mono PCM
OUT_FRAME_MS = 60
OUT_FRAME_SAMPLES = OUT_RATE * OUT_FRAME_MS // 1000
PREBUFFER_MAX = max(8, min(40, int(_env("XIAOZHI_PREBUFFER_MAX", "36") or 36)))   # [XIAOZHI_PREBUFFER_MAX] 선전송량 상한(프레임). 기기 재생 큐가 이보다 작으면 넘친 프레임이 버려지니, 기기 큐 크기에 맞춰 낮춘다. 코드가 허용하는 최솟값은 8
PREBUFFER_FRAMES = max(8, min(PREBUFFER_MAX, int(_env("XIAOZHI_PREBUFFER_FRAMES", "8") or 8)))   # [XIAOZHI_PREBUFFER_FRAMES] 기기 큐에 미리 채워 두는 양(기본 8 = 최솟값). 올리면 서버 지연은 더 흡수하지만, 기기 큐 용량을 넘으면 프레임이 버려져 소리가 끊긴다. 로그의 '재생 비었던 횟수'가 1 이상일 때만 올려 본다
TTS_START_DELAY_S = max(0.0, min(1.0, float(_env("XIAOZHI_TTS_START_DELAY_S", "0.1") or 0.1)))   # [XIAOZHI_TTS_START_DELAY_S] tts start를 보낸 뒤 첫 소리 프레임을 보내기 전까지 두는 짧은 대기(초). 기기가 재생을 시작할 준비를 할 시간. 0이면 대기 없음
IDLE = True                                               # 대화가 없는 동안 가끔 고개를 움직인다
IDLE_MIN_S = 12                                           # 대기 중 동작 간격 (초, 최소~최대 사이 무작위)
IDLE_MAX_S = 35
SLEEP_AFTER_S = int(_env("XIAOZHI_SLEEP_AFTER_S", "180") or 180)                                       # (CONVO_IDLE_S의 예전 이름)
KEEP_CONNECTION = _env("XIAOZHI_KEEP_CONNECTION", "1").lower() not in ("0", "false", "no")      # 기기가 서버 연결을 계속 유지한다: 대화가 없어도 서버가 연결을 닫지 않고, 대화 중일 때만 무활동 시간을 잰다
CONVO_IDLE_S = int(_env("XIAOZHI_CONVO_IDLE_S", str(SLEEP_AFTER_S)) or SLEEP_AFTER_S)   # (사용 안 함) 서버 무활동 타이머는 없앴다   # 이만큼 대화가 없으면 작별 인사 후 연결을 닫는다 (예전 이름 XIAOZHI_SLEEP_AFTER_S도 같은 뜻으로 받는다)
CONVO_END_S = float(_env("XIAOZHI_CONVO_END_S", "0") or 0)      # [XIAOZHI_CONVO_END_S] 대화 중(듣기 상태)에 이만큼(초) 아무 말소리도 없으면 서버가 연결을 닫아 기기를 대기 모드로 보낸다 (기본 0 = 끔). 기기가 30초 타이머(마지막 음성 입력/출력이 끝난 뒤)로 listen stop을 보내 대기로 가므로 반드시 0(끔)으로 둘 것. 서버가 켜면 긴 대답 도중에 끊길 수 있다. 연결을 닫으면 기기가 자동 재연결하지 않아 다음 호출 때 3초쯤 걸린다
CONVO_END_FAREWELL = _env("XIAOZHI_CONVO_END_FAREWELL", "0").lower() in ("1", "true", "yes")   # 1이면 닫기 전에 SLEEP_FAREWELL 인사를 한다 (기본: 말없이 대기로)
IDLE_EMOTIONS = ["neutral", "happy", "relaxed", "winking"]      # 이 기기는 "thinking" 표정을 모른다 (Unknown emotion 경고)
TURN_MAX_S = 120                                          # 대답 생성/재생에서 이만큼 아무 진전이 없으면 멈춘 것으로 보고 풀어 준다 (먹통 방지)
MOTION = _env("XIAOZHI_MOTION", "1") != "0"   # XIAOZHI_MOTION=0 이면 고개 움직임 끔 (소리 끊김 원인 가려내기용)                                              # 고개 움직임 (self.robot.set_head_angles / center_head 사용)
FRONT_ON = _env("XIAOZHI_FACE_FRONT", "1") != "0"        # 0이면 대화 시작 때 고개를 정면으로 맞추는 동작을 끈다 (카메라가 화자를 향하게 하는 용도)
FRONT_PAN = int(_env("XIAOZHI_FRONT_PAN", "0") or 0)     # 정면으로 볼 때의 좌우 각도 (-70~70)
FRONT_TILT = int(_env("XIAOZHI_FRONT_TILT", "0") or 0)   # 정면으로 볼 때의 위아래 각도 (-35~35). 얼굴 높이에 맞게 조금 올리거나 내릴 때
MCP_ON = True
MAX_TURNS_KEPT = 40
MIN_FIRST, MIN_NEXT = 20, 70                               # taeyeon-pipe.html과 같은 문장 자르기 기준
XZ_TTS_TEMPO = max(0.5, min(2.0, float(_env("XIAOZHI_TTS_TEMPO", "1.0") or 1.0)))   # [XIAOZHI_TTS_TEMPO] 말하는 속도 배율 (1.0 = 기본, 0.9 = 10% 느리게, 1.1 = 10% 빠르게). 서버의 TYPECAST_TEMPO에 곱해진다 (예전 기본값: 1.1)
PIPE_FIRST_NOW = _env("XIAOZHI_PIPE_FIRST_NOW", "1") != "0"   # 1(기본) = 통째로 읽기에서도 첫 문장은 도착하자마자 바로 읽고, 나머지만 모아서 한 번에 읽는다 / 0 = 처음부터 끝까지 다 모았다가 읽는다
STRIP_EMO = _env("XIAOZHI_STRIP_EMO", "1") != "0"           # 1(기본) = 대답 글자 속 [sighs] 같은 감정 태그를 지우고, 서버가 키워드로 감정 목소리를 붙이는 것도 끈다 / 0 = 예전처럼
PIPE_WHOLE = _env("XIAOZHI_PIPE_WHOLE", "1") != "0"          # 1(기본) = 대답 글자를 끝까지 모았다가 한 번에 TTS로 합성해 읽는다 / 0 = 예전처럼 문장 단위로 잘라 바로바로 읽는다
WHOLE_MAX = 1800                                           # 한 번에 보낼 글자 상한 (서버 /api/tts의 타입캐스트 한도 2000자보다 조금 작게). 넘으면 문장 끝에서 나눈다
FAST_FIRST, FAST_NEXT, FAST_COMMA = 8, 24, 8               # Live 글자를 받아 읽을 때: 글자가 말하는 속도로 천천히 오니, 문장이 끝나는 대로 바로 읽는다
STOP_EXTRA_S = max(0.0, float(_env("XIAOZHI_STOP_EXTRA_S", "0.3") or 0.3))   # [XIAOZHI_STOP_EXTRA_S] 마지막 소리 재생이 끝난 뒤 이만큼(초) 더 기다렸다가 tts stop을 보낸다. 말끝이 잘리면 0.8~1.0으로 올려 본다

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


def _gain(pcm: bytes, g: float) -> bytes:
    """16bit PCM에 배율을 곱한다. 1.0이면 그대로. 오류가 나면 원본을 돌려준다."""
    if g == 1.0 or not pcm:
        return pcm
    try:
        from array import array
        a = array("h")
        a.frombytes(pcm[:len(pcm) - len(pcm) % 2])
        return array("h", (max(-32768, min(32767, int(x * g))) for x in a)).tobytes()
    except Exception:
        return pcm


def _wav16k(pcm: bytes) -> bytes:
    n = len(pcm)
    return (b"RIFF" + struct.pack("<I", 36 + n) + b"WAVEfmt " + struct.pack("<IHHIIHH", 16, 1, 1, 16000, 32000, 2, 16)
            + b"data" + struct.pack("<I", n) + pcm)


def _norm_text(t: str) -> str:
    """한글/영문/숫자만 남긴 소문자 글자 (말 비교용)."""
    return re.sub(r"[^0-9a-z가-힣]", "", (t or "").lower())


def _amplify(pcm: bytes, gain: float) -> bytes:
    """16bit PCM을 gain배로 키운다. 한 프레임 안에서 최대값이 넘치면 넘치지 않는 만큼만 키운다(최소 1배)."""
    if gain <= 1.0 or len(pcm) < 2:
        return pcm
    s = memoryview(pcm[:len(pcm) - len(pcm) % 2]).cast("h")
    peak = max(max(s), -min(s))
    if peak <= 0:
        return pcm
    g = max(1.0, min(gain, 32000.0 / peak))
    if g <= 1.0:
        return pcm
    return array.array("h", [int(x * g) for x in s]).tobytes()


def _rms(frame: bytes) -> float:
    s = memoryview(frame[:len(frame) - len(frame) % 2]).cast("h")
    return math.sqrt(sum(x * x for x in s) / len(s)) if len(s) else 0.0


def _pcm_stats(pcm: bytes):
    """16bit 16kHz PCM -> (길이 초, 최대 크기, 평균 크기(RMS), 찌그러진 샘플 비율 %).
    받아쓰기가 이상할 때 소리가 너무 작은지/찌그러졌는지 로그로 보려는 용도."""
    try:
        s = memoryview(pcm[:len(pcm) - len(pcm) % 2]).cast("h")
        if not len(s):
            return 0.0, 0, 0, 0.0
        peak = max(max(s), -min(s))
        rms = int(math.sqrt(sum(x * x for x in s) / len(s)))
        clip = sum(1 for x in s if x >= 32000 or x <= -32000) * 100.0 / len(s)
        return len(s) / 16000.0, peak, rms, clip
    except Exception:
        return 0.0, 0, 0, 0.0


_EMOJI = re.compile("[\U0001F000-\U0001FAFF\u2600-\u27BF\u2B00-\u2BFF\uFE0F\u200D]")
_TAG = re.compile(r"\[[^\[\]]{1,30}\]")


def _vis(s: str) -> str:
    """실제로 소리 나는 글자만 (감정 태그 [sighs] 등은 TTS 직전에 지워지므로 길이를 셀 때는 뺀다)."""
    return _TAG.sub("", s)


def _clean(t: str) -> str:
    t = _EMOJI.sub("", t)
    t = re.sub(r"[*_`#]+", "", t)
    return re.sub(r"\s+", " ", t).strip()


_CUT_RE = re.compile(r"[.!?~…。！？]+[\"'”’)\]]*(?=\s)|\n")


def _split_whole(s: str, limit: int = None) -> list:
    """통째로 읽기용: s가 limit자 이하면 그대로 한 조각, 넘으면 limit자 안쪽의 마지막 문장 끝(없으면 공백)에서 나눈다."""
    limit = limit or WHOLE_MAX
    out = []
    s = s.strip()
    while len(s) > limit:
        cut = 0
        for m in _CUT_RE.finditer(s[:limit]):
            cut = m.end()
        if cut < limit // 3:
            sp = s.rfind(" ", 0, limit)
            cut = sp if sp > limit // 3 else limit
        out.append(s[:cut].strip())
        s = s[cut:].strip()
    if s:
        out.append(s)
    return out


WHOLE_STAGE = int(_env("XIAOZHI_WHOLE_STAGE_CHARS", "100") or 100)   # [XIAOZHI_WHOLE_STAGE_CHARS] 통째로 읽기에서 첫 문장 뒤 나머지가 이보다 많이 길면 '앞 ~100자 + 나머지'로 나눠 앞쪽부터 읽는다 (긴 대답에서 첫 문장이 끝난 뒤 무음이 생기는 것을 막는다). 0이면 끔


def _split_staged(s: str) -> list:
    """통째로 읽기용: 나머지가 길면 첫 단계를 WHOLE_STAGE자 안팎(문장 끝)에서 끊어 먼저 합성/재생하고, 이후는 _split_whole로 나눈다."""
    s = s.strip()
    if WHOLE_STAGE <= 0 or len(_vis(s)) <= WHOLE_STAGE * 1.6:
        return _split_whole(s)
    cut = 0
    for m in _CUT_RE.finditer(s):
        if len(_vis(s[:m.end()]).strip()) >= WHOLE_STAGE:
            cut = m.end()
            break
    if cut <= 0 or len(_vis(s[cut:]).strip()) < 20:
        return _split_whole(s)
    return [s[:cut].strip()] + _split_whole(s[cut:].strip())


def _find_cut(s: str, first: bool, fast: bool = False) -> int:
    """taeyeon-pipe.html의 findCut과 같은 규칙: 첫 조각은 짧게(첫 소리 빨리), 이후는 3~4문장씩. fast면 문장 끝마다 거의 바로 자른다."""
    need = (FAST_FIRST if first else FAST_NEXT) if fast else (MIN_FIRST if first else MIN_NEXT)
    for m in _CUT_RE.finditer(s):
        if len(_vis(s[:m.end()]).strip()) >= need:      # 태그 글자는 세지 않는다 (예전엔 세어서 읽을 글자가 2~14자인데 잘렸다)
            return m.end()
    if first:
        m = re.search(r"[,，、](?=\s)", s)
        if m and len(_vis(s[:m.start()]).strip()) >= (FAST_COMMA if fast else 14):
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
        self.pre = deque(maxlen=max(15, PIPE_PREROLL_MS // 20))       # 말 시작 앞 PIPE_PREROLL_MS (첫 음절이 잘리지 않게)
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
    """기기는 받은 프레임을 바로 재생 큐에 쌓고(한도가 있어 넘치면 버림), 서버가 앞서 보내면 안 된다.
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
        self.fast_cut = False                   # Live 글자를 받아 읽는 Speaker는 True (문장 단위로 빨리 자른다)
        self.whole = PIPE_WHOLE                 # True면 feed()는 글자를 모으기만 하고, flush()에서 한 번에 합성한다
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
        if self.whole and not (PIPE_FIRST_NOW and self.sent == 0):
            return                              # 문장으로 자르지 않고 끝까지 모은다 (flush에서 한 번에 읽는다)
        while True:
            cut = _find_cut(self.buf, self.sent == 0, self.fast_cut)
            if cut <= 0:
                break
            piece = self.buf[:cut]
            if piece.count("[") != piece.count("]"):
                break
            self.buf = self.buf[cut:]
            self._speak(piece)
            if self.whole and self.sent > 0:
                break                           # 첫 문장만 바로 읽었다: 나머지는 모아서 flush에서 한 번에 읽는다

    def filler(self, text):      # '잠시만요' 같은 한마디: 버퍼에 갇히지 않게 바로 읽는다
        rest, self.buf = self.buf, ""
        if rest.strip():
            self._speak(rest)
        self._speak(text)
        self.sent = 0

    def flush(self):
        rest, self.buf = self.buf, ""
        if rest.strip():
            if self.whole:
                chain = None
                for piece in _split_staged(rest):       # 짧으면 한 조각, 길면 앞 단계(~100자)와 나머지로 나눈다
                    self._speak(piece, after=chain)
                    chain = getattr(self, "_last_fut", None)      # 다음 단계는 이 단계 합성이 끝난 뒤에 시작한다 (동시 요청이 늘어 429가 나지 않게)
            else:
                self._speak(rest)
        self.sent, self.prev, self.carry = 0, "", ""

    def _synth_after(self, after, text, prev):
        try:
            after.result(timeout=50)
        except Exception:
            pass
        if self.cancel.is_set():
            return b""
        return self.s.synth(text, prev)

    def _speak(self, raw, after=None):
        text = _clean(raw)
        if STRIP_EMO:
            text = re.sub(r"\s+", " ", _TAG.sub(" ", text)).strip()      # [sighs] 같은 감정 태그는 전부 지운다 (그래서 태그만 있는 조각은 아래에서 그냥 버려진다)
        if not text or not re.search(r"\w", _TAG.sub(" ", text)):
            if text and _TAG.search(text):        # 태그([sighs])만 있는 조각은 다음 조각 앞에 붙인다
                self.carry = (self.carry + " " + text).strip()
            return
        if self.carry:
            text, self.carry = self.carry + " " + text, ""
        prev, self.prev = self.prev, text
        self.sent += 1
        fut = _pool.submit(self._synth_after, after, text, prev) if after is not None else _pool.submit(self.s.synth, text, prev)
        self._last_fut = fut
        self.q.put((text, fut))

    # --- 소리 출력 ---
    def _begin(self):
        if not self.started:
            self.started = True
            self.s.send_json({"type": "tts", "state": "start"})
            self._start_t = time.monotonic()      # 첫 프레임 전 짧은 대기(TTS_START_DELAY_S)의 기준 시각

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
                # [CMD OFF - 2. 표정] self.s.send_json({"type": "llm", "emotion": emo, "text": ""})
            self.s.send_json({"type": "tts", "state": "sentence_start", "text": _TAG.sub("", text).strip()})
            self.s.motion_speak(emo or self.last_emo)
            self.emit_pcm(pcm)

    def emit_pcm(self, pcm: bytes):
        fb = OUT_FRAME_SAMPLES * 2
        if TTS_START_DELAY_S > 0 and not getattr(self, "_gap_done", False):
            self._gap_done = True               # 턴의 첫 소리에서만: tts start 직후 기기가 준비할 틈을 준다 (이미 지났으면 바로)
            left = TTS_START_DELAY_S - (time.monotonic() - getattr(self, "_start_t", 0.0))
            if left > 0:
                self.cancel.wait(min(left, TTS_START_DELAY_S))
        for off in range(0, len(pcm), fb):
            if self.cancel.is_set() or self.s.closed:
                return
            fr = pcm[off:off + fb]
            if len(fr) < fb:
                fr += b"\0" * (fb - len(fr))
            opus = self.enc.encode(_gain(fr, XZ_OUT_GAIN), OUT_FRAME_SAMPLES)
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
            log.info("[xiaozhi] tts stop 전 재생 끝 대기 %.2fs (여유 %.2fs 포함, 재생한 프레임 %d)", max(left, 0.0), STOP_EXTRA_S, getattr(self.pacer, "n", 0))
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
LIVE_SILENCE_MS = int(_env("XIAOZHI_LIVE_SILENCE_MS", "900") or 900)               # [XIAOZHI_LIVE_SILENCE_MS] Live 서버가 '말이 끝났다'고 보는 조용한 시간
LIVE_OPEN_MS = int(_env("XIAOZHI_LIVE_MIN_SPEECH_MS", "240") or 240)   # 대화 중: 이만큼 말소리가 모여야 Live로 보내기 시작 (pipe의 MIN_SPEECH_MS처럼 짧은 소음은 거름)
LIVE_HANGOVER_MS = int(_env("XIAOZHI_LIVE_HANGOVER_MS", "1800") or 1800)           # [XIAOZHI_LIVE_HANGOVER_MS] 대화 중: 마지막 말소리 뒤로 이만큼은 조용한 소리도 계속 보낸다 (말 사이 쉬는 틈을 이어 붙임)
SLEEP_FAREWELL = _env("XIAOZHI_SLEEP_FAREWELL", "대화가 없어서 잠시 나갈게요. 필요하면 또 불러 주세요!")      # 대화가 없어서 연결을 닫기 직전에 하는 말 (비우면 말없이 닫음)
LIVE_THINKING = (_env("XIAOZHI_LIVE_THINKING", "") or "").strip().lower()      # [XIAOZHI_LIVE_THINKING] Gemini Live의 thinking 수준 (minimal/low/medium/high). 비우면(기본) 설정을 안 보내고 모델 기본값을 쓴다
if LIVE_THINKING in ("off", "none", "0", "default"):
    LIVE_THINKING = ""
MIC_GAIN = float(_env("XIAOZHI_MIC_GAIN", "2.0") or 2.0)                   # 기기 마이크 소리를 이 배수로 키워서 듣는다 (작게 말해도 알아듣게). 1이면 끔. 소리가 찢어지지 않게 큰 소리는 자동으로 덜 키운다
LIVE_PREROLL_MS = int(_env("XIAOZHI_PREROLL_MS", "1200") or 1200)         # 대화 중 말소리를 감지한 순간보다 이만큼 앞의 소리부터 Live로 보낸다 (첫 단어가 잘리지 않게. 예전 600ms)
LIVE_FAST_CUT = _env("XIAOZHI_LIVE_FAST_CUT", "0") == "1"      # [XIAOZHI_LIVE_FAST_CUT] 1이면 Live 글자를 8자부터 잘게 잘라 읽는다(예전 방식). 기본 0 = pipe 입력과 똑같은 문장 자르기(첫 조각 20자~, 이후 모아서 읽기)
LIVE_TAIL_MUTE_S = float(_env("XIAOZHI_TAIL_MUTE_S", "0.5") or 0.5)                # [XIAOZHI_TAIL_MUTE_S] 대답이 끝난 뒤 스피커 잔향을 말로 오인하지 않게 이만큼 듣지 않는다 (줄이면 대답 직후 바로 말해도 받음)
LIVE_GAIN = max(0.1, min(4.0, float(_env("XIAOZHI_LIVE_GAIN", "1.0") or 1.0)))   # [XIAOZHI_LIVE_GAIN] Live/한국어 받아쓰기로 보내기 직전에 한 번 더 키우는 배수 (예전 고정값 1.8). 기본 1.0 = 안 키움. XIAOZHI_MIC_GAIN(2.0)과 곱해지고 이쪽은 넘치면 그냥 잘라내므로, 올릴수록 잡음이 커지고 큰 소리는 찌그러진다
LIVE_CONNECT_FAILS_MAX = 3                                # 처음부터 연속으로 이만큼 연결에 실패하면 파이프 모드로 되돌린다
LIVE_CLIENT = None
# 출력 방식은 XIAOZHI_MODE로 정한다 (입력은 두 경우 모두 Live):
#   pipe = Live가 만든 목소리는 버리고, 대답 글자(전사)를 문장마다 /api/tts(타입캐스트)로 읽는다
#   live = Live가 만든 목소리를 그대로 기기로 보낸다
LIVE_OUT_PIPE = XZ_MODE != "live"
LIVE_TEXT = _env("XIAOZHI_LIVE_TEXT", "0") == "1"                 # [실험] 1 = pipe 출력일 때 Live에게 소리 없이 글자(TEXT)만 받는다 (쓰지도 않는 Live 목소리를 만드는 속도에 글자가 묶이지 않게). 모델이 TEXT를 지원하지 않아 연결이 2번 실패하면 자동으로 예전(AUDIO+받아쓰기) 방식으로 돌아간다
STT_ON = _env("XIAOZHI_STT", "1") != "0"                  # 한국어 전용 받아쓰기(별도 전사 모델)를 같이 돌린다. 0이면 Live가 해 주는 받아쓰기만 쓴다
LIVE_IN_STT = _env("XIAOZHI_LIVE_IN_STT", "0") == "1"      # [XIAOZHI_LIVE_IN_STT] 1 = Live 내장 입력 받아쓰기도 켠다(예전 방식, 받아쓰기 2번). 기본 0 = pipe 출력 + 한국어 받아쓰기가 살아 있을 때는 Live 내장 받아쓰기를 끈다. live 출력 모드/한국어 받아쓰기 꺼짐·죽음일 때는 자동으로 켜진다
STT_MODEL_DEFAULT = "models/gemini-3.5-transcribe-live"   # 서버(/api/live/setup)가 모델을 알려 주면 그걸 쓴다
STT_TEXT = _env("XIAOZHI_STT_TEXT", "0") == "1"           # [XIAOZHI_STT_TEXT] 1 = 대화 중 소리 대신 한국어 받아쓰기 글자를 Live에 넘긴다 (pipe 출력 + XIAOZHI_STT=1 일 때만). 기본 0(끔)
STT_TEXT_SETTLE_S = float(_env("XIAOZHI_STT_TEXT_SETTLE_S", "") or (LIVE_SILENCE_MS / 1000.0))   # [XIAOZHI_STT_TEXT_SETTLE_S] 말하는 도중, 새 글자가 이만큼(초) 안 오면 '말이 끝났다'고 보고 Live에 보낸다
STT_TEXT_CLOSED_S = 0.4                                   # 마이크 문이 닫힌 뒤에는 이만큼만 더 기다렸다가 보낸다
STT_TEXT_WAIT_S = float(_env("XIAOZHI_STT_TEXT_WAIT_S", "2.0") or 2.0)   # [XIAOZHI_STT_TEXT_WAIT_S] 말이 끝났는데 받아쓰기 글자가 이만큼(초) 동안 하나도 없으면 소리를 Live로 대신 보낸다
STT_TEXT_API = (_env("XIAOZHI_STT_TEXT_API", "realtime") or "realtime").strip().lower()   # [XIAOZHI_STT_TEXT_API] 글자를 Live에 넣는 방법: realtime(send_realtime_input) / content(send_client_content). 모델이 한쪽만 받으면 바꿔 본다
STT_TEXT_MISS_MAX = 3                                     # 연달아 이만큼 받아쓰기 결과가 없으면 STT_TEXT_OFF_S 동안은 예전처럼 소리를 Live로 보낸다
STT_TEXT_OFF_S = 120.0
STT_FAILS_MAX = 3                                         # 처음부터 연속으로 이만큼 연결에 실패하면 한국어 받아쓰기는 포기하고 Live 받아쓰기로 간다
THINK_EMOTION = _env("XIAOZHI_THINK_EMOTION", "neutral") or "neutral"      # 대답을 기다리는 동안 보내는 표정 (기기가 아는 이름이어야 한다)
_mw = _env("XIAOZHI_MIC_WATCHDOG_S")
MIC_WATCHDOG_S = 8.0 if _mw in (None, "") else float(_mw)                  # [XIAOZHI_MIC_WATCHDOG_S] 대답(tts stop)이 끝난 뒤 기기 마이크 소리가 이만큼(초) 안 오면 서버가 먼저 연결을 닫아 기기가 Auto listen으로 다시 붙게 한다 (기본 8, 0이면 끔). 푸시투토크(manual)에서는 동작하지 않는다
RESUME_WINDOW_S = float(_env("XIAOZHI_RESUME_WINDOW_S", "90") or 90)      # 이 안에 같은 기기가 다시 연결되면 직전 대화 기록을 이어받는다
_RESUME = {}                                              # device_id -> 직전 연결이 끝날 때의 상태 (재연결 시 이어받기)
STT_VOCAB = [x.strip() for x in (_env("XIAOZHI_STT_VOCAB") or "쎄리,세리,쎄리야,세리야,안녕 쎄리,안녕 세리").split(",") if x.strip()]      # 받아쓰기가 이 말들로 알아듣게 힌트를 준다 (custom_vocabulary). 비우면 끔
LIVE_START_SENS = (_env("XIAOZHI_LIVE_START_SENS", "high") or "high").strip().upper()   # [XIAOZHI_LIVE_START_SENS] Gemini Live가 말 시작을 알아채는 민감도: HIGH(기본) / LOW
LIVE_END_SENS = (_env("XIAOZHI_LIVE_END_SENS", "low") or "low").strip().upper()         # [XIAOZHI_LIVE_END_SENS] Gemini Live가 말 끝을 알아채는 민감도: LOW(기본, 말 사이 쉬어도 안 끊음) / HIGH(빨리 끊음)
# --- 화자(가족 목소리) 확인: stick_relay의 /identify에 물어서, 등록된 목소리가 아니면(TV 등) 버린다 ---
# [화자 확인 임시 끔] 아래 원래 줄을 주석 처리하고 빈 값으로 고정. 다시 켜려면 아래 줄을 지우고 이 주석을 풀 것
# SPEAKER_URL = (_env("XIAOZHI_SPEAKER_URL") or "").strip().rstrip("/")                 # 예: https://내-릴레이.up.railway.app  (비우면 이 기능 전체 꺼짐)
SPEAKER_URL = ""
SPEAKER_TOKEN = (_env("XIAOZHI_SPEAKER_TOKEN") or "").strip()                         # 릴레이의 DEVICE_TOKEN
SPEAKER_SCOPE = (_env("XIAOZHI_SPEAKER_SCOPE", "both") or "both").strip().lower()    # convo(대화 중 말). wake/both는 예전 값 (호출어 판정이 없어져 convo만 남았다)
_thr = (_env("XIAOZHI_SPEAKER_THRESHOLD") or "").strip()
SPEAKER_THR = float(_thr) if _thr else None                                          # 비우면 릴레이의 판정 기준(SPEAKER_THRESHOLD)을 그대로 쓴다
SPEAKER_VERIFY_MS = int(_env("XIAOZHI_SPEAKER_VERIFY_MS", "1000") or 1000)           # 대화 중: 말을 이만큼 모은 뒤 판정 (길수록 정확, 반응은 그만큼 늦어짐)
SPEAKER_TIMEOUT_S = float(_env("XIAOZHI_SPEAKER_TIMEOUT_S", "2.0") or 2.0)           # 릴레이가 이보다 늦으면 판정 없이 통과시킨다
SPEAKER_SHORT_DROP = _env("XIAOZHI_SPEAKER_SHORT", "pass") == "drop"                 # 판정하기엔 너무 짧은 말: pass(기본, 통과) / drop(버림)
SPK_ON_CONVO = bool(SPEAKER_URL) and SPEAKER_SCOPE in ("convo", "both")
_SPK_POOL = ThreadPoolExecutor(max_workers=2, thread_name_prefix="xz-spk")
_spk_off_until = 0.0                                                                  # 릴레이에 등록된 목소리가 없거나 엔진이 죽었으면 잠시 묻지 않는다


def _speaker_check(pcm: bytes):
    """16kHz PCM16 -> (True=등록된 목소리 / False=아님 / None=판정 못 함(통과시킬 것), 이름, 점수)"""
    global _spk_off_until
    if not SPEAKER_URL or time.monotonic() < _spk_off_until:
        return None, None, None
    try:
        url = f"{SPEAKER_URL}/identify?token={urllib.parse.quote(SPEAKER_TOKEN, safe='')}"
        req = urllib.request.Request(url, data=pcm, method="POST", headers={"Content-Type": "application/octet-stream"})
        with urllib.request.urlopen(req, timeout=SPEAKER_TIMEOUT_S) as r:
            d = json.loads(r.read().decode("utf-8"))
        if not d.get("ok"):
            if d.get("reason") in ("no_voices", "engine", "off"):
                _spk_off_until = time.monotonic() + 60
                log.warning("[xiaozhi] 화자 확인 건너뜀 (릴레이 응답: %s) - 60초 동안 묻지 않고 모두 통과", d.get("reason"))
            return None, None, None
        score = float(d.get("score"))
        ok = (score >= SPEAKER_THR) if SPEAKER_THR is not None else bool(d.get("match"))
        return ok, d.get("name"), score
    except Exception as e:
        log.warning("[xiaozhi] 화자 확인 실패 - 판정 없이 통과 (%s: %s)", type(e).__name__, str(e)[:120])
        return None, None, None


LIVE_NO_REPLY_S = float(_env("XIAOZHI_LIVE_NO_REPLY_S", "8") or 8)       # 말소리 2번을 보냈는데 Live가 이만큼 아무 반응이 없으면 Live 연결이 멈춘 것으로 보고 새로 연결한다 (0이면 끔)
KEEPALIVE_S = 20                                          # 조용한 동안에도 이만큼마다 기기에 가벼운 신호를 보낸다 (서버에서 오는 게 한참 없으면 기기가 연결을 닫고 대기로 갈 수 있어서)
LIVE_TEXT_TAIL_S = 0.6                                    # 턴이 끝난 뒤에도 마지막 대답 글자가 조금 늦게 오는 일이 있어서, 이만큼 더 기다렸다가 마무리한다


def _live_client():
    global LIVE_CLIENT
    if LIVE_CLIENT is None:
        from google import genai
        LIVE_CLIENT = genai.Client(api_key=_env("GEMINI_API_KEY"), http_options={"api_version": "v1beta"})
    return LIVE_CLIENT


# 입력 방식: live(기본) = 기기 마이크를 Gemini Live로 보낸다 / pipe = Live를 쓰지 않고 gemini-3.5-flash-lite(/api/pipe/chat)만으로 대화한다 (토큰 비용 최소, 대신 첫 소리까지 느림)
INPUT_MODE = (_env("XIAOZHI_INPUT", "live") or "live").strip().lower()
PIPE_ONLY = INPUT_MODE == "pipe"

STT_CLIENT = None


def _stt_client():
    global STT_CLIENT
    if STT_CLIENT is None:
        from google import genai
        STT_CLIENT = genai.Client(api_key=_env("GEMINI_API_KEY"), http_options={"api_version": "v1alpha"})
    return STT_CLIENT


def _live_available() -> bool:
    if PIPE_ONLY:                 # XIAOZHI_INPUT=pipe: Live를 쓰지 않고 예전 pipe 입력 방식(flash-lite만)으로 간다
        return False
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
        self.pre = deque(maxlen=max(30, LIVE_PREROLL_MS // 20))
        self.recent = deque(maxlen=30)
        self.open = False
        self.voiced_ms = 0
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
                # 최근 0.6초 안에 말소리가 LIVE_OPEN_MS 이상 모여야 연다 (잡음/TV 소리 거름)
                opened = sum(self.recent) * 20 >= LIVE_OPEN_MS
                if opened:
                    self.open, self.quiet_ms = True, 0
                    pre = list(self.pre)
                    out += b"".join(pre)
                    self.sent_ms = len(pre) * 20
                    self.voiced_ms = sum(self.recent) * 20
                    self.pre.clear()
                    log.info("[xiaozhi] 말소리 감지 -> Live로 보내기 시작 (말소리 %dms)", self.voiced_ms)
            else:
                out += fr
                self.sent_ms += 20
                if v:
                    self.voiced_ms += 20
                self.quiet_ms = 0 if v else self.quiet_ms + 20
                if self.quiet_ms >= LIVE_HANGOVER_MS:
                    log.info("[xiaozhi] 말소리 끝 -> Live로 보낸 소리 %.1f초 (조용한 %.1f초 포함, 말소리 %dms)", self.sent_ms / 1000, self.quiet_ms / 1000, self.voiced_ms)
                    self.open = False
                    self.recent.clear()
        return bytes(out)


class LiveSpeaker(Speaker):
    """Speaker에서 문장 자르기/TTS 합성 부분은 빼고, 소리 내보내기(Opus 인코딩, 속도 맞추기, tts start/stop, 부저)만 쓴다."""

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
        if LIVE_OUT_PIPE:
            self.speaker.fast_cut = LIVE_FAST_CUT      # 기본 False: pipe 입력의 Speaker와 같은 설정
        self.done = False               # Live가 턴 끝을 알려 왔다 (pipe 출력: 늦게 오는 글자를 기다리는 중)
        self.fin = None                 # 마무리 예약 (loop.call_later 핸들)
        self.rem = b""                  # 아직 60ms 프레임으로 못 채운 소리 조각
        self.otext = ""                 # 대답 글자(전사)
        self.obuf = ""                  # 아직 문장으로 못 자른 대답 글자
        self.nsent = 0
        self.meta = False               # 서버가 시켜서 하는 말(작별 인사, 웹 글 읽기): 대화 기록에 남기지 않는다
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
        self.pending_ends = []                  # Live에 보냈는데 아직 아무 반응(받아쓰기/대답)이 없는 말의 끝 시각들
        self.last_stuck_t = 0.0                 # 마지막으로 '멈춤'으로 보고 재연결한 때 (연달아 재연결 방지)
        self._stuck_close = False               # 우리가 직접 닫은 연결인가 (정상 종료 코드 1000을 오류로 세지 않으려고)
        self.cur_session = None
        self.setup = None
        self.fails = 0
        self.ever_ready = False
        self.main_task = None
        self.turn = None
        self.utext = ""
        self.gen_active = False
        self.discard = False
        self.want_reconnect = False
        self.thought_sent = False
        self.stt_q = None                       # 한국어 받아쓰기 모델로 보낼 소리
        self.stt_text = ""                      # 한국어 받아쓰기 결과 (있으면 Live 받아쓰기보다 우선)
        self.stt_task = None
        self.stt_dead = not STT_ON
        self.in_stt_on = True                   # 이번 Live 연결에서 Live 내장 입력 받아쓰기를 켰는지 (_build_config가 정한다)
        self.stt_ever = False
        self.stt_fails = 0
        self.stt_connected = False              # 한국어 받아쓰기 연결이 지금 살아 있나
        self.utt_text = False                   # 지금 말은 '글자로 넘기는 방식'인가 (말이 시작될 때 정해 말이 끝날 때까지 유지)
        self.utt_pcm = bytearray()              # 이번 말의 소리 (받아쓰기가 실패하면 Live로 대신 보내려고 모아 둔다)
        self.utt_closed = False                 # 이번 말의 마이크 문이 닫혔다
        self.utt_any = False                    # 이번 말에서 받아쓰기 글자가 한 번이라도 왔다
        self.utt_voiced = 0                     # 이번 말의 말소리 길이(ms)
        self.pend_text = ""                     # 받아썼지만 아직 Live로 안 보낸 글자
        self.txt_timer = None
        self.txt_miss = 0
        self.txt_off_until = 0.0
        self.meta_pending = 0.0                 # 서버가 글자로 시킨 말(say_text)을 보낸 시각 (0이면 없음)
        self.after_turn = None                  # say_text의 대답이 끝나면(True) 또는 끊기면(False) 부를 함수
        threading.Thread(target=self._run, daemon=True, name="xz-live").start()
        threading.Thread(target=self._out_worker, daemon=True, name="xz-live-out").start()

    # ---------- 바깥(동기 스레드)에서 부르는 함수 ----------
    def feed(self, pcm: bytes):
        if self.dead or self.in_q is None or not pcm:
            return
        pcm = _apply_gain(pcm, LIVE_GAIN)      # 연결 전/재연결 중에 들어온 소리도 쌓아 뒀다가 연결되면 보낸다 (8초 넘은 것은 버림)
        now = time.monotonic()
        self.loop.call_soon_threadsafe(self._feed_conv, pcm, now)

    def _feed_conv(self, pcm, now):
        if self.utt_text:                            # 글자로 넘기는 말: 소리는 받아쓰기로만 보내고, 실패할 때를 위해 모아 둔다
            self.utt_pcm += pcm
            del self.utt_pcm[:-32000 * 30]           # 최근 30초만
            self._put_stt(("audio", pcm, now))
            return
        self._put(("audio", pcm, now))
        if not self.stt_dead and LIVE_OUT_PIPE:      # Live 전용(XIAOZHI_MODE=live)에서는 대화 중 소리를 별도 받아쓰기로 보내지 않는다
            self._put_stt(("audio", pcm, now))

    def stream_end(self):
        """대화 중 한 마디가 끝나 마이크 문이 닫혔다: Live에 소리 스트림이 멈췄음을 알려 남은 소리를 처리하게 한다."""
        if self.dead or self.in_q is None:
            return
        self.loop.call_soon_threadsafe(self._stream_end_conv)

    def _stream_end_conv(self):
        if self.utt_text:
            self._text_utt_closed()
            return
        self._put(("end", None, time.monotonic()))

    def _put_stt(self, item):
        q = self.stt_q
        if q is None:
            return
        try:
            q.put_nowait(item)
        except self.asyncio.QueueFull:
            try:
                q.get_nowait()
                q.put_nowait(item)
            except Exception:
                pass

    def new_utterance(self):
        """새로 말이 시작됐다(마이크 문이 열렸다): 지난 말의 한국어 받아쓰기 결과를 비운다."""
        self.loop.call_soon_threadsafe(self._reset_stt)

    def _reset_stt(self):
        if self.utt_text:                         # 지난 말의 글자/소리가 아직 Live로 안 갔으면 먼저 처리한다
            if self.pend_text.strip():
                self._text_send()
            elif not self.utt_any and self.utt_closed:
                self._text_fallback()
        self._cancel_txt_timer()
        self.stt_text = ""
        self.pend_text = ""
        self.utt_pcm = bytearray()
        self.utt_closed = False
        self.utt_any = False
        self.utt_text = self._text_ok()

    # ---------- 한국어 받아쓰기 글자를 Live로 넘기는 방식 (XIAOZHI_STT_TEXT=1) ----------
    def _text_ok(self) -> bool:
        return bool(STT_TEXT and LIVE_OUT_PIPE and STT_ON and not self.dead and not self.stt_dead
                    and self.stt_connected and time.monotonic() >= self.txt_off_until)

    def _cancel_txt_timer(self):
        h = self.txt_timer
        self.txt_timer = None
        if h is not None:
            h.cancel()

    def _arm_txt_timer(self, delay):
        self._cancel_txt_timer()
        self.txt_timer = self.loop.call_later(delay, self._txt_timer_fire)

    def _text_utt_closed(self):
        """마이크 문이 닫혔다: 받아쓰기에 말 끝을 알려 결과를 빨리 확정하게 하고, 글자가 올 때까지(또는 포기할 때까지) 기다린다."""
        self.utt_closed = True
        now = time.monotonic()
        self._put_stt(("audio", b"\0" * 16000, now))
        self._put_stt(("end", None, now))
        if self.pend_text.strip():
            self._arm_txt_timer(STT_TEXT_CLOSED_S)
        elif not self.utt_any:
            self._arm_txt_timer(STT_TEXT_WAIT_S)

    def _txt_timer_fire(self):
        self.txt_timer = None
        if not self.utt_text:
            return
        if self.pend_text.strip():
            self._text_send()
        elif not self.utt_any and self.utt_closed:
            self._text_fallback()

    def _text_send(self):
        text = " ".join(self.pend_text.split())
        self.pend_text = ""
        if len(_norm_text(text)) < 2:             # 잡음이 한두 글자로 받아써진 것은 보내지 않는다
            return
        now = time.monotonic()
        self.txt_miss = 0
        self.pending_ends.append(now)
        self._put(("text", text, now))
        log.info("[xiaozhi] 한국어 받아쓰기 글자를 Live로 보냄: %r", text[:60])

    def _text_fallback(self):
        """받아쓰기 글자가 끝내 안 왔다: 말소리가 충분했다면 모아 둔 소리를 Live로 대신 보낸다. 잡음이면 버린다."""
        pcm, self.utt_pcm = bytes(self.utt_pcm), bytearray()
        self.utt_text = False
        if self.utt_voiced < 500 or len(pcm) < 16000:
            log.info("[xiaozhi] 받아쓰기 글자 없음 - 짧은 소리(%dms)라 잡음으로 보고 버립니다", self.utt_voiced)
            return
        self.txt_miss += 1
        log.warning("[xiaozhi] 한국어 받아쓰기 글자가 %.1fs 안에 안 와서 소리 %.1f초를 Live로 대신 보냅니다 (연속 %d회)",
                    STT_TEXT_WAIT_S, len(pcm) / 32000, self.txt_miss)
        if self.txt_miss >= STT_TEXT_MISS_MAX:
            self.txt_off_until = time.monotonic() + STT_TEXT_OFF_S
            self.txt_miss = 0
            log.warning("[xiaozhi] 받아쓰기 결과가 계속 없어 %.0f초 동안은 소리를 Live로 직접 보냅니다", STT_TEXT_OFF_S)
        now = time.monotonic()
        for i in range(0, len(pcm), 32000):
            self._put(("audio", pcm[i:i + 32000], now))
        self.pending_ends.append(now)
        self._put(("audio", b"\0" * 32000, now))
        self._put(("end", None, now))

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
            if not self.stt_dead:
                self.loop.call_soon_threadsafe(self._put_stt, ("audio", b"\0" * 32000, now))
                self.loop.call_soon_threadsafe(self._put_stt, ("end", None, now))

    def say_text(self, prompt: str, on_done=None):
        """(live 출력) 서버가 정한 말을 Live 목소리로 시킨다: 글자를 Live에 넣으면 Live가 소리로 말한다. TTS를 쓰지 않는다.
        on_done(ok): 말이 끝나면 True, 사용자가 끊었으면 False. 대화 기록에는 남기지 않는다."""
        if self.dead or self.in_q is None:
            return False
        self.loop.call_soon_threadsafe(self._say_text, prompt, on_done)
        return True

    def _say_text(self, prompt, on_done):
        self.meta_pending = time.monotonic()      # 이 시각 뒤 15초 안에 시작되는 대답만 '서버가 시킨 말'로 본다 (Live가 반응 없으면 다음 진짜 대화를 잘못 숨기지 않게)
        self.after_turn = on_done
        self._put(("text", prompt, time.monotonic()))

    def cancel_say(self):
        """say_text로 시킨 말이 시작도 못 하고 포기됐다: 예약을 없앤다."""
        self.meta_pending = False
        self.after_turn = None

    def _fire_after(self, ok: bool):
        cb, self.after_turn = self.after_turn, None
        if cb is not None:
            try:
                cb(ok)
            except Exception:
                log.exception("[xiaozhi] 말 끝 처리 실패")

    def interrupt(self):
        """기기가 abort/listen start를 보냈다: 말하던 것을 멈추고, 이미 만들어지는 중인 대답의 남은 소리는 버린다."""
        t = self.turn
        if t is not None:
            t.cancel.set()
            if LIVE_OUT_PIPE:
                t.speaker.q.put(None)       # 합성/전송 스레드를 끝낸다
        if self.gen_active:
            self.discard = True
        self.turn = None
        self.meta_pending = False
        self._fire_after(False)
        while True:
            try:
                self.out_q.get_nowait()
            except queue.Empty:
                break

    def close(self):
        self.out_q.put(None)
        try:
            self.loop.call_soon_threadsafe(lambda: self.main_task and self.main_task.cancel())
            self.loop.call_soon_threadsafe(lambda: self.stt_task and self.stt_task.cancel())
        except Exception:
            pass

    # ---------- asyncio 쪽 ----------
    def _run(self):
        self.asyncio.set_event_loop(self.loop)
        self.in_q = self.asyncio.Queue(maxsize=400)
        self.stt_q = self.asyncio.Queue(maxsize=400)
        self.main_task = self.loop.create_task(self._main())
        if not self.stt_dead:
            self.stt_task = self.loop.create_task(self._stt_main())
        try:
            self.loop.run_until_complete(self.main_task)
        except BaseException:
            pass
        finally:
            try:
                if self.stt_task is not None:
                    self.stt_task.cancel()
                    self.loop.run_until_complete(self.asyncio.gather(self.stt_task, return_exceptions=True))
            except BaseException:
                pass
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
                if self._stuck_close:               # check_stuck이 직접 닫은 것: 실패로 세지 않고 바로 다시 연결
                    self._stuck_close = False
                    self.connected = False
                    log.info("[xiaozhi] Live 연결을 직접 닫았음 - 바로 다시 연결합니다")
                    continue
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
        body = {"mode": "pipe" if LIVE_OUT_PIPE else "live"}      # live면 서버가 TTS용 안내를 프롬프트에 넣지 않는다
        if STT_TEXT and LIVE_OUT_PIPE and STT_ON:
            body["stt_text"] = True                      # 서버가 '상대의 말은 음성 인식 글자로 온다'는 안내를 프롬프트에 넣는다
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
        want_in = LIVE_IN_STT or self.stt_dead or not (LIVE_OUT_PIPE and STT_ON)      # live 출력은 한국어 받아쓰기에 소리를 안 보내므로(_feed_conv) Live 받아쓰기가 유일한 받아쓰기다
        self.in_stt_on = want_in
        if not want_in:
            kw.pop("input_audio_transcription", None)
            log.info("[xiaozhi] Live 내장 입력 받아쓰기를 끕니다 (한국어 전용 받아쓰기만 사용. XIAOZHI_LIVE_IN_STT=1이면 켬)")
        if LIVE_TEXT and LIVE_OUT_PIPE and not minimal:      # 글자만 받기: 소리/목소리/소리 받아쓰기 설정은 뺀다
            kw["response_modalities"] = ["TEXT"]
            kw.pop("speech_config", None)
            kw.pop("output_audio_transcription", None)
            log.info("[xiaozhi] Live 응답을 TEXT로 받습니다 (XIAOZHI_LIVE_TEXT=1 실험 모드)")
        if tools:
            kw["tools"] = tools
        if LIVE_THINKING and not minimal:
            try:
                kw["thinking_config"] = T.ThinkingConfig(thinking_level=LIVE_THINKING)
            except Exception as e:      # 오래된 SDK나 잘못된 값이면 설정 없이 진행
                log.warning("[xiaozhi] XIAOZHI_LIVE_THINKING=%r 설정을 건너뜀: %s", LIVE_THINKING, e)
        if not minimal:
            kw["realtime_input_config"] = T.RealtimeInputConfig(automatic_activity_detection=T.AutomaticActivityDetection(
                start_of_speech_sensitivity=getattr(T.StartSensitivity, "START_SENSITIVITY_" + LIVE_START_SENS, T.StartSensitivity.START_SENSITIVITY_HIGH),
                end_of_speech_sensitivity=getattr(T.EndSensitivity, "END_SENSITIVITY_" + LIVE_END_SENS, T.EndSensitivity.END_SENSITIVITY_LOW),
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
            self.cur_session = session
            self.pending_ends = []
            try:
                await self._receiver(session)
            finally:
                sender.cancel()
                self.cur_session = None
                self.connected = False

    def note_end(self, voiced_ms):
        """대화 중 한 마디를 Live에 보내고 끝냈다 (말소리가 충분히 있었던 말만 센다)."""
        self.utt_voiced = voiced_ms
        if self.utt_text:                          # 글자로 넘기는 말은 실제로 글자를 보낼 때 센다 (_text_send)
            return
        if voiced_ms >= 500 and (self.in_stt_on or len(_norm_text(self.stt_text)) >= 2):      # Live 받아쓰기가 꺼져 있으면 잡음(글자 없음)은 안 센다: Live가 잡음에 대답 안 해도 먹통으로 오판해 재연결하지 않게
            self.pending_ends.append(time.monotonic())

    def check_stuck(self, now):
        """말소리를 2번 이상 보냈는데 Live가 받아쓰기도 대답도 전혀 안 준 채 LIVE_NO_REPLY_S가 지났다면
        Live 연결이 조용히 멈춘 것이다: 그대로 두면 아무리 말해도 대답이 없으니 새 세션으로 다시 연결한다."""
        pe = self.pending_ends
        if (LIVE_NO_REPLY_S and self.connected and self.cur_session is not None
                and len(pe) >= 2 and now - pe[-1] >= LIVE_NO_REPLY_S
                and now - self.last_stuck_t > 60):      # 방금 재연결했는데도 무반응이면 연결 문제가 아니라 소리(잡음) 문제라서 또 재연결하지 않는다
            self.last_stuck_t = now
            self._stuck_close = True
            log.warning("[xiaozhi] Live가 말 %d번에 아무 반응이 없어 %.0fs 지남 -> Live 연결을 새로 합니다", len(pe), now - pe[-1])
            self.pending_ends = []
            self.handle = None
            try:
                self.asyncio.run_coroutine_threadsafe(self.cur_session.close(), self.loop)
            except Exception:
                log.exception("[xiaozhi] Live 연결 닫기 실패")

    # ---------- 한국어 전용 받아쓰기 (별도 전사 모델, 같은 소리를 나란히 보낸다) ----------
    async def _stt_main(self):
        backoff = 1.0
        for _ in range(50):                       # Live 설정(모델 이름)이 오길 잠깐 기다린다
            if self.setup is not None:
                break
            await self.asyncio.sleep(0.2)
        while not self.s.closed and not self.stt_dead:
            try:
                await self._stt_connect_once()
                backoff = 1.0
            except self.asyncio.CancelledError:
                return
            except Exception as e:
                if "inactivity" in str(e):
                    continue
                if STT_VOCAB and not self.stt_ever and not getattr(self, "_vocab_off", False):
                    self._vocab_off = True      # 단어 힌트 때문에 연결이 거절됐을 수 있다: 힌트 없이 다시 시도
                    log.warning("[xiaozhi] 단어 힌트를 붙인 받아쓰기 연결 실패 (%s) - 힌트 없이 다시 시도합니다", str(e)[:200])
                    continue
                self.stt_fails += 1
                log.warning("[xiaozhi] 한국어 받아쓰기 연결/수신 오류 (%d회째, %s): %s", self.stt_fails, type(e).__name__, str(e)[:300])
                if not self.stt_ever and self.stt_fails >= STT_FAILS_MAX:
                    self.stt_dead = True
                    log.error("[xiaozhi] 한국어 받아쓰기가 처음부터 %d번 연속 실패 - Live 받아쓰기로 대신합니다", self.stt_fails)
                    return
            if self.s.closed:
                return
            await self.asyncio.sleep(min(backoff, 8.0))
            backoff *= 2

    async def _stt_connect_once(self):
        from google.genai import types as T
        st = self.setup or {}
        model = st.get("stt_model") or STT_MODEL_DEFAULT
        lang = st.get("stt_language") or "ko-KR"
        atc = None
        if STT_VOCAB and not getattr(self, "_vocab_off", False):
            try:
                atc = T.AudioTranscriptionConfig(language_codes=[lang], custom_vocabulary=list(STT_VOCAB))
            except Exception as e:      # 설치된 google-genai가 오래돼서 이 항목을 모르는 경우
                self._vocab_off = True
                log.warning("[xiaozhi] 받아쓰기 단어 힌트(custom_vocabulary)를 쓸 수 없습니다 - google-genai를 올리면 켜집니다 (%s)", str(e)[:120])
        if atc is None:
            atc = T.AudioTranscriptionConfig(language_codes=[lang])
        cfg = T.LiveConnectConfig(response_modalities=["TEXT"], input_audio_transcription=atc)
        t0 = time.monotonic()
        async with _stt_client().aio.live.connect(model=model, config=cfg) as session:
            self.stt_ever, self.stt_fails = True, 0
            self.stt_connected = True
            log.info("[xiaozhi] 한국어 받아쓰기 연결됨 model=%s lang=%s (%.1fs)", model, lang, time.monotonic() - t0)
            sender = self.loop.create_task(self._stt_sender(session))
            try:
                while not self.s.closed:
                    got = False
                    async for msg in session.receive():
                        got = True
                        sc = msg.server_content
                        if sc is not None and sc.input_transcription and sc.input_transcription.text:
                            self._on_stt_text(sc.input_transcription.text)
                        if msg.go_away:
                            return
                    if not got:
                        await self.asyncio.sleep(0.05)
            finally:
                self.stt_connected = False
                sender.cancel()

    async def _stt_sender(self, session):
        from google.genai import types as T
        while True:
            kind, data, ts = await self.stt_q.get()
            if kind == "audio":
                if time.monotonic() - ts > 8.0:
                    continue
                await session.send_realtime_input(audio=T.Blob(data=data, mime_type="audio/pcm;rate=16000"))
            elif kind == "end":
                await session.send_realtime_input(audio_stream_end=True)

    async def _sender(self, session):
        from google.genai import types as T
        sent = 0
        try:
            while True:
                kind, data, ts = await self.in_q.get()
                if kind == "audio":
                    if time.monotonic() - ts > 8.0:
                        continue
                    await session.send_realtime_input(audio=T.Blob(data=data, mime_type="audio/pcm;rate=16000"))
                    sent += len(data)
                elif kind == "text":
                    if time.monotonic() - ts > 20.0:
                        continue
                    if STT_TEXT_API == "content":
                        await session.send_client_content(turns=T.Content(role="user", parts=[T.Part(text=data)]), turn_complete=True)
                    else:
                        await session.send_realtime_input(text=data)
                elif kind == "end":
                    await session.send_realtime_input(audio_stream_end=True)
                    log.info("[xiaozhi] Live로 audio_stream_end 전송 (이번 말에 보낸 소리 %.1f초)", sent / 32000)
                    sent = 0
        except self.asyncio.CancelledError:
            raise
        except Exception as e:
            log.warning("[xiaozhi] Live로 소리를 보내다 실패 - 연결을 닫고 다시 연결합니다 (%s: %s)", type(e).__name__, str(e)[:200])
            try:
                await session.close()
            except Exception:
                pass

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
                    if sc.input_transcription or sc.model_turn or sc.output_transcription or sc.turn_complete:
                        self.pending_ends.clear()          # Live가 살아서 반응했다
                    if sc.interrupted:
                        self._on_interrupted()
                    if sc.input_transcription and sc.input_transcription.text:
                        self._on_input_text(sc.input_transcription.text)
                    if sc.model_turn and sc.model_turn.parts:          # 소리를 먼저 처리해야 턴이 만들어진 뒤 글자가 붙는다
                        for p in sc.model_turn.parts:
                            idata = getattr(p, "inline_data", None)
                            if idata and idata.data:
                                self._on_audio(idata.data)
                            ptxt = getattr(p, "text", None)
                            if ptxt and LIVE_OUT_PIPE and not getattr(p, "thought", False):      # TEXT 응답: 글자가 소리 받아쓰기가 아니라 여기로 온다
                                self._on_model_text(ptxt)
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
                    resps = await self.asyncio.gather(*[loop.run_in_executor(None, self._run_tool, c) for c in calls])
                    await session.send_tool_response(function_responses=[
                        T.FunctionResponse(id=c.id, name=c.name, response=r) for c, r in zip(calls, resps)])
            if not got:
                await self.asyncio.sleep(0.05)

    # ---------- 모델이 보낸 것 처리 ----------
    def _user_text(self) -> str:
        """화면 표시/대화 기록에 쓸 내 말: 한국어 받아쓰기가 있으면 그것을, 없으면 Live 받아쓰기를 쓴다."""
        return " ".join((self.stt_text or self.utext).split())

    def _take_user_text(self) -> str:
        u = self._user_text()
        self.utext = self.stt_text = ""
        return u

    def _on_input_text(self, text):
        self.discard = False
        self.utext += text
        log.info("[xiaozhi] Live 받아쓰기: %r", text[:200])
        self._after_user_text()

    def _on_stt_text(self, text):
        self.stt_text += text
        log.info("[xiaozhi] 한국어 받아쓰기: %r", text[:200])
        if not self.in_stt_on:
            self.discard = False                  # Live 받아쓰기가 없으니 새 말이 들어온 신호로 한국어 받아쓰기를 쓴다 (_on_input_text와 같은 역할)
        if self.utt_text:                         # 글자로 넘기는 말: 새 글자가 한동안 안 오면 그때 Live로 보낸다
            self.utt_any = True
            self.txt_miss = 0
            self.pend_text += text
            self._arm_txt_timer(STT_TEXT_CLOSED_S if self.utt_closed else STT_TEXT_SETTLE_S)
        self._after_user_text()
        # [CMD OFF - 4. 화면 표시] 화면의 내 말 글자 고쳐 보여 주기
        # if self.turn is not None:                 # 대답이 이미 시작됐으면 화면의 내 말을 더 정확한 글자로 고쳐 보여 준다
        #     self.s.send_json({"type": "stt", "text": self._user_text()})

    def _suppressed(self) -> bool:
        return self.discard

    def _after_user_text(self):
        if len(_norm_text(self._user_text())) >= 2:      # 잡음이 한두 글자로 받아써진 것은 '대화'로 치지 않는다
            self.s.touch()
        if not self.thought_sent:                 # 내 말이 들어오기 시작하면 '생각 중' 표정/고개
            self.thought_sent = True
            self.s.motion_think()
            # [CMD OFF - 2. 표정] self.s.send_json({"type": "llm", "emotion": THINK_EMOTION, "text": ""})

    def _begin_turn(self):
        t = _Turn(self.s)
        t.meta = bool(self.meta_pending) and time.monotonic() - self.meta_pending < 15.0
        self.meta_pending = 0.0
        self.s.busy = True
        self.s.cancel = t.cancel
        self.s.turn_t0 = self.s.turn_progress = time.monotonic()
        self.turn = t
        if not LIVE_OUT_PIPE:           # pipe 출력은 첫 문장 소리가 합성돼 나올 때 Speaker가 tts start를 보낸다
            t.speaker._begin()
        user = self._user_text()
        # [CMD OFF - 4. 화면 표시] stt 텍스트 전송
        # if user:
        #     self.s.send_json({"type": "stt", "text": user})
        lv = getattr(self.s.gate, "last_voiced", 0.0) if self.s.gate else 0.0
        if lv:
            log.info("[xiaozhi] 마지막 말소리 뒤 %.2fs 만에 첫 대답 소리 도착 (입력=%r)", time.monotonic() - lv, user[:200])
        return t

    def _on_model_text(self, text):
        """(TEXT 응답) 소리 없이 글자만 온다: 첫 글자가 오면 턴을 만들고, 이후는 소리 받아쓰기와 똑같이 처리한다."""
        if self._suppressed():
            return
        self.gen_active = True
        if self.turn is None:
            self._begin_turn()
        self._on_output_text(text)

    def _on_audio(self, data: bytes):
        if self._suppressed():
            return
        self.gen_active = True
        t = self.turn or self._begin_turn()
        self.s.turn_progress = time.monotonic()
        if LIVE_OUT_PIPE:
            return                      # Live의 목소리는 쓰지 않고 버린다 (대답 글자만 받아서 TTS로 읽는다)
        self.out_q.put(("pcm", t, data))

    def _on_output_text(self, text):
        if self._suppressed():
            return
        t = self.turn
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
            # [CMD OFF - 2. 표정] self.s.send_json({"type": "llm", "emotion": emo, "text": ""})
        self.s.send_json({"type": "tts", "state": "sentence_start", "text": _TAG.sub("", txt).strip()})
        self.s.motion_speak(emo or t.speaker.last_emo)

    def _on_turn_complete(self):
        self.gen_active = False
        self.thought_sent = False
        if self.discard:
            self.discard = False
            self.utext = self.stt_text = ""
            if LIVE_OUT_PIPE and self.turn is not None:
                self.turn.cancel.set()
                self.turn.speaker.q.put(None)
                self.turn = None
            return
        t = self.turn
        if t is None:
            self.utext = self.stt_text = ""
            return
        if LIVE_OUT_PIPE:
            self._arm_finalize(t)                 # 마지막 글자가 늦게 올 수 있어서 잠깐 기다렸다가 마무리
            return
        if t.obuf.strip():
            self._sentence(t, t.obuf)
            t.obuf = ""
        user = self._take_user_text()
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
        user = self._take_user_text()
        if t.cancel.is_set():
            return
        self.out_q.put(("end", t, user))

    def _on_interrupted(self):
        self.gen_active = False
        self.discard = False
        t = self.turn
        self.turn = None
        if t is not None:
            t.cancel.set()
            if LIVE_OUT_PIPE:
                t.speaker.q.put(None)
            if self.s.cancel is t.cancel:
                self.s.busy = False
            self.s.send_json({"type": "tts", "state": "stop"})
        self._fire_after(False)
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
        sp.end()
        reply = " ".join(_clean(t.otext).split())
        if reply and not t.cancel.is_set() and not t.meta:
            s.turns += [{"role": "user", "text": user_text or "(음성 메시지)"}, {"role": "model", "text": reply}]
            s.turns = s.turns[-MAX_TURNS_KEPT:]
            if user_text:
                threading.Thread(target=s.save_turn, args=(user_text, reply), daemon=True).start()
        log.info("[xiaozhi] Live 턴 완료 %.1fs 취소=%s 입력=%r%s", time.monotonic() - t.t0, t.cancel.is_set(), user_text[:200], " (서버가 시킨 말)" if t.meta else "")
        s.last_active = time.monotonic()
        if s.cancel is t.cancel:
            s.busy = False
            s._mute_until = time.monotonic() + LIVE_TAIL_MUTE_S
            if not s.closed:
                s.gate = LiveGate(manual=(s.mode == "manual"))
        if t.meta:
            self._fire_after(not t.cancel.is_set())


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
        self.last_audio_t = time.monotonic()    # 기기 마이크 소리가 마지막으로 도착한 때 (마이크 끊김 감시용)
        self.spk_state = None                   # 화자 확인: None / collect(모으는 중) / pending(판정 중) / pass(통과, 그대로 전달) / drop(버리는 중)
        self.spk_buf = bytearray()
        self.spk_fut = None
        self.stop_at = None
        self.resumed = False
        _prev = _RESUME.pop(device_id, None)
        if _prev and time.monotonic() - _prev["t"] <= RESUME_WINDOW_S:      # 직전 연결이 막 끝났다: 대화 기록을 이어받는다
            self.turns = list(_prev.get("turns") or [])
            self.resumed = True
        # 연결 유지 모드에서는 연결이 맺어졌다고 대화가 시작된 게 아니다: 호출어(detect)/터치/listen start가 와야 대화 중이 된다
        self.in_convo = not KEEP_CONNECTION
        self._convo_started = False if KEEP_CONNECTION else self.resumed      # 이 연결에서 대화 시작(고개 정면)을 이미 했나
        self._ending = False                    # 서버가 연결을 닫는 중이다
        self._web = None                        # 웹 화면에서 보낸 글을 읽는 중인 대답 (say_chunk)
        self._say_lock = threading.Lock()
        self.turn_progress = time.monotonic()   # 마지막으로 대답이 진전된 때 (소리 전송/서버 응답 조각)
        self.has_robot = False
        self._mute_until = 0.0                  # 대기 동작 중 모터 소리를 말로 오인하지 않게 잠깐 듣지 않는다
        self._stick_mute = False                # M5Stick 버튼을 누르는 동안 True: 스택챈 마이크 소리를 버린다 (/xiaozhi/mute, /xiaozhi/unmute)
        self._stick_mute_at = 0.0               # 마지막으로 뮤트가 걸린 시각 (unmute가 유실돼도 STICK_MUTE_MAX_S 뒤 자동 해제)
        self.live = None                        # Gemini Live 연결 (live 모드일 때)
        self.gate = None                        # 마이크 소리를 Live로 보낼지 정하는 문

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
        # [비활성화] 대화 시작 시 서버(/api/pipe/start)에서 직전 대화 블록(ctx)을 가져오던 부분.
        # 주석을 풀면 원래대로 돌아간다. 그동안 ctx="", sig="", model_tags=False 로 진행한다.
        # try:
        #     r = self._client().post("/api/pipe/start", json={}, headers=self.auth_headers())
        #     d = r.get_json(silent=True) or {}
        #     self.ctx, self.sig, self.model_tags = d.get("ctx") or "", d.get("sig") or "", bool(d.get("modelTags"))
        #     log.info("[xiaozhi] 직전 대화 블록 준비 (%s자, status=%s)", len(self.ctx), r.status_code)
        # except Exception as e:
        #     log.warning("[xiaozhi] /api/pipe/start 실패 - 이전 대화 블록 없이 진행: %s", e)
        # finally:
        #     self.ctx_ready.set()
        log.info("[xiaozhi] 직전 대화 블록 가져오기 꺼짐 (주석 처리됨)")
        self.ctx_ready.set()

    def synth(self, text: str, prev: str) -> bytes:
        body = {"text": text, "fast": True, "tempo": XZ_TTS_TEMPO, **({"tags": False} if STRIP_EMO else {})}      # fast: 문장마다 감정 태그 LLM을 기다리지 않고 키워드 규칙으로 바로 합성 (서버가 2.5초씩 기다리던 것을 없앤다)
        if prev:
            body["previous_text"] = prev
        if XZ_VOICE_ID:
            body["voice_id"] = XZ_VOICE_ID
        if self.model_tags:
            body["model_tags"] = True
        t0 = time.monotonic()
        r = self._client().post("/api/tts", json=body, headers=self.auth_headers())
        dt = time.monotonic() - t0
        if r.status_code != 200:
            log.warning("[xiaozhi] TTS 서버 처리 %.2fs 후 실패 status=%s (글자 %d)", dt, r.status_code, len(text))
            raise RuntimeError(f"/api/tts {r.status_code}: {r.get_data(as_text=True)[:120]}")
        b = r.get_data()
        b = b[:len(b) - len(b) % 2]
        log.info("[xiaozhi] TTS 서버 처리 %.2fs (글자 %d -> 소리 %.1fs) %r", dt, len(text), len(b) / 2 / 24000, text[:30])      # 소리 길이는 서버 합성 24kHz 16bit 기준
        return b

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
            if self.resumed:
                log.info("[xiaozhi] 직전 연결에서 대화 기록을 이어받음")
            if not getattr(self, "_idle_started", False):
                self._idle_started = True
                threading.Thread(target=self._idle_loop, daemon=True, name="xz-idle").start()
            # --- 진단용: 기기가 MCP(움직임 등 도구)를 지원하면 도구 목록을 요청해서 로그로 찍는다 ---
            feats = obj.get("features") or {}
            log.info("[xiaozhi] 기기 features=%s", json.dumps(feats, ensure_ascii=False)[:300])
            if feats.get("mcp") and MCP_ON:
                self._mcp_id = 0
                caps = {}
                if getattr(self, "vision_url", ""):       # 카메라 사진을 올려 보낼 주소를 기기에 알려 준다 (/xiaozhi/cam/ 화면용)
                    caps["vision"] = {"url": self.vision_url, "token": _device_token(self.device_id)}
                    log.info("[xiaozhi] 기기에 알려 준 카메라 업로드 주소: %s", self.vision_url)
                self._mcp_call("initialize", {"protocolVersion": "2024-11-05", "capabilities": caps,
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
                self.in_convo = True
                self.mode = str(obj.get("mode") or "auto")
                if self.live:
                    self.gate = LiveGate(manual=(self.mode == "manual"))
                else:
                    self.ep = Endpointer(manual=(self.mode == "manual"))
                if self.mode == "manual":      # 화면을 눌러 시작한 대화: 고개를 정면으로 맞추고, 바로 듣고 부저음
                    self._begin_conversation()
                    if not self.busy:
                        threading.Thread(target=self._beep_only, daemon=True, name="xz-beep").start()
            elif st == "stop":
                self.stop_at = None      # 기기가 일부러 듣기를 멈췄다: 마이크 감시(watchdog)가 '마이크 끊김'으로 오해해 연결을 끊지 않게 한다
                if KEEP_CONNECTION and self.mode != "manual":
                    self._convo_idle_end("기기가 대화를 끝냈다(listen stop)")      # 연결은 그대로 둔다
                if self.live:
                    if self.gate is not None and self.gate.manual:
                        self.live.end_input()
                elif self.ep is not None and self.ep.manual:
                    self._on_utterance(self.ep.finish())
                    self.ep = None
            elif st == "detect":
                # 기기가 호출어를 알아듣거나 화면을 두드려 대화를 시작했다 (기기가 연결음/녹색등은 스스로 낸다)
                log.info("[xiaozhi] 기기 대화 시작 신호 %r", obj.get("text"))
                self.last_active = time.monotonic()
                self.in_convo = True
                self._begin_conversation()
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
                    if not hasattr(self, "_tool_schemas"):
                        self._tool_schemas = {}
                    for t_ in tl:
                        self._tool_schemas[t_.get("name")] = t_.get("inputSchema") or {}
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
        # [CMD OFF - 1. 고개 움직임] 기기에 고개 이동 명령(self.robot.set_head_angles)을 보내지 않는다
        return
        # if not MOTION or self.closed or not getattr(self, "has_robot", False):
        #     return
        # now = time.monotonic()
        # if now - getattr(self, "_last_move", 0.0) < min_gap:
        #     return
        # self._last_move = now
        # pan = max(-70, min(70, int(pan)))
        # tilt = max(-35, min(35, int(tilt)))
        # dur = max(120, min(5000, int(dur)))
        # self._mcp_call("tools/call", {"name": "self.robot.set_head_angles",
        #                               "arguments": {"pan": pan, "tilt": tilt, "duration_ms": dur}}, quiet=True)

    def center_head(self):
        # [CMD OFF - 1. 고개 움직임] 기기에 고개 정면 명령(center_head)을 보내지 않는다
        return
        # if not MOTION or self.closed or not getattr(self, "has_robot", False):
        #     return
        # self._last_move = time.monotonic()
        # if "self.robot.center_head" in getattr(self, "_tool_names", []):
        #     self._mcp_call("tools/call", {"name": "self.robot.center_head", "arguments": {}}, quiet=True)
        # else:
        #     # 공장 펌웨어에는 center_head가 없다 -> 정면(0, 0)으로 set_head_angles
        #     self._mcp_call("tools/call", {"name": "self.robot.set_head_angles",
        #                                   "arguments": {"pan": 0, "tilt": 0, "duration_ms": 600}}, quiet=True)

    def _head_raw(self, pan=0, tilt=0, dur=700):
        """[정면 맞추기] CMD OFF(move_head/center_head 막힘)와 상관없이 고개 이동 명령을 직접 보낸다. 테스트 주소와 face_front()가 쓴다."""
        names = getattr(self, "_tool_names", None) or []
        tool = "self.robot.set_head_angles"
        if self.closed or (names and tool not in names):      # 재접속 직후라 도구 목록이 비어 있으면 일단 시도한다
            return
        pan = max(-70, min(70, int(pan)))
        tilt = max(-35, min(35, int(tilt)))
        dur = max(120, min(5000, int(dur)))
        self._mute_until = max(self._mute_until, time.monotonic() + dur / 1000.0 + 0.6)      # 모터 소리를 마이크가 말로 오인하지 않게
        self._mcp_call("tools/call", {"name": tool,
                                      "arguments": {"pan": pan, "tilt": tilt, "duration_ms": dur}}, quiet=True)

    def face_front(self, dur=700):
        """[정면 맞추기] 대화가 시작될 때 고개를 정면으로 맞춘다 (카메라가 화자 쪽을 보게). 다른 고개 움직임은 꺼져 있어서 그대로 고정된다."""
        if not FRONT_ON:
            return
        log.info("[xiaozhi] 고개 정면으로 (pan=%d tilt=%d)", FRONT_PAN, FRONT_TILT)
        self._head_raw(FRONT_PAN, FRONT_TILT, dur)

    def _beep_only(self):
        # [CMD OFF - 5. 소리] 연결 부저음을 기기에 보내지 않는다
        return
        # sp = Speaker(self, threading.Event())
        # sp.beep()
        # sp.close()
        # sp.end()

    # --- 대화 시작/종료 ---
    def _begin_conversation(self):
        """대화가 시작됐다 (기기가 호출어/터치로 깨워 연결한 직후): 고개를 정면으로 맞춘다. 연결 하나에 한 번만 한다."""
        if self._convo_started:
            return
        self._convo_started = True
        log.info("[xiaozhi] 대화 시작")
        self.face_front()      # [정면 맞추기] 호출어/화면 터치 모두 여기를 거친다

    def set_stick_mute(self, on: bool):
        """M5Stick 버튼을 누르는 동안 스택챈 마이크 소리를 서버에서 버린다 (스택챈 펌웨어는 그대로 둔다).
        mute: 지금 듣던 말/문(gate)을 비운다. unmute: 잔향 방지로 STICK_UNMUTE_DELAY_S 동안 더 버린 뒤 다시 듣는다."""
        now = time.monotonic()
        if on:
            self._stick_mute, self._stick_mute_at = True, now
            if self.live is not None:
                was_open = bool(self.gate is not None and self.gate.open)
                self.gate = LiveGate(manual=(self.mode == "manual"))      # 앞서 쌓인 preroll/열린 문을 버린다
                self.spk_state, self.spk_buf, self.spk_fut = None, bytearray(), None
                if was_open:
                    self.live.stream_end()                                # 말하던 중이었다면 Live에 스트림 끝을 알린다
            elif self.mode != "manual":
                self.ep = Endpointer()
            log.info("[xiaozhi] M5Stick mute -> 스택챈 마이크 소리 버림")
        else:
            self._stick_mute = False
            self._mute_until = max(self._mute_until, now + STICK_UNMUTE_DELAY_S)
            if self.live is not None:
                self.gate = LiveGate(manual=(self.mode == "manual"))
            log.info("[xiaozhi] M5Stick unmute -> %.1fs 뒤 스택챈 마이크 복귀", STICK_UNMUTE_DELAY_S)

    def touch(self):
        """대화/말소리가 있었다: 마지막 활동 시각을 갱신해 연결을 닫기까지의 시간(CONVO_IDLE_S)을 다시 센다."""
        self.last_active = time.monotonic()

    def _convo_idle_end(self, why):
        """대화만 끝낸다 (연결은 닫지 않는다). 다음 호출어/터치 때 대화가 새로 시작되고 고개도 다시 정면을 본다."""
        if self.in_convo:
            log.info("[xiaozhi] 대화 종료 (연결 유지): %s", why)
        self.in_convo = False
        self._convo_started = False

    def _farewell_then_end(self, text=None, dismissed=False):
        """대화 중이던 기기가 조용해서 연결을 닫기 전에, 말없이 사라지지 않게 한마디 하고 연결을 닫는다.
        인사하는 중에 사용자가 말을 걸어 끊으면(abort/listen start) 닫지 않는다.
        text: 인사 문구(없으면 SLEEP_FAREWELL). dismissed: 사용자가 '들어가' 하고 시켜서 가는 것."""
        text = text or SLEEP_FAREWELL
        if self.live is not None and not LIVE_OUT_PIPE:      # live 출력: TTS 없이 Live 목소리로 인사한다
            self._farewell_via_live(text, dismissed)
            return
        cancel = threading.Event()
        self.cancel = cancel
        self.turn_progress = time.monotonic()
        log.info("[xiaozhi] 대화를 끝내기 전에 인사: %r", text)
        try:
            sp = Speaker(self, cancel)
            sp.feed(text)
            sp.flush()
            sp.close()
            sp.end()
        except Exception:
            log.exception("[xiaozhi] 대기 전 인사 실패")
        finally:
            if self.cancel is cancel:
                self.busy = False
                if self.live and not self.closed:
                    self.gate = LiveGate(manual=(self.mode == "manual"))
        if cancel.is_set() or self.closed:
            self.last_active = time.monotonic()      # 사용자가 끼어들었다: 닫지 않고 계속 대화
            return
        self.end_conversation(delay_s=0.8)      # 인사 소리가 기기에서 다 나온 뒤에 닫는다

    def _farewell_via_live(self, text=None, dismissed=False):
        """live 출력: 작별 인사를 Live에게 시켜 Live 목소리로 말하게 한다 (TTS 없음). 끝나면 연결을 닫는다.
        Live가 15초 안에 아무 반응이 없으면 말없이 연결을 닫는다. 사용자가 끼어들면 닫지 않는다."""
        text = text or SLEEP_FAREWELL
        started = time.monotonic()
        done = threading.Event()
        self.turn_progress = started

        def _fin(ok):
            done.set()
            if ok:
                self.end_conversation(delay_s=0.8)      # 인사 소리가 기기에서 다 나온 뒤에 닫는다
            else:
                self.last_active = time.monotonic()      # 사용자가 끼어들었다: 닫지 않고 계속 대화

        log.info("[xiaozhi] 대화를 끝내기 전에 인사(Live 목소리): %r", text)
        why = "한동안 대화가 없어서"
        prompt = (f"[시스템 안내 - 사용자가 한 말이 아니다] {why} 곧 대화를 끝내고 연결을 닫는다. "
                  "아래 인사를 네 말투로 한 번만, 한두 문장으로 짧게 말해라. 다른 말은 덧붙이지 마라.\n" + text)
        if not self.live.say_text(prompt, _fin):
            self.busy = False
            self.end_conversation(delay_s=0.8)      # 인사 소리가 기기에서 다 나온 뒤에 닫는다
            return
        while not done.is_set() and not self.closed:
            time.sleep(0.2)
            if time.monotonic() - self.turn_progress > 15.0:      # 소리 전송/대답이 15초 동안 진전이 없다
                break
        if done.is_set() or self.closed:
            return
        log.warning("[xiaozhi] Live가 작별 인사에 반응이 없어 말없이 연결을 닫습니다")
        self.live.cancel_say()
        self.busy = False
        if not self.closed:
            self.gate = LiveGate(manual=(self.mode == "manual"))
            self.end_conversation(delay_s=0.8)      # 인사 소리가 기기에서 다 나온 뒤에 닫는다

    def end_conversation(self, delay_s=0.0):
        """대화 종료: 서버가 먼저 WebSocket 연결을 닫는다 (기다리지 않고 스레드로 닫는다).
        기기는 연결이 닫히면 서버와 통신하지 않는 상태로 돌아가고, 호출어/터치로 깨울 때만 다시 연결한다."""
        if self._ending or self.closed:
            return
        self._ending = True
        log.info("[xiaozhi] 대화가 끝나서 연결을 닫습니다 (device=%s)", self.device_id)

        def _close():
            if delay_s:
                time.sleep(delay_s)
            try:
                with self.send_lock:
                    self.ws.close(reason=1000, message="conversation-ended")
            except Exception:
                pass

        threading.Thread(target=_close, daemon=True, name="xz-end").start()

    def _idle_loop(self):
        nxt = time.monotonic() + random.uniform(IDLE_MIN_S, IDLE_MAX_S)
        last_ka = time.monotonic()
        while not self.closed:
            time.sleep(1.0)
            now = time.monotonic()
            if KEEPALIVE_S and now - last_ka >= KEEPALIVE_S:
                last_ka = now
                self.send_json({"session_id": self.session_id, "type": "keepalive"})      # 기기가 모르는 종류의 신호는 무시하고, 받았다는 사실만 남는다
            if (MIC_WATCHDOG_S and self.in_convo and self.stop_at and self.mode != "manual" and not self.busy
                    and now - self.stop_at >= MIC_WATCHDOG_S and now - self.last_audio_t >= MIC_WATCHDOG_S
                    and now - self.turn_progress >= MIC_WATCHDOG_S):
                # 대답(tts stop) 뒤에 기기 마이크 소리가 끊겼다: 기기가 듣기 상태로 못 돌아온 것이다.
                # 가만히 두면 기기가 한참 뒤 스스로 연결을 닫고 대기로 가므로, 먼저 끊어서 기기가 바로 새로 연결하게 한다.
                log.warning("[xiaozhi] 대답이 끝난 뒤 기기 마이크 소리가 %.1fs 동안 없음 -> 연결을 닫아 기기가 다시 연결하게 합니다", now - max(self.stop_at, self.last_audio_t))
                self.stop_at = None
                try:
                    with self.send_lock:
                        self.ws.close(reason=1000, message="mic-watchdog")
                except Exception:
                    pass
            if self.live is not None and not self.busy:
                self.live.check_stuck(now)
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
            if self.busy or (not self.live and self._hearing()):
                self.touch()                  # 말소리가 들리면 대화 중으로 친다
                nxt = now + random.uniform(IDLE_MIN_S, IDLE_MAX_S)
                continue
            if (CONVO_END_S and self.in_convo and self.mode != "manual" and not self._ending
                    and now - self.last_active >= CONVO_END_S):
                # 듣기 상태에서 CONVO_END_S 동안 말소리도 대답도 없었다: 연결을 닫으면 기기가 대기(Idle)로 간다.
                # (펌웨어는 서버가 연결을 닫을 때만 대기로 돌아간다. 호출어/터치로 다시 깨운다)
                log.info("[xiaozhi] %.0f초 동안 대화가 없어 대기 모드로 보냅니다", now - self.last_active)
                self._convo_idle_end("무활동 %.0f초" % CONVO_END_S)
                if CONVO_END_FAREWELL and SLEEP_FAREWELL:
                    threading.Thread(target=self._farewell_then_end, daemon=True, name="xz-farewell").start()
                else:
                    self.end_conversation(delay_s=0.0)
                continue
            if not IDLE:
                continue
            # 대기 모드로 보내는 일은 기기가 맡는다 (기기의 무활동 타이머 -> listen stop). 서버는 무활동 타이머로 대화를 끝내거나 연결을 닫지 않는다.
            if now >= nxt:
                nxt = now + random.uniform(IDLE_MIN_S, IDLE_MAX_S)
                dur = random.randint(900, 1600)
                self._mute_until = now + dur / 1000.0 + 0.6
                self.move_head(random.randint(-30, 30), random.randint(-4, 12), dur, min_gap=0)
                # [CMD OFF - 2. 표정] idle 표정 전송
                # if IDLE_EMOTIONS and random.random() < 0.6:
                #     self.send_json({"type": "llm", "emotion": random.choice(IDLE_EMOTIONS), "text": ""})

    def _hearing(self) -> bool:
        """지금 사람 말소리가 들어오는 중인가 (대기 동작/잠들기 판단용)."""
        if self.live:
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
        if self._stick_mute:                         # M5Stick 버튼을 누르는 동안: 스택챈은 듣지 않는다
            if time.monotonic() - self._stick_mute_at > STICK_MUTE_MAX_S:
                self._stick_mute = False             # unmute 신호가 유실됐다: 안전장치로 자동 복귀
                log.warning("[xiaozhi] unmute 신호가 %.0fs 동안 없어 스택챈 마이크를 자동으로 복귀합니다", STICK_MUTE_MAX_S)
            else:
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
        pcm = _amplify(pcm, MIC_GAIN)        # 작은 목소리도 알아듣게 키운다 (VAD/Live 모두 키운 소리를 쓴다)
        if self.live:                       # Live 모드: 말소리가 열린 동안만 Live로 흘려보낸다 (말 끝은 Live 서버가 판단)
            if self.gate is not None:
                was_open = self.gate.open
                sent = self.gate.feed(pcm)
                if sent:
                    if SPK_ON_CONVO:
                        self._convo_feed(sent, was_open)       # 등록된 목소리인지 확인한 뒤에만 Live로 보낸다
                    else:
                        if self.gate.open and not was_open:
                            self.live.new_utterance()          # 새 말이 시작됐다: 지난 말의 받아쓰기를 비운다
                            self.touch()                       # 대화 중 말소리도 '활동': Live가 대답을 못 해도 말하는 동안 대기로 잠들지 않게
                        self.live.feed(sent)
                        if was_open and not self.gate.open:      # 대화 중 한 마디가 끝났다: Live에 스트림 끝을 알린다
                            self.touch()
                            self.live.note_end(self.gate.voiced_ms)
                            self.live.stream_end()
            return
        out = self.ep.feed(pcm)
        if out is not None:
            self.ep = None if self.ep.manual else Endpointer()
            self._on_utterance(out)

    # --- 화자(가족 목소리) 확인: TV/낯선 사람 소리를 Live로 보내지 않는다 ---
    def _spk_accept(self):
        """확인 통과(또는 판정 불가): 모아 둔 소리를 Live로 보내고 이후 소리는 그대로 전달한다."""
        self.live.new_utterance()
        self.touch()
        if self.spk_buf:
            self.live.feed(bytes(self.spk_buf))
        self.spk_buf = bytearray()
        self.spk_state = "pass"

    def _spk_apply(self, res):
        ok, name, score = res
        if ok is False:
            log.info("[xiaozhi] 화자 확인: 등록된 목소리가 아님 (가장 비슷한 %s, 점수 %.2f) -> 이번 말 버림", name, score)
            self.spk_buf = bytearray()
            self.spk_state = "drop"
        else:
            if ok is True:
                log.info("[xiaozhi] 화자 확인: %s (점수 %.2f) -> 통과", name, score)
            self._spk_accept()

    def _convo_feed(self, sent, was_open):
        opened = self.gate.open and not was_open
        closed = was_open and not self.gate.open
        if opened:
            self.spk_state, self.spk_buf, self.spk_fut = "collect", bytearray(), None
        st = self.spk_state
        if st == "pass":
            self.live.feed(sent)
        elif st in ("collect", "pending"):
            self.spk_buf += sent
            if st == "collect" and not closed and len(self.spk_buf) >= SPEAKER_VERIFY_MS * 32 and self.gate.voiced_ms >= 500:
                self.spk_fut = _SPK_POOL.submit(_speaker_check, bytes(self.spk_buf[-32000 * 10:]))
                self.spk_state = "pending"
            elif st == "pending" and self.spk_fut is not None and self.spk_fut.done():
                try:
                    res = self.spk_fut.result()
                except Exception:
                    res = (None, None, None)
                self.spk_fut = None
                self._spk_apply(res)
        if closed:
            st = self.spk_state
            if st == "pending" and self.spk_fut is not None:           # 판정 중에 말이 끝났다: 잠깐 기다린다
                try:
                    res = self.spk_fut.result(timeout=SPEAKER_TIMEOUT_S)
                except Exception:
                    res = (None, None, None)
                self.spk_fut = None
                self._spk_apply(res)
            elif st == "collect":                                      # 판정할 만큼 길지 않은 말
                if self.gate.voiced_ms >= 450 and len(self.spk_buf) >= 16000:
                    try:
                        res = _SPK_POOL.submit(_speaker_check, bytes(self.spk_buf)).result(timeout=SPEAKER_TIMEOUT_S)
                    except Exception:
                        res = (None, None, None)
                    self._spk_apply(res)
                elif SPEAKER_SHORT_DROP:
                    log.info("[xiaozhi] 화자 확인: 너무 짧은 말(%dms) -> 버림", self.gate.voiced_ms)
                    self.spk_buf, self.spk_state = bytearray(), "drop"
                else:
                    self._spk_accept()
            st = self.spk_state
            if st == "pass":                                            # 통과한 말이 끝났다: Live에 스트림 끝을 알린다
                self.touch()
                self.live.note_end(self.gate.voiced_ms)
                self.live.stream_end()
            self.spk_state, self.spk_buf = None, bytearray()

    # --- 웹 화면에서 글로 물은 대답을 이 기기 스피커로 읽는다 ---
    def say_chunk(self, tid, text, final):
        """웹 화면이 대답 글자를 조각조각 보내 준다. 같은 tid의 조각은 하나의 '말하기 턴'으로 이어서 읽는다.
        반환: True(받음) / False(기기가 지금 다른 대답을 하는 중이라 받지 못함)"""
        if self.live is not None and not LIVE_OUT_PIPE:      # live 출력: 글자를 모았다가 끝나면 Live 목소리로 읽게 한다 (TTS 없음)
            return self._say_chunk_live(tid, text, final)
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
                log.info("[xiaozhi] 웹에서 보낸 대답 읽기 시작 tid=%s", tid)
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

    def _say_chunk_live(self, tid, text, final):
        with self._say_lock:
            w = self._web
            if w is None or w["tid"] != tid:
                if self.busy:
                    return False
                self.busy = True
                self.cancel = threading.Event()
                self.turn_progress = time.monotonic()
                self.touch()
                log.info("[xiaozhi] 웹에서 보낸 대답 읽기 시작(Live 목소리) tid=%s", tid)
                w = self._web = {"tid": tid, "buf": [], "n": 0, "t0": time.monotonic()}
            if text:
                w["buf"].append(text)
                w["n"] += len(text)
                self.turn_progress = time.monotonic()
            if final:
                self._web = None
        if final:
            threading.Thread(target=self._say_finish_live, args=(w,), daemon=True, name="xz-say").start()
        return True

    def _say_finish_live(self, w):
        body = " ".join("".join(w["buf"]).split())[:3000]
        done = threading.Event()

        def _fin(ok):
            done.set()
            self.last_active = time.monotonic()
            log.info("[xiaozhi] 웹에서 보낸 대답 읽기 완료(Live) %.1fs %d자 끊김=%s", time.monotonic() - w["t0"], w["n"], not ok)

        def _release():
            self.busy = False
            self._mute_until = time.monotonic() + LIVE_TAIL_MUTE_S
            if not self.closed:
                self.gate = LiveGate(manual=(self.mode == "manual"))

        if not body or not self.live.say_text(
                "[시스템 안내 - 사용자가 한 말이 아니다] 아래는 화면에서 나눈 대화의 네 답변이다. "
                "내용을 바꾸거나 덧붙이거나 요약하지 말고, 그대로 자연스럽게 소리 내어 읽어라.\n\n" + body, _fin):
            _release()
            return
        self.turn_progress = time.monotonic()
        while not done.is_set() and not self.closed:
            time.sleep(0.2)
            if time.monotonic() - self.turn_progress > 20.0:
                break
        if not done.is_set() and not self.closed:
            log.warning("[xiaozhi] Live가 웹 대답 읽기에 반응이 없어 포기합니다")
            self.live.cancel_say()
            _release()

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
                if self.live:               # Live 입력: 스피커 잔향을 말로 오인하지 않게 잠깐 듣지 않고, 마이크 문을 새로 연다
                    self._mute_until = time.monotonic() + LIVE_TAIL_MUTE_S
                    if not self.closed:
                        self.gate = LiveGate(manual=(self.mode == "manual"))
                elif not self.closed and self.mode != "manual":
                    self.ep = Endpointer()

    def play_sound(self, path: str) -> bool:
        """서버에 있는 소리 파일(mp3 등)을 기기 스피커로 재생한다 (예: '주문을 외워줘' -> sound/seri-mirotic.mp3).
        ffmpeg로 24kHz 16bit mono PCM으로 풀면서, TTS 대답과 똑같은 경로(Speaker -> Opus 60ms 프레임 -> 실시간 속도)로 보낸다.
        반환: True(재생 시작) / False(기기가 다른 말을 하는 중이거나, 파일/ffmpeg가 없어서 시작하지 못함).
        재생은 별도 스레드에서 하므로 바로 돌아온다. 기기가 말을 걸어 끼어들면(abort) 대답처럼 멈춘다."""
        ff = _which("ffmpeg")
        if not ff or not path or not os.path.isfile(path):
            log.warning("[xiaozhi] 소리 파일 재생 불가 (ffmpeg=%s, 파일=%s)", bool(ff), path)
            return False
        with self._say_lock:
            if self.busy:
                return False
            self.busy = True
            cancel = threading.Event()
            self.cancel = cancel
            self.turn_progress = time.monotonic()
        threading.Thread(target=self._play_sound_run, args=(ff, path, cancel), daemon=True, name="xz-sound").start()
        return True

    def _play_sound_run(self, ff, path, cancel):
        proc, total, t0 = None, 0, time.monotonic()
        try:
            self.touch()
            log.info("[xiaozhi] 소리 파일 재생 시작: %s", os.path.basename(path))
            sp = Speaker(self, cancel)
            sp._begin()
            fb = OUT_FRAME_SAMPLES * 2
            proc = subprocess.Popen([ff, "-nostdin", "-v", "error", "-i", path, "-f", "s16le", "-ac", "1", "-ar", str(OUT_RATE), "-"],
                                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            while not cancel.is_set() and not self.closed:
                chunk = proc.stdout.read(fb * 8)       # 60ms 프레임 8개씩 (마지막 조각만 프레임보다 짧을 수 있다)
                if not chunk:
                    break
                total += len(chunk)
                self.turn_progress = time.monotonic()      # 긴 곡이 '진전 없음'으로 취소되지 않게
                sp.emit_pcm(chunk)                         # 실시간 속도에 맞춰 보낸다 (Pacer)
            sp.close()
            sp.end()
            log.info("[xiaozhi] 소리 파일 재생 완료 %.1fs (소리 %.1fs) 취소=%s", time.monotonic() - t0, total / 2 / OUT_RATE, cancel.is_set())
        except Exception:
            log.exception("[xiaozhi] 소리 파일 재생 실패")
        finally:
            try:
                if proc is not None and proc.poll() is None:
                    proc.kill()
            except Exception:
                pass
            self.last_active = time.monotonic()
            if self.cancel is cancel:
                self.busy = False
                if self.live:               # 스피커 잔향을 말로 오인하지 않게 잠깐 듣지 않고, 마이크 문을 새로 연다 (대답 읽기와 같은 처리)
                    self._mute_until = time.monotonic() + LIVE_TAIL_MUTE_S
                    if not self.closed:
                        self.gate = LiveGate(manual=(self.mode == "manual"))
                elif not self.closed and self.mode != "manual":
                    self.ep = Endpointer()

    def abort(self):
        """말하던 것(대답)을 멈춘다."""
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
        # [CMD OFF - 2. 표정] self.send_json({"type": "llm", "emotion": THINK_EMOTION, "text": ""})      # 대답을 기다리는 동안 기기 화면이 멈춘 것처럼 보이지 않게
        threading.Thread(target=self._turn, args=(pcm, self.cancel), daemon=True, name="xz-turn").start()

    # --- 한 턴 ---
    def _turn(self, pcm: bytes, cancel: threading.Event):
        speaker = None
        t_start = time.monotonic()
        try:
            self.ctx_ready.wait(timeout=5)
            tid = "x" + uuid.uuid4().hex[:15]
            boosted = _boost(pcm)
            sec, pk0, rms0, clip0 = _pcm_stats(pcm)
            _, pk1, rms1, clip1 = _pcm_stats(boosted)
            hint = ""
            if pk0 < 2500:
                hint = " ← 소리가 작음 (XIAOZHI_MIC_GAIN을 올려 보세요)"
            elif clip0 >= 1.0:
                hint = " ← 소리가 찌그러짐 (XIAOZHI_MIC_GAIN을 낮춰 보세요)"
            log.info("[xiaozhi] 받아쓰기에 보낸 소리 %.1f초 | 원본 최대 %d·평균 %d → 증폭 후 최대 %d·평균 %d | 찌그러진 샘플 %.2f%%%s",
                     sec, pk0, rms0, pk1, rms1, clip0, hint)
            payload = {"audio": base64.b64encode(_wav16k(boosted)).decode(), "mime": "audio/wav",
                       "turns": self.turns[-30:], "ctx": self.ctx, "sig": self.sig, "tid": tid}
            if XZ_LAT and XZ_LNG:
                payload["lat"], payload["lng"] = XZ_LAT, XZ_LNG
            speaker = Speaker(self, cancel)
            real, user_text, stopped, got_error = [], "", False, False
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
                        if user_text:
                            log.info("[xiaozhi] 받아쓰기: %r (말 %.1f초, 요청 후 %.1fs 만에 받음)", user_text, sec, time.monotonic() - t_start)
                        # [CMD OFF - 4. 화면 표시] self.send_json({"type": "stt", "text": user_text})
                    elif kind == "stop":
                        stopped = True
                    elif kind == "error":
                        got_error = True
                        log.warning("[xiaozhi] pipe 오류: %s", ev.get("message"))
            try:
                resp.close()
            except Exception:
                pass
            if not user_text and not cancel.is_set():
                log.warning("[xiaozhi] 받아쓰기 결과가 없음 (말 %.1f초) - 위의 '받아쓰기에 보낸 소리' 줄로 소리 크기를 확인하세요", sec)
            if got_error and not real and self.error_text():
                speaker.filler(self.error_text())
            speaker.flush()
            speaker.close()
            speaker.end()
            reply = "".join(real).strip()
            if reply and not cancel.is_set():                     # 필러/사과 한마디는 기록하지 않는다 (웹 화면과 같은 규칙)
                self.turns += [{"role": "user", "text": user_text or "(음성 메시지)"}, {"role": "model", "text": reply}]
                self.turns = self.turns[-MAX_TURNS_KEPT:]
            self.last_active = time.monotonic()
            log.info("[xiaozhi] 턴 완료 %.1fs 취소=%s 입력=%r", time.monotonic() - t_start, cancel.is_set(), user_text[:200])
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
        _sch = "https" if request.headers.get("X-Forwarded-Proto", request.scheme) == "https" else "http"
        sess.vision_url = _env("XIAOZHI_VISION_URL") or f"{_sch}://{request.host}/xiaozhi/vision/explain"      # 주소가 잘못 만들어지면 환경변수로 직접 지정
        with _SESSIONS_LOCK:
            _SESSIONS.append(sess)
        try:
            while True:
                msg = ws.receive(timeout=60)
                if msg is None:
                    continue
                if isinstance(msg, (bytes, bytearray)):
                    sess.n_audio = getattr(sess, "n_audio", 0) + 1
                    sess.last_audio_t = time.monotonic()
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
            _RESUME[device_id] = {"t": time.monotonic(), "turns": list(sess.turns[-MAX_TURNS_KEPT:])}
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
            log.info("[xiaozhi] 웹 상태 확인: 연결된 기기 없음")
            return jsonify({"connected": False})
        log.info("[xiaozhi] 웹 상태 확인: 연결됨 busy=%s", bool(sess.busy))
        return jsonify({"connected": True, "busy": bool(sess.busy), "asleep": False})      # asleep은 예전 웹 화면 호환용 (잠든 모드가 없어졌다)

    @app.route("/xiaozhi/mute", methods=["GET", "POST"])
    @app.route("/xiaozhi/unmute", methods=["GET", "POST"])
    def xz_stick_mute():
        """M5Stick이 버튼을 누르면 /xiaozhi/mute, 떼면 /xiaozhi/unmute 를 부른다 (?key=XIAOZHI_KEY 또는 X-Xiaozhi-Key 헤더).
        누르는 동안 스택챈 마이크 소리를 서버에서 버려서, 옆에서 Stick에 하는 말을 스택챈이 듣지 않게 한다."""
        given = request.headers.get("X-Xiaozhi-Key") or request.args.get("key", "")
        if not hmac.compare_digest(given.encode(), XZ_KEY.encode()):
            return jsonify({"error": "unauthorized"}), 401
        on = not request.path.rstrip("/").endswith("/unmute")
        with _SESSIONS_LOCK:
            live = [x for x in _SESSIONS if not x.closed]
        dev = request.args.get("device", "").strip().lower()      # 선택: 스택챈의 Device-Id(MAC). 주면 그 기기만 뮤트한다 (기기가 여러 대일 때)
        if dev:
            live = [x for x in live if (x.device_id or "").lower() == dev]
        for x in live:
            x.set_stick_mute(on)
        return jsonify({"ok": True, "muted": on, "devices": len(live)})

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
            log.warning("[xiaozhi] 웹 대답 거절: 기기가 다른 대답을 하는 중 (tid=%s)", tid)
            return jsonify({"error": "busy"}), 409
        return jsonify({"ok": True})

    @app.get("/xiaozhi/test")
    def xz_test():
        """브라우저에서 기기를 직접 시험해 보는 주소 (키 필요).
        /xiaozhi/test?key=KEY&emotion=sleepy      표정 바꾸기 (이름 확인용)
        /xiaozhi/test?key=KEY&pan=20&tilt=-10     고개 움직이기 (pan -70~70, tilt -35~35, dur=ms)
        /xiaozhi/test?key=KEY&center=1            고개 정면
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
            sess._head_raw(pan, tilt, dur)      # [정면 맞추기] move_head는 CMD OFF라 아무 일도 안 해서 직접 보낸다
            done.append(f"head pan={pan} tilt={tilt} dur={dur}")
        if a.get("center"):
            sess.has_robot = True
            sess.face_front()      # [정면 맞추기] center_head는 CMD OFF
            done.append("center")
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
        return jsonify({"sent": done or ["(할 일이 없어요: emotion, pan/tilt, center, volume, status, tone 중 하나를 붙이세요)"], "devices": len(live)})


    # ---------- 카메라 화면 (/xiaozhi/cam/) ----------
    # 기기의 사진 도구(self.camera.take_photo)를 MCP로 호출하면, 기기가 찍은 JPEG를 위 vision 주소로 올려 보낸다.
    # 그걸 받아 두었다가 웹 화면에 보여 준다. 영상이 아니라 몇 초 간격의 사진이다.
    def _cam_key_ok():
        return hmac.compare_digest(request.args.get("key", "").encode(), XZ_KEY.encode())

    def _cam_status(sess=None):
        with _CAM_LOCK:
            n, ts, size, dev = _CAM["n"], _CAM["ts"], len(_CAM["img"] or b""), _CAM["device"]
        return {"n": n, "age": (round(time.time() - ts, 1) if ts else None), "bytes": size, "device": dev,
                "connected": sess is not None, "tool": _cam_tool(sess) if sess else ""}

    def _cam_tool(sess):
        want = _env("XIAOZHI_CAM_TOOL")
        if want:
            return want
        names = [n for n in (getattr(sess, "_tool_names", None) or []) if n]
        if not names:       # 재접속 직후라 도구 목록을 아직 못 받았을 수 있다: 스택찬이 가진 기본 이름으로 바로 시도한다
            return "self.camera.take_photo"
        for n in names:
            if "take_photo" in n:
                return n
        for n in names:
            if "camera" in n.lower():
                return n
        return ""

    @app.route("/xiaozhi/vision/explain", methods=["POST"])
    def xz_vision():
        log.info("[xiaozhi] 카메라 업로드 요청 도착 (%s, %s바이트)", request.content_type, request.content_length)
        device_id = request.headers.get("Device-Id", "")
        token = request.headers.get("Authorization", "").removeprefix("Bearer ").strip()
        if not (_ok_device(device_id) and hmac.compare_digest(token.encode(), _device_token(device_id).encode())):
            log.warning("[xiaozhi] 카메라 사진 업로드 인증 실패 device=%r", device_id)
            return jsonify({"success": False, "message": "unauthorized"}), 401
        data = b""
        for f in request.files.values():
            data = f.read()
            break
        if not data and (request.mimetype or "").startswith("image/"):
            data = request.get_data()
        if not data or len(data) > 4 * 1024 * 1024 or not (data[:2] == b"\xff\xd8" or data[:4] == b"\x89PNG"):
            log.warning("[xiaozhi] 카메라 사진이 이상합니다 (%d바이트, 앞부분=%r)", len(data), data[:8])
            return jsonify({"success": False, "message": "bad image"}), 400
        with _CAM_LOCK:
            _CAM.update(img=data, ts=time.time(), device=device_id, n=_CAM["n"] + 1,
                        mime=("image/png" if data[:4] == b"\x89PNG" else "image/jpeg"))
        log.info("[xiaozhi] 카메라 사진 받음 device=%s %d바이트 (#%d)", device_id, len(data), _CAM["n"])
        return jsonify({"success": True, "result": "사진을 받았어요."})

    @app.get("/xiaozhi/vision/explain")
    def xz_vision_ping():      # 브라우저에서 열어 보면 이 주소가 밖에서 닿는지 확인할 수 있다 (업로드는 POST만 받는다)
        return jsonify({"ok": True, "hint": "POST로 사진을 받는 주소예요"})

    @app.get("/xiaozhi/cam/")
    def xz_cam_page():
        if not _cam_key_ok():
            return jsonify({"error": "unauthorized"}), 401
        return Response(_CAM_HTML, mimetype="text/html")

    @app.get("/xiaozhi/cam/status")
    def xz_cam_status():
        if not _cam_key_ok():
            return jsonify({"error": "unauthorized"}), 401
        return jsonify(_cam_status(_live_session()))

    @app.get("/xiaozhi/cam/latest.jpg")
    def xz_cam_latest():
        if not _cam_key_ok():
            return jsonify({"error": "unauthorized"}), 401
        with _CAM_LOCK:
            img, mime = _CAM["img"], _CAM["mime"]
        if not img:
            return jsonify({"error": "아직 받은 사진이 없어요"}), 404
        return Response(img, mimetype=mime, headers={"Cache-Control": "no-store"})

    @app.route("/xiaozhi/cam/shoot", methods=["GET", "POST"])
    def xz_cam_shoot():
        if not _cam_key_ok():
            return jsonify({"error": "unauthorized"}), 401
        sess = _live_session()
        if not sess:
            return jsonify({"error": "연결된 기기가 없어요 (스택찬이 서버에 접속해 있어야 합니다)"}), 404
        tool = _cam_tool(sess)
        if not tool:
            return jsonify({"error": "기기에서 카메라 도구를 못 찾았어요. 서버 로그의 '기기 MCP 도구' 줄을 확인하고, 이름을 XIAOZHI_CAM_TOOL 환경변수에 넣어 주세요.",
                            "tools": [n for n in (getattr(sess, "_tool_names", None) or []) if n]}), 409
        if not _CAM_SHOOT.acquire(blocking=False):
            return jsonify({"error": "이미 찍는 중이에요"}), 409
        try:
            n0 = _CAM["n"]
            log.info("[xiaozhi] 카메라 촬영 요청 보냄 tool=%s (연결 %.0f초째)", tool, time.monotonic() - sess.t0)
            sess._mcp_call("tools/call", {"name": tool, "arguments": {"question": "사진을 찍어서 서버로 보내줘"}}, quiet=True)
            t_end = time.monotonic() + 20
            while time.monotonic() < t_end:
                if _CAM["n"] > n0:
                    return jsonify(_cam_status(sess))
                if sess.closed:
                    log.warning("[xiaozhi] 촬영 요청 뒤에 기기 연결이 끊겼습니다 (기기가 재시작됐을 수 있어요)")
                    return jsonify({"error": "촬영 중에 기기 연결이 끊겼어요 (기기가 다시 시작됐을 수 있어요)"}), 502
                time.sleep(0.2)
            return jsonify({"error": "사진이 오지 않았어요. 기기가 vision 주소를 못 받았거나(펌웨어 확인), 업로드에 실패했을 수 있어요. 서버 로그를 확인하세요."}), 504
        finally:
            _CAM_SHOOT.release()

    # ---------- 실시간 영상 (/xiaozhi/cam/stream) ----------
    # 기기 펌웨어(hal_ws_avatar.cpp)가 STACKCHAN_SERVER_URL + "/stackChan/ws?deviceType=StackChan" 으로 접속해서
    # [타입 1바이트][길이 4바이트 빅엔디안][내용] 패킷을 주고받는다. 0x05 = 영상 시작, 0x06 = 중지, 0x02 = JPEG 프레임.
    # 기기는 Authorization 헤더로 고정 문자열만 보내서 인증이 안 되므로, 주소 경로에 토큰을 넣어 접속을 걸러 낸다.
    def _live_token():
        return hmac.new(XZ_KEY.encode(), b"stackchan-live-v1", hashlib.sha256).hexdigest()[:24]

    def _live_pkt(t, payload=b""):
        return bytes([t]) + len(payload).to_bytes(4, "big") + payload

    @sock.route("/xz/<tok>/stackChan/ws")
    def xz_live_ws(ws, tok):
        # 정식 토큰(live-status의 device_url에 나오는 값)과, 펌웨어에 XIAOZHI_KEY를 그대로 넣은 경우 둘 다 받는다
        if not (hmac.compare_digest(tok.encode(), _live_token().encode())
                or hmac.compare_digest(tok.encode(), XZ_KEY.encode())):
            log.warning("[xiaozhi-live] 영상 접속 거부 (주소의 토큰이 달라요) 받은 토큰 길이=%d", len(tok))
            ws.close(reason=1008, message="unauthorized")
            return
        log.info("[xiaozhi-live] 영상 기기 접속")
        with _LIVE_COND:
            _LIVE["connected"] = True
            _LIVE_COND.notify_all()
        want, last_ping = None, 0.0
        try:
            while True:
                need = _LIVE["viewers"] > 0         # 화면을 보는 사람이 있을 때만 기기가 영상을 보내게 한다
                if need != want:
                    ws.send(_live_pkt(0x05 if need else 0x06))
                    want = need
                    log.info("[xiaozhi-live] 기기에 영상 %s 보냄", "시작" if need else "중지")
                if time.monotonic() - last_ping > 5:
                    ws.send(_live_pkt(0x10))        # HeartbeatPing: 기기가 연결 끊김 경고를 내지 않게 한다
                    last_ping = time.monotonic()
                msg = ws.receive(timeout=1)
                if msg is None or not isinstance(msg, (bytes, bytearray)):
                    continue
                if len(msg) >= 5 and msg[0] == 0x02:
                    n = int.from_bytes(msg[1:5], "big")
                    jpg = bytes(msg[5:5 + n])
                    if jpg[:2] == b"\xff\xd8":
                        with _LIVE_COND:
                            _LIVE.update(jpg=jpg, ts=time.time(), seq=_LIVE["seq"] + 1, frames=_LIVE["frames"] + 1)
                            _LIVE_COND.notify_all()
        except Exception as e:      # ConnectionClosed 포함
            log.info("[xiaozhi-live] 영상 기기 연결 종료 (%s)", type(e).__name__)
        finally:
            with _LIVE_COND:
                _LIVE["connected"] = False
                _LIVE_COND.notify_all()

    @app.get("/xiaozhi/cam/stream")
    def xz_cam_stream():
        if not _cam_key_ok():
            return jsonify({"error": "unauthorized"}), 401

        def gen():
            t_end = time.monotonic() + 120          # 화면이 주기적으로 다시 연결한다 (닫힌 화면이 오래 남지 않게)
            with _LIVE_COND:
                _LIVE["viewers"] += 1
                last = _LIVE["seq"] if _LIVE["jpg"] is None else -1      # 프레임이 아직 없으면 새 프레임이 올 때까지 기다린다 (헛돌지 않게)
            try:
                while time.monotonic() < t_end:
                    with _LIVE_COND:
                        _LIVE_COND.wait_for(lambda: _LIVE["seq"] != last, timeout=2)
                        jpg, seq = _LIVE["jpg"], _LIVE["seq"]
                    if jpg is None or seq == last:
                        continue
                    last = seq
                    yield (b"--frame\r\nContent-Type: image/jpeg\r\nContent-Length: %d\r\n\r\n" % len(jpg)) + jpg + b"\r\n"
            finally:
                with _LIVE_COND:
                    _LIVE["viewers"] = max(0, _LIVE["viewers"] - 1)

        return Response(gen(), mimetype="multipart/x-mixed-replace; boundary=frame",
                        headers={"Cache-Control": "no-store", "X-Accel-Buffering": "no"})

    @app.get("/xiaozhi/cam/live-status")
    def xz_cam_live_status():
        if not _cam_key_ok():
            return jsonify({"error": "unauthorized"}), 401
        _sch = "https" if request.headers.get("X-Forwarded-Proto", request.scheme) == "https" else "http"
        with _LIVE_COND:
            d = {"connected": _LIVE["connected"], "frames": _LIVE["frames"], "viewers": _LIVE["viewers"],
                 "age": (round(time.time() - _LIVE["ts"], 1) if _LIVE["ts"] else None)}
        d["device_url"] = f"{_sch}://{request.host}/xz/{_live_token()}"      # 펌웨어 CONFIG_STACKCHAN_SERVER_URL 에 넣을 값
        return jsonify(d)

    log.info("[xiaozhi] 스택찬 브리지 켜짐 - OTA: /xiaozhi/ota/?key=...  WS: /xiaozhi/v1/  (모드=%s, VAD=%s)",
             ("live→pipe" if LIVE_OUT_PIPE else "live") if _live_available() else "pipe", "webrtc" if webrtcvad else "없음")
    if not webrtcvad:
        log.error("[xiaozhi] webrtcvad 모듈이 없어 말 끝 감지가 동작하지 않습니다 (pip install webrtcvad)")
    return True


_SESSIONS = []           # 지금 연결된 기기들 (테스트 주소가 쓴다)
_SESSIONS_LOCK = threading.Lock()


def play_sound(path: str) -> bool:
    """서버의 소리 파일(mp3)을 연결된 기기 스피커로 재생한다. 연결된 기기가 없거나 기기가 말하는 중이면 False (호출한 쪽이 다른 방법으로 대신한다)."""
    with _SESSIONS_LOCK:
        live = [x for x in _SESSIONS if not x.closed]
    if not live:
        return False
    return live[-1].play_sound(path)


_CAM = {"img": None, "mime": "image/jpeg", "ts": 0.0, "n": 0, "device": ""}      # 마지막으로 받은 카메라 사진
_CAM_LOCK = threading.Lock()
_CAM_SHOOT = threading.Lock()

# 실시간 영상(기기가 /xz/<토큰>/stackChan/ws 로 보내는 JPEG 프레임) 상태
_LIVE = {"jpg": None, "seq": 0, "ts": 0.0, "connected": False, "frames": 0, "viewers": 0}
_LIVE_COND = threading.Condition()

_CAM_HTML = """<!doctype html>
<html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>스택찬 카메라</title>
<style>
  :root{--bg:#14121a;--card:#201c2b;--tx:#f2ece4;--dim:#a79fb3;--ac:#c07b7f;--ok:#7fc79a}
  *{box-sizing:border-box} body{margin:0;background:var(--bg);color:var(--tx);font:15px/1.5 system-ui,sans-serif;padding:14px;max-width:560px;margin:auto}
  h1{font-size:18px;margin:4px 0 10px}
  #view{background:#000;border-radius:14px;overflow:hidden;aspect-ratio:4/3;display:flex;align-items:center;justify-content:center}
  #view img{width:100%;height:100%;object-fit:contain;display:none}
  #ph{color:var(--dim)}
  #lview{background:#000;border-radius:14px;overflow:hidden;aspect-ratio:4/3;display:flex;align-items:center;justify-content:center;position:relative}
  #lview img{width:100%;height:100%;object-fit:contain;display:none}
  #lph{color:var(--dim);padding:0 12px;text-align:center}
  #lst{color:var(--dim);font-size:13px;margin:8px 2px;min-height:20px}
  details{color:var(--dim);font-size:12px;margin:6px 2px;word-break:break-all}
  #st{color:var(--dim);font-size:13px;margin:8px 2px;min-height:20px}
  #st.err{color:#f0a0a0}
  .row{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin:8px 0}
  button,select{background:var(--card);color:var(--tx);border:1px solid #3a3347;border-radius:10px;padding:10px 14px;font-size:15px}
  button.pri{background:var(--ac);border-color:var(--ac);color:#fff} button:disabled{opacity:.5}
  .box{background:var(--card);border-radius:14px;padding:12px;margin-top:12px}
  .box label{display:block;color:var(--dim);font-size:13px;margin-top:6px}
  input[type=range]{width:100%}
</style></head><body>
<h1>스택찬 카메라</h1>
<div id="lview"><img id="live" alt="실시간 영상"><span id="lph">영상 기기 연결을 기다리는 중…</span></div>
<div id="lst"></div>
<details><summary>기기 설정 주소 (펌웨어에 넣는 값)</summary><span id="lurl">-</span></details>
<div id="view"><span id="ph">아직 받은 사진이 없어요</span><img id="img" alt="스택찬 카메라 사진"></div>
<div id="st"></div>
<div class="row">
  <button class="pri" id="shoot">지금 찍기</button>
  <select id="every"><option value="0">자동 촬영 끔</option><option value="3">3초마다</option><option value="5">5초마다</option><option value="10">10초마다</option><option value="30">30초마다</option></select>
</div>
<div class="box">
  <b>고개 움직이기</b>
  <label>좌우 <span id="pv">0</span></label><input type="range" id="pan" min="-70" max="70" value="0">
  <label>상하 <span id="tv">0</span></label><input type="range" id="tilt" min="-35" max="35" value="0">
  <div class="row"><button id="mv">움직이기</button><button id="ct">정면</button></div>
</div>
<script>
const KEY = new URLSearchParams(location.search).get('key') || '';
const $ = (i) => document.getElementById(i);
const q = (path, extra) => path + '?key=' + encodeURIComponent(KEY) + (extra || '');
let timer = null, busy = false, lastN = 0;
function say(t, err){ $('st').textContent = t; $('st').className = err ? 'err' : ''; }
function show(n){ lastN = n; $('img').src = q('/xiaozhi/cam/latest.jpg', '&t=' + Date.now()); $('img').style.display = 'block'; $('ph').style.display = 'none'; }
async function shoot(){
  if (busy) return; busy = true; $('shoot').disabled = true; say('찍는 중…');
  try {
    const r = await fetch(q('/xiaozhi/cam/shoot'), {method: 'POST'}); const d = await r.json();
    if (!r.ok) { say(d.error || '실패했어요', true); stopAuto(); }
    else { show(d.n); say('방금 찍었어요 (' + new Date().toLocaleTimeString() + ')'); }
  } catch (e) { say('서버에 연결하지 못했어요', true); stopAuto(); }
  busy = false; $('shoot').disabled = false;
}
function stopAuto(){ if (timer) { clearTimeout(timer); timer = null; } $('every').value = '0'; }
function loop(){
  const s = +$('every').value; if (!s) return;
  timer = setTimeout(async () => { if (!document.hidden) await shoot(); if (+$('every').value) loop(); }, s * 1000);
}
$('shoot').onclick = shoot;
$('every').onchange = () => { if (timer) { clearTimeout(timer); timer = null; } if (+$('every').value) { shoot().then(loop); } };
$('pan').oninput = () => { $('pv').textContent = $('pan').value; };
$('tilt').oninput = () => { $('tv').textContent = $('tilt').value; };
$('mv').onclick = () => fetch(q('/xiaozhi/test', '&pan=' + $('pan').value + '&tilt=' + $('tilt').value + '&dur=600'));
$('ct').onclick = () => { $('pan').value = 0; $('tilt').value = 0; $('pv').textContent = '0'; $('tv').textContent = '0'; fetch(q('/xiaozhi/test', '&center=1')); };
function startLive(){ if (document.hidden) return; $('live').src = q('/xiaozhi/cam/stream', '&t=' + Date.now()); }
function stopLive(){ $('live').removeAttribute('src'); }
document.addEventListener('visibilitychange', () => { if (document.hidden) stopLive(); else startLive(); });
async function liveStatus(){
  try {
    const r = await fetch(q('/xiaozhi/cam/live-status')); const d = await r.json();
    if (d.error) { $('lst').textContent = '주소 뒤에 ?key=... 가 맞는지 확인하세요'; return; }
    $('lurl').textContent = d.device_url;
    const fresh = d.age !== null && d.age < 5;
    $('live').style.display = fresh ? 'block' : 'none';
    $('lph').style.display = fresh ? 'none' : 'block';
    $('lph').textContent = d.connected ? '기기에서 영상을 기다리는 중…' : '영상 기기 연결을 기다리는 중…';
    $('lst').textContent = (d.connected ? '영상 기기 연결됨' : '영상 기기 연결 안 됨') + ' · 받은 프레임 ' + d.frames + (d.age !== null ? ' · 마지막 ' + d.age + '초 전' : '');
  } catch (e) { $('lst').textContent = '서버에 연결하지 못했어요'; }
}
startLive(); setInterval(startLive, 110000); liveStatus(); setInterval(liveStatus, 2000);
fetch(q('/xiaozhi/cam/status')).then(r => r.json()).then(d => {
  if (d.error) { say('주소 뒤에 ?key=... 가 맞는지 확인하세요', true); return; }
  if (d.n) { show(d.n); say('마지막 사진: ' + d.age + '초 전'); }
  else say(d.connected ? '기기가 연결되어 있어요. 「지금 찍기」를 눌러 보세요.' : '기기가 서버에 연결되어 있지 않아요', !d.connected);
});
</script></body></html>
"""


def _which(name):
    from shutil import which
    return which(name)
