"""
db_schema.py - 새 PostgreSQL에서 token_server.py가 쓰는 테이블을 만들어 주는 부트스트랩

token_server.py는 원래 태연봇(taeyeon_bot.py)의 init_db()가 만든 테이블을 가져다 쓰는 구조라서,
태연봇과 연결되지 않은 새 DB에서는 conversations/users 같은 테이블이 아예 없다. 특히
_load_owner_db_data()는 독립 페르소나 모드에서도 아래 테이블들을 한 번에 읽고 개별 예외 처리가 없어서,
하나라도 없으면 기억/요약 컨텍스트 전체가 로드되지 않는다. 그래서 '쓰이는 것만'이 아니라 전부 만든다
(태연 전용 테이블은 비어 있는 채로 둔다).

이 파일의 컬럼은 token_server.py가 실제로 실행하는 SQL(43개)을 기준으로 정했고,
test_db_schema.py가 그 SQL 전부를 실제 Postgres에 돌려서 맞는지 확인한다.

사용: token_server.py 시작 부분(대화 기록 함수/스레드가 시작되기 전)에서 한 번 호출.
    import db_schema; db_schema.ensure_schema(DATABASE_URL, OWNER_USER_ID)
모든 문장이 IF NOT EXISTS라 여러 번 실행해도, 서버가 여러 개 동시에 떠도 안전하다. 실패해도 서버는 그대로 뜬다.
"""
import logging
import os

try:
    import psycopg2
except ImportError:
    psycopg2 = None

log = logging.getLogger("db_schema")

_LOCK_KEY = 7316001  # 동시에 두 인스턴스가 CREATE TABLE을 겹쳐 실행하는 것을 막는 advisory lock 번호

SCHEMA = [
    # ----- 대화 기록 (음성 대화가 저장되는 곳) -----
    """CREATE TABLE IF NOT EXISTS users (
        user_id BIGINT PRIMARY KEY,
        chat_id BIGINT,
        affinity INTEGER NOT NULL DEFAULT 0,
        last_message_at TIMESTAMP,
        emotion_label TEXT NOT NULL DEFAULT 'neutral',
        emotion_intensity INTEGER NOT NULL DEFAULT 0,
        emotion_updated_at TIMESTAMP,
        created_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    """CREATE TABLE IF NOT EXISTS conversations (
        id BIGSERIAL PRIMARY KEY,
        user_id BIGINT NOT NULL,
        role TEXT NOT NULL,
        content TEXT NOT NULL,
        created_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    "CREATE INDEX IF NOT EXISTS idx_conversations_user_created ON conversations (user_id, created_at)",
    """CREATE TABLE IF NOT EXISTS conversation_summary (
        user_id BIGINT PRIMARY KEY,
        summary_text TEXT NOT NULL DEFAULT '',
        updated_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    """CREATE TABLE IF NOT EXISTS daily_summary (
        user_id BIGINT NOT NULL,
        summary_date DATE NOT NULL,
        summary_text TEXT NOT NULL,
        covered_until TIMESTAMP,
        is_final BOOLEAN NOT NULL DEFAULT FALSE,
        updated_at TIMESTAMP NOT NULL DEFAULT NOW(),
        PRIMARY KEY (user_id, summary_date)
    )""",
    # ----- 기억 / 약속 / 사실 -----
    """CREATE TABLE IF NOT EXISTS memorable_moments (
        id BIGSERIAL PRIMARY KEY,
        user_id BIGINT NOT NULL,
        topic TEXT NOT NULL,
        detail TEXT,
        created_at TIMESTAMP NOT NULL DEFAULT NOW(),
        embedding REAL[],
        emotion_label TEXT,
        emotion_intensity INTEGER,
        strength REAL NOT NULL DEFAULT 1.0,
        last_recalled TIMESTAMP,
        recall_count INTEGER NOT NULL DEFAULT 0
    )""",
    # 이미 (예전 방식으로) 만들어진 memorable_moments가 있어도 인출용 컬럼이 빠지지 않게
    """ALTER TABLE memorable_moments
        ADD COLUMN IF NOT EXISTS embedding REAL[],
        ADD COLUMN IF NOT EXISTS emotion_label TEXT,
        ADD COLUMN IF NOT EXISTS emotion_intensity INTEGER,
        ADD COLUMN IF NOT EXISTS strength REAL NOT NULL DEFAULT 1.0,
        ADD COLUMN IF NOT EXISTS last_recalled TIMESTAMP,
        ADD COLUMN IF NOT EXISTS recall_count INTEGER NOT NULL DEFAULT 0""",
    "CREATE INDEX IF NOT EXISTS idx_moments_user_created ON memorable_moments (user_id, created_at)",
    """CREATE TABLE IF NOT EXISTS user_promises (
        id BIGSERIAL PRIMARY KEY,
        user_id BIGINT NOT NULL,
        promise_text TEXT NOT NULL,
        created_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    "CREATE INDEX IF NOT EXISTS idx_promises_user_created ON user_promises (user_id, created_at)",
    """CREATE TABLE IF NOT EXISTS user_facts (
        user_id BIGINT NOT NULL,
        fact_key TEXT NOT NULL,
        fact_value TEXT,
        updated_at TIMESTAMP NOT NULL DEFAULT NOW(),
        PRIMARY KEY (user_id, fact_key)
    )""",
    """CREATE TABLE IF NOT EXISTS user_facts_pending (
        user_id BIGINT PRIMARY KEY,
        marked_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    # ----- 태연 전용 테이블: 독립 페르소나에선 항상 비어 있지만, 읽는 쿼리가 있어서 존재는 해야 한다 -----
    """CREATE TABLE IF NOT EXISTS taeyeon_custom_prompt (
        id BIGSERIAL PRIMARY KEY,
        prompt_text TEXT,
        created_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    """CREATE TABLE IF NOT EXISTS taeyeon_extra_info (
        id BIGSERIAL PRIMARY KEY,
        info_text TEXT,
        created_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    """CREATE TABLE IF NOT EXISTS owner_profile_qna (
        id BIGSERIAL PRIMARY KEY,
        user_id BIGINT NOT NULL,
        category TEXT,
        question TEXT,
        answer TEXT,
        created_at TIMESTAMP NOT NULL DEFAULT NOW()
    )""",
    """CREATE TABLE IF NOT EXISTS owner_daily_fortune (
        fortune_date DATE PRIMARY KEY,
        fortune_text TEXT
    )""",
    """CREATE TABLE IF NOT EXISTS owner_fortune_entries (
        id BIGSERIAL PRIMARY KEY,
        entry_text TEXT,
        last_shown_at TIMESTAMP,
        active BOOLEAN NOT NULL DEFAULT TRUE
    )""",
    """CREATE TABLE IF NOT EXISTS taeyeon_schedule (
        id BIGSERIAL PRIMARY KEY,
        event_text TEXT,
        category TEXT,
        schedule_date DATE,
        start_time TIME,
        end_time TIME
    )""",
    """CREATE TABLE IF NOT EXISTS daily_taeyeon_news (
        news_date DATE PRIMARY KEY,
        news_text TEXT
    )""",
]


def ensure_schema(database_url, owner_user_id=None, sslmode=None) -> bool:
    """테이블을 (없으면) 만들고, OWNER 사용자 행을 심는다. 성공하면 True. 실패해도 예외를 던지지 않는다."""
    if not database_url or psycopg2 is None:
        return False
    sslmode = sslmode or os.environ.get("DB_SSLMODE", "require")     # token_server.py의 다른 연결들과 같은 기본값
    try:
        conn = psycopg2.connect(database_url, sslmode=sslmode, connect_timeout=10)
    except Exception as e:
        log.warning("[db_schema] DB 연결 실패 - 테이블 준비를 건너뜁니다: %s", e)
        return False
    try:
        cur = conn.cursor()
        cur.execute("SELECT pg_advisory_xact_lock(%s)", (_LOCK_KEY,))
        for stmt in SCHEMA:
            cur.execute(stmt)
        if owner_user_id is not None:
            # token_server.py는 users를 UPDATE만 하고 INSERT는 하지 않는다(원래는 태연봇이 행을 만들어 줬다).
            # 행이 없으면 last_message_at이 영영 갱신되지 않으니 OWNER 행을 심어 둔다.
            cur.execute(
                "INSERT INTO users (user_id, chat_id) VALUES (%s, %s) ON CONFLICT (user_id) DO NOTHING",
                (owner_user_id, owner_user_id),
            )
        conn.commit()
        cur.close()
        log.info("[db_schema] 테이블 준비 완료 (owner_user_id=%s)", owner_user_id)
        return True
    except Exception as e:
        conn.rollback()
        log.warning("[db_schema] 테이블 준비 실패 - 서버는 계속 뜹니다: %s", e)
        return False
    finally:
        conn.close()
