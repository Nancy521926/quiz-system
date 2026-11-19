# -*- coding: utf-8 -*-
"""青简 · 智能刷题系统 — 本地 Flask 后端

启动：py -3 server.py    然后打开 http://127.0.0.1:8766/
功能：题库管理（JSON / 纯文本 / CSV / Word 导入）、大模型解析代理、静态页面。
"""
import csv as csvmod
import hashlib
import hmac
import io
import json
import os
import re
import secrets
import smtplib
import sqlite3
import ssl
import sys
import time
import unicodedata
from datetime import datetime, timedelta
from email.message import EmailMessage
from email.utils import formataddr
from pathlib import Path

import requests
from flask import (Flask, g, has_request_context, jsonify, request,
                   send_from_directory, session)
from werkzeug.security import check_password_hash, generate_password_hash

BASE_DIR = Path(__file__).resolve().parent
BANK_DIR = BASE_DIR / "题库"
STATIC_DIR = BASE_DIR / "static"
CONFIG_PATH = BASE_DIR / "config.json"
MAIL_PATH = BASE_DIR / "smtp.json"
DB_PATH = BASE_DIR / "quiz.db"
SECRET_PATH = BASE_DIR / "secret.key"
BANK_DIR.mkdir(parents=True, exist_ok=True)
STATIC_DIR.mkdir(parents=True, exist_ok=True)


def load_secret_key():
    """会话签名密钥：首次启动生成，落本地 secret.key，重启后登录态不失效。"""
    try:
        key = SECRET_PATH.read_text(encoding="utf-8").strip()
        if key:
            return key
    except OSError:
        pass
    key = secrets.token_hex(32)
    try:
        SECRET_PATH.write_text(key, encoding="utf-8")
    except OSError:
        pass
    return key


app = Flask(__name__, static_folder=None)
try:
    app.json.ensure_ascii = False
except Exception:
    pass
app.config["MAX_CONTENT_LENGTH"] = 30 * 1024 * 1024
app.config["SECRET_KEY"] = load_secret_key()
app.config["SESSION_COOKIE_HTTPONLY"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(days=30)

PORT = 8766

PRESETS = {
    "deepseek": {
        "label": "DeepSeek 官方",
        "base_url": "https://api.deepseek.com/v1",
        "model": "deepseek-chat",
    },
    "local": {
        "label": "本地 Ollama（免 Key）",
        "base_url": "http://127.0.0.1:11434/v1",
        "model": "qwen3.8-27b:q2",
    },
    "custom": {"label": "自定义", "base_url": "", "model": ""},
}

DEFAULT_CONFIG = {
    "preset": "local",
    "base_url": PRESETS["local"]["base_url"],
    "api_key": "",
    "model": PRESETS["local"]["model"],
}

SYSTEM_PROMPT = (
    "你是题库解析助手，面向国网招聘考试与计算机专业题库。"
    "输出简洁准确的解析：考点 + 关键知识点 + 为什么选该答案 + 易错点，不超过150字。"
    "直接输出正文，不要复述题干，不要使用 Markdown 标题。"
)

# ---------------------------------------------------------------------------
# 通用文本工具
# ---------------------------------------------------------------------------

def norm(s):
    """只规整全角字母/数字，保留中文标点，避免题干排版被破坏。"""
    if s is None:
        return ""
    s = str(s).replace("　", " ")
    table = {}
    for ch in s:
        o = ord(ch)
        if 0xFF10 <= o <= 0xFF19 or 0xFF21 <= o <= 0xFF3A or 0xFF41 <= o <= 0xFF5A:
            table[o] = o - 0xFEE0
    if table:
        s = s.translate(table)
    s = s.replace("．", ".")
    return s.strip()


def collapse(s):
    return re.sub(r"\s+", " ", norm(s)).strip()


QNUM_RE = re.compile(r"^\s*(?:第\s*)?(\d{1,4})\s*(?:题)?\s*[.．、)）:：]\s*(?!\d)")
SECTION_RE = re.compile(
    r"^\s*(?:[一二三四五六七八九十百零]{1,4}\s*[、.．]|第\s*[一二三四五六七八九十\d]{1,4}\s*[部分章节]|"
    r"(?:单项选择|多项选择|单选|多选|判断)题?\s*$)"
)
ANS_RE = re.compile(r"(?:【|\[)?\s*(?:正确|参考)?\s*答\s*案\s*(?:】|\])?\s*[:：]?")
EXP_RE = re.compile(r"(?:【|\[)?\s*(?:答案)?\s*解\s*析\s*(?:】|\])?\s*[:：]?")
OPT_RE = re.compile(r"(?:(?<=[\s(（:：、,，;；。])|^)([A-H])\s*[.．、)）]\s*", re.M)
TABLE_OPT_RE = re.compile(r"^\s*([A-H])\s*[.、)）:：]\s*(.+)$")


def judge_letter(s):
    t = norm(s)
    if not t:
        return ""
    if re.search(r"不正确|不对|错误|错|×|✗|否定|false|^F$", t, re.I):
        return "B"
    if re.search(r"正确|对|√|✓|肯定|true|^T$", t, re.I):
        return "A"
    return ""


def ans_letters(s):
    letters = re.findall(r"[A-H]", norm(s).upper())
    return "".join(dict.fromkeys(letters))


def find_answer_marker(text):
    best = None
    for m in ANS_RE.finditer(text):
        tail = text[m.end():m.end() + 60]
        if re.search(r"[A-H]|对|错|正确|错误|√|×", tail):
            best = m
    return best


# ---------------------------------------------------------------------------
# 题库文件
# ---------------------------------------------------------------------------

def safe_bank_id(name):
    name = re.sub(r'[\\/:*?"<>|\r\n\t]', "", norm(name)).strip(" .")
    name = re.sub(r"\s+", " ", name)
    return name[:80] or ("题库" + datetime.now().strftime("%Y%m%d%H%M%S"))


def safe_group_name(name):
    g = re.sub(r'[\\/:*?"<>|\r\n\t]', "", norm(name)).strip(" .")
    g = re.sub(r"\s+", " ", g)[:40]
    return "" if g in ("", "未分组") else g


def group_dir(group):
    return BANK_DIR / group if group else BANK_DIR


def rel_bank_id(path):
    return path.relative_to(BANK_DIR).with_suffix("").as_posix()


def group_of_path(path):
    parent = path.relative_to(BANK_DIR).parent.as_posix()
    return "" if parent == "." else parent


def unique_bank_id(base, group=""):
    folder = group_dir(group)
    folder.mkdir(parents=True, exist_ok=True)
    bid = safe_bank_id(base)
    candidate = folder / (bid + ".json")
    if not candidate.exists():
        return rel_bank_id(candidate)
    i = 2
    while (folder / (f"{bid}-{i}.json")).exists():
        i += 1
    return rel_bank_id(folder / (f"{bid}-{i}.json"))


def bank_path(bank_id):
    if not bank_id or ".." in Path(bank_id).parts:
        return None
    p = (BANK_DIR / (bank_id + ".json")).resolve()
    try:
        p.relative_to(BANK_DIR.resolve())
    except ValueError:
        return None
    return p if p.exists() else None


def load_bank(bank_id):
    p = bank_path(bank_id)
    if not p:
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return None


def save_bank(bank_id, name, questions):
    path = BANK_DIR / (bank_id + ".json")
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "name": name or bank_id,
        "group": group_of_path(path),
        "questions": questions,
        "updated": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    }
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, path)


def bank_summary(path):
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None
    qs = data.get("questions") or []
    return {
        "id": rel_bank_id(path),
        "name": data.get("name") or path.stem,
        "group": group_of_path(path),
        "total": len(qs),
        "single": sum(1 for q in qs if q.get("type") == "single"),
        "multi": sum(1 for q in qs if q.get("type") == "multi"),
        "judge": sum(1 for q in qs if q.get("type") == "judge"),
        "exp": sum(1 for q in qs if (q.get("exp") or "").strip()),
        "updated": data.get("updated") or "",
    }


# ---------------------------------------------------------------------------
# 解析：纯文本 / CSV / Word / JSON → 统一题目
# ---------------------------------------------------------------------------

def split_blocks(text):
    blocks, cur = [], None
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            if cur is not None:
                cur.append("")
            continue
        if SECTION_RE.match(line):
            if cur is not None:
                blocks.append("\n".join(cur))
                cur = None
            continue
        m = QNUM_RE.match(line)
        if m:
            if cur is not None:
                blocks.append("\n".join(cur))
            cur = [QNUM_RE.sub("", line, count=1)]
        elif cur is not None:
            cur.append(line)
    if cur is not None:
        blocks.append("\n".join(cur))
    return [b for b in blocks if b.strip()]


def parse_options(body):
    matches, expected = [], ord("A")
    for m in OPT_RE.finditer(body):
        if ord(m.group(1)) == expected:
            matches.append(m)
            expected += 1
    if len(matches) < 2:
        return [], collapse(body)
    stem = collapse(body[:matches[0].start()])
    opts = []
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(body)
        opts.append({"k": m.group(1), "v": collapse(body[m.end():end])})
    return opts, stem


def parse_block(block):
    """一个题块 → raw dict（后续统一 finalize + 质检）。"""
    text = norm(block)
    m_ans = find_answer_marker(text)
    if m_ans:
        body = text[:m_ans.start()]
        answer_region = text[m_ans.end():]
    else:
        body, answer_region = text, ""
    m_exp = EXP_RE.search(answer_region)
    if m_exp:
        ans_part = answer_region[:m_exp.start()]
        exp = answer_region[m_exp.end():]
    else:
        ans_part, exp = answer_region, ""

    opts, stem = parse_options(body)
    letters = ans_letters(ans_part)
    truth = judge_letter(ans_part) if (not letters or not opts) else ""
    if opts and truth and not letters:
        for o in opts:
            if judge_letter(o["v"]) == truth:
                letters = o["k"]
                break
        if not letters and len(opts) == 2:
            letters = truth
    if truth and not letters:
        letters = truth

    block_type = ""
    if re.search(r"多\s*选|多项选择|多选题", text):
        block_type = "multi"
    elif re.search(r"判\s*断", text) and not opts:
        block_type = "judge"
    elif not opts and truth:
        block_type = "judge"
    elif (len(opts) == 2 and judge_letter(opts[0]["v"]) == "A"
          and judge_letter(opts[1]["v"]) == "B"):
        block_type = "judge"

    return {
        "stem": stem,
        "opts": opts,
        "ans": letters,
        "type": block_type,
        "exp": collapse(exp),
        "part": "",
    }


def parse_text_questions(text):
    blocks = split_blocks(norm(text))
    if not blocks:
        raise ValueError("没有识别到题目。纯文本要求每题以「数字.」或「数字、」开头，例如：1. 题干……")
    return [parse_block(b) for b in blocks], len(blocks)


def decode_bytes(data):
    for enc in ("utf-8-sig", "utf-8", "gb18030", "gbk"):
        try:
            return data.decode(enc)
        except Exception:
            continue
    return data.decode("utf-8", errors="replace")


def parse_csv_questions(text, delimiter=","):
    rows = list(csvmod.reader(io.StringIO(text), delimiter=delimiter))
    rows = [[norm(c) for c in r] for r in rows]
    rows = [r for r in rows if any(c for c in r)]
    if len(rows) < 2:
        raise ValueError("CSV 至少需要一行表头和一行数据。")

    header = [re.sub(r"\s+", "", c).upper() for c in rows[0]]

    def find_col(names):
        for i, h in enumerate(header):
            for n in names:
                if n.upper() in h:
                    return i
        return -1

    stem_i = -1
    for i, h in enumerate(header):
        if h in ("题干", "问题", "题目", "QUESTION", "STEM") or \
                h.startswith(("题干", "问题", "题目")) or h in ("QUESTIONSTEM",):
            stem_i = i
            break
    ans_i = find_col(["答案", "ANSWER", "ANS"])
    exp_i = find_col(["解析", "EXPLANATION", "EXP"])
    type_i = find_col(["题型", "类型", "TYPE"])
    part_i = find_col(["部分", "分类", "类别", "PART"])

    opt_cols = {}
    for i, h in enumerate(header):
        for letter in "ABCDEFGH":
            if h in (letter, "选项" + letter, "OPTION" + letter):
                opt_cols[letter] = i
                break

    has_header = stem_i >= 0
    if has_header:
        data_rows = rows[1:]
    else:
        data_rows = rows
        opt_cols = {}

    out = []
    for row in data_rows:
        if not any(row):
            continue
        if has_header:
            stem = row[stem_i] if stem_i < len(row) else ""
            ans = row[ans_i] if 0 <= ans_i < len(row) else ""
            exp = row[exp_i] if 0 <= exp_i < len(row) else ""
            qtype = row[type_i] if 0 <= type_i < len(row) else ""
            part = row[part_i] if 0 <= part_i < len(row) else ""
            opts = [
                {"k": letter, "v": row[i] if i < len(row) else ""}
                for letter, i in sorted(opt_cols.items())
                if i < len(row) and row[i]
            ]
        else:
            # 无表头：第 1 列题干；从右向左找「答案列」（A/B/AB 或 对/错），其左为选项
            stem = row[0] if row else ""
            ans, exp, qtype, part = "", "", "", ""
            opts = []
            ans_idx = -1
            for j in range(len(row) - 1, 0, -1):
                cell = row[j].strip()
                if not cell:
                    continue
                if re.fullmatch(r"[A-H]{1,8}", cell.upper()) or judge_letter(cell):
                    ans_idx = j
                    ans = cell
                    break
            if ans_idx > 0:
                for j in range(1, ans_idx):
                    if row[j]:
                        opts.append({"k": chr(ord("A") + len(opts)), "v": row[j]})
                rest = row[ans_idx + 1:]
                if rest:
                    if re.search(r"^\s*(单选|多选|判断|单选|多选|判断)题?\s*$", rest[0]) or \
                            re.search(r"^(single|multi|judge)$", rest[0], re.I):
                        qtype = rest[0]
                    else:
                        exp = rest[0]
                if len(rest) > 1 and re.search(r"单选|多选|判断|single|multi|judge", rest[1], re.I):
                    qtype = rest[1]
            else:
                opts = [{"k": chr(ord("A") + i), "v": c} for i, c in enumerate(row[1:5]) if c]
        out.append({
            "stem": stem,
            "opts": opts,
            "ans": ans,
            "type": qtype,
            "exp": exp,
            "part": part,
        })
    return out, len(data_rows)


def parse_docx_questions(file_bytes):
    try:
        from docx import Document
    except Exception as e:
        raise ValueError("缺少 python-docx 组件：" + str(e))
    doc = Document(io.BytesIO(file_bytes))
    lines = [p.text.strip() for p in doc.paragraphs if p.text.strip()]
    text = "\n".join(lines)

    if len(split_blocks(norm(text))) >= 1:
        return parse_text_questions(text)

    # 纯表格文档：每行 → 制表符分隔，再按 CSV 解析
    table_lines = []
    for tb in doc.tables:
        for row in tb.rows:
            cells = [collapse(c.text) for c in row.cells]
            if any(cells):
                table_lines.append("\t".join(cells))
    if table_lines:
        tsv = "\n".join(table_lines)
        try:
            raw, n = parse_csv_questions(tsv, delimiter="\t")
            if raw:
                return raw, n
        except Exception:
            pass
        return parse_text_questions(tsv)
    raise ValueError("Word 文档里没有识别到题目段落或表格。")


def parse_json_questions(text):
    try:
        obj = json.loads(text)
    except Exception as e:
        raise ValueError("JSON 解析失败：" + str(e))
    if isinstance(obj, dict):
        arr = obj.get("questions") or obj.get("题目") or obj.get("list")
        if not isinstance(arr, list):
            raise ValueError('JSON 对象需要包含 "questions" 数组，或直接上传题目数组。')
    elif isinstance(obj, list):
        arr = obj
    else:
        raise ValueError("JSON 根节点必须是数组或含 questions 的对象。")
    out = []
    for item in arr:
        if not isinstance(item, dict):
            continue
        out.append(normalize_raw_question(item))
    return out, len(arr)


def normalize_raw_question(item):
    stem = item.get("stem") or item.get("题干") or item.get("question") or \
        item.get("题目") or item.get("问题") or ""
    ans_raw = item.get("ans", item.get("answer", item.get("答案", "")))
    if isinstance(ans_raw, (list, tuple)):
        ans_raw = "".join(str(x) for x in ans_raw)
    exp = item.get("exp") or item.get("explanation") or item.get("解析") or ""
    part = item.get("part") or item.get("部分") or item.get("分类") or item.get("类别") or ""
    qtype = item.get("type") or item.get("题型") or ""

    opts_raw = item.get("opts") or item.get("options") or item.get("选项") or []
    opts = []
    if isinstance(opts_raw, dict):
        for k in opts_raw.keys():
            opts.append({"k": norm(k).upper()[:1], "v": opts_raw[k]})
    elif isinstance(opts_raw, list):
        for i, o in enumerate(opts_raw):
            if isinstance(o, dict):
                k = o.get("k") or o.get("key") or o.get("label") or o.get("letter") or chr(ord("A") + i)
                v = o.get("v") or o.get("value") or o.get("text") or o.get("content") or ""
                opts.append({"k": norm(k).upper()[:1], "v": v})
            else:
                opts.append({"k": chr(ord("A") + i), "v": o})
    return {
        "stem": stem,
        "opts": opts,
        "ans": ans_raw,
        "type": qtype,
        "exp": exp,
        "part": part,
    }


def finalize_question(raw):
    stem = collapse(raw.get("stem"))
    ans_raw = raw.get("ans", "")
    letters = ans_letters(ans_raw)
    truth = judge_letter(ans_raw)

    opts = []
    for o in raw.get("opts") or []:
        k = norm(o.get("k", "")).upper()[:1]
        v = collapse(o.get("v", ""))
        if k and v:
            opts.append({"k": k, "v": v})

    t = norm(raw.get("type", "")).lower()
    if "多" in t or "multi" in t:
        qtype = "multi"
    elif "判断" in t or "judge" in t:
        qtype = "judge"
    elif "单选" in t or "single" in t:
        qtype = "single"
    elif truth and not opts:
        qtype = "judge"
    elif len(letters) > 1:
        qtype = "multi"
    else:
        qtype = "single"

    if not opts and qtype == "judge":
        opts = [{"k": "A", "v": "正确"}, {"k": "B", "v": "错误"}]
        if not letters:
            letters = truth
    elif opts and truth and not letters:
        for o in opts:
            if judge_letter(o["v"]) == truth:
                letters = o["k"]
                break
        if not letters and len(opts) == 2:
            letters = truth

    return {
        "stem": stem,
        "opts": opts,
        "ans": letters,
        "type": qtype,
        "exp": collapse(raw.get("exp")),
        "part": collapse(raw.get("part")),
    }


def qc_questions(raw_list):
    out, seen = [], set()
    stats = {"total": len(raw_list), "kept": 0, "dropped": 0, "reasons": {}}

    def drop(reason):
        stats["dropped"] += 1
        stats["reasons"][reason] = stats["reasons"].get(reason, 0) + 1

    for raw in raw_list:
        q = finalize_question(raw)
        if not q["stem"]:
            drop("题干为空")
            continue
        if not q["ans"]:
            drop("答案缺失")
            continue
        if len(q["opts"]) < 2 and q["type"] != "judge":
            drop("选项不足")
            continue
        if not q["opts"]:
            drop("选项不足")
            continue
        keys = [o["k"] for o in q["opts"]]
        if any(k not in keys for k in q["ans"]):
            drop("答案越界")
            continue
        if len(set(o["v"] for o in q["opts"])) != len(q["opts"]):
            drop("选项重复")
            continue
        if q["type"] == "single" and len(q["ans"]) > 1:
            q["type"] = "multi"
        if q["type"] == "multi" and len(q["ans"]) < 2:
            drop("多选单答案")
            continue
        dedupe = re.sub(r"\s+", "", q["stem"])[:80] + "||" + "|".join(o["v"] for o in q["opts"])[:120]
        if dedupe in seen:
            drop("重复题目")
            continue
        seen.add(dedupe)
        out.append(q)

    for i, q in enumerate(out, 1):
        q["id"] = "Q%04d" % i
        q.setdefault("exp", "")
    stats["kept"] = len(out)
    return out, stats


# ---------------------------------------------------------------------------
# 用户、会话与本地数据库（SQLite，零额外依赖）
# ---------------------------------------------------------------------------

def get_db():
    if "db" not in g:
        conn = sqlite3.connect(DB_PATH)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        g.db = conn
    return g.db


@app.teardown_appcontext
def close_db(_exc):
    conn = g.pop("db", None)
    if conn is not None:
        conn.close()


def init_db():
    conn = sqlite3.connect(DB_PATH)
    try:
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                email TEXT NOT NULL UNIQUE,
                pass_hash TEXT NOT NULL,
                name TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                last_login TEXT NOT NULL DEFAULT ''
            );
            CREATE TABLE IF NOT EXISTS user_llm (
                user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
                preset TEXT NOT NULL DEFAULT '',
                base_url TEXT NOT NULL DEFAULT '',
                api_key TEXT NOT NULL DEFAULT '',
                model TEXT NOT NULL DEFAULT '',
                updated_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS user_progress (
                user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
                done_json TEXT NOT NULL DEFAULT '{}',
                fav_json TEXT NOT NULL DEFAULT '{}',
                updated_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS email_codes (
                email TEXT NOT NULL,
                purpose TEXT NOT NULL,
                code_hash TEXT NOT NULL,
                expires_at INTEGER NOT NULL,
                sent_at INTEGER NOT NULL,
                attempts INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY (email, purpose)
            );
            """
        )
        conn.commit()
    finally:
        conn.close()


def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def current_user():
    uid = session.get("uid")
    if not uid:
        return None
    row = get_db().execute(
        "SELECT id, email, name, created_at, last_login FROM users WHERE id = ?",
        (uid,),
    ).fetchone()
    if not row:
        session.pop("uid", None)
        return None
    return dict(row)


def user_llm_row(uid):
    row = get_db().execute(
        "SELECT preset, base_url, api_key, model FROM user_llm WHERE user_id = ?",
        (uid,),
    ).fetchone()
    return dict(row) if row else None


EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]{2,}$")


def auth_fields(data):
    email = str(data.get("email") or "").strip().lower()
    password = str(data.get("password") or "")
    name = str(data.get("name") or "").strip()[:24]
    if not EMAIL_RE.match(email):
        return None, "邮箱格式不正确"
    if len(password) < 6:
        return None, "密码至少 6 位"
    if len(password) > 128:
        return None, "密码过长"
    return (email, password, name), None


# ------------------------------ 邮件验证码 ------------------------------

DEFAULT_MAIL = {
    "host": "",
    "port": 465,
    "ssl": True,
    "user": "",
    "password": "",
    "from_name": "青简刷题系统",
}
CODE_TTL = 10 * 60          # 验证码有效期（秒）
CODE_COOLDOWN = 60          # 同邮箱同用途重发冷却
CODE_MAX_ATTEMPTS = 5


def load_mail_config():
    cfg = {}
    if MAIL_PATH.exists():
        try:
            cfg = json.loads(MAIL_PATH.read_text(encoding="utf-8"))
        except Exception:
            cfg = {}
    merged = dict(DEFAULT_MAIL)
    if isinstance(cfg, dict):
        merged.update(cfg)
    return merged


def save_mail_config(cfg):
    MAIL_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )


def mail_ready(cfg=None):
    cfg = cfg or load_mail_config()
    return bool(
        str(cfg.get("host") or "").strip()
        and str(cfg.get("user") or "").strip()
        and str(cfg.get("password") or "")
    )


def send_mail(to_addr, subject, body):
    """用本机 smtp.json 的配置发纯文本邮件，错误统一抛 RuntimeError 给前端。"""
    cfg = load_mail_config()
    if not mail_ready(cfg):
        raise RuntimeError("尚未配置邮件服务，请到「我的」页填写 SMTP 信息")
    host = str(cfg.get("host") or "").strip()
    user = str(cfg.get("user") or "").strip()
    try:
        port = int(cfg.get("port") or 465)
    except (TypeError, ValueError):
        port = 465
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = formataddr((str(cfg.get("from_name") or "青简"), user))
    msg["To"] = to_addr
    msg.set_content(body)
    server = None
    try:
        if cfg.get("ssl", True):
            server = smtplib.SMTP_SSL(
                host, port, timeout=20, context=ssl.create_default_context()
            )
        else:
            server = smtplib.SMTP(host, port, timeout=20)
            server.ehlo()
            server.starttls(context=ssl.create_default_context())
            server.ehlo()
        server.login(user, str(cfg.get("password") or ""))
        server.send_message(msg)
    except smtplib.SMTPAuthenticationError:
        raise RuntimeError("SMTP 登录失败：账号或授权码不对（QQ/163 填授权码，不是登录密码）")
    except (smtplib.SMTPException, OSError) as e:
        raise RuntimeError("邮件发送失败：%s" % e)
    finally:
        if server is not None:
            try:
                server.quit()
            except Exception:
                pass


def code_hash(code):
    salt = secrets.token_hex(8)
    digest = hashlib.sha256((salt + code).encode("utf-8")).hexdigest()
    return salt + "$" + digest


def verify_code_hash(stored, code):
    try:
        salt, digest = str(stored or "").split("$", 1)
    except ValueError:
        return False
    calc = hashlib.sha256((salt + str(code)).encode("utf-8")).hexdigest()
    return hmac.compare_digest(calc, digest)


def drop_code(db, email, purpose):
    db.execute(
        "DELETE FROM email_codes WHERE email = ? AND purpose = ?", (email, purpose)
    )
    db.commit()


def consume_code(email, purpose, code):
    """校验并消耗验证码，返回 (ok, 提示)。"""
    code = str(code or "").strip()
    if not code:
        return False, "请填写邮箱验证码"
    db = get_db()
    row = db.execute(
        "SELECT code_hash, expires_at, attempts FROM email_codes"
        " WHERE email = ? AND purpose = ?",
        (email, purpose),
    ).fetchone()
    if not row:
        return False, "验证码未发送或已失效，请重新获取"
    if int(row["expires_at"] or 0) < int(time.time()):
        drop_code(db, email, purpose)
        return False, "验证码已过期，请重新获取"
    if not verify_code_hash(row["code_hash"], code):
        attempts = int(row["attempts"] or 0) + 1
        if attempts >= CODE_MAX_ATTEMPTS:
            drop_code(db, email, purpose)
            return False, "验证码错误次数过多，请重新获取"
        db.execute(
            "UPDATE email_codes SET attempts = ? WHERE email = ? AND purpose = ?",
            (attempts, email, purpose),
        )
        db.commit()
        return False, "验证码不正确，还可尝试 %d 次" % (CODE_MAX_ATTEMPTS - attempts)
    drop_code(db, email, purpose)
    return True, ""


init_db()


# 未登录只能用这几类接口：看首页、登录/注册/找回密码、配置邮件服务。
# 其余（题库、AI、配置、进度、个人资料）一律 401，前端据此打开强制登录页。
PUBLIC_ENDPOINTS = {
    "index",
    "api_register",
    "api_login",
    "api_logout",
    "api_send_code",
    "api_reset_password",
    "api_me",
    "api_mail_config",
    "api_save_mail_config",
    "api_mail_test",
}


@app.before_request
def require_login():
    ep = request.endpoint
    if ep is None or ep == "static" or ep in PUBLIC_ENDPOINTS:
        return None
    if request.method == "OPTIONS":
        return None
    if not current_user():
        return jsonify({"error": "请先登录", "need_login": True}), 401
    return None


# ---------------------------------------------------------------------------
# LLM
# ---------------------------------------------------------------------------

def load_config():
    cfg = {}
    if CONFIG_PATH.exists():
        try:
            cfg = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
        except Exception:
            cfg = {}
    merged = dict(DEFAULT_CONFIG)
    if isinstance(cfg, dict):
        merged.update(cfg)
    return merged


def save_config(cfg):
    CONFIG_PATH.write_text(
        json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8"
    )


def effective_config():
    """当前请求生效的 LLM 配置：登录用户有自己的配置用个人的，否则回落全局 config.json。"""
    if has_request_context() and session.get("uid"):
        user = current_user()
        if user:
            row = user_llm_row(user["id"])
            if row:
                cfg = dict(DEFAULT_CONFIG)
                cfg.update({k: v for k, v in row.items() if v is not None})
                return cfg
    return load_config()


def call_llm(prompt, system=SYSTEM_PROMPT, timeout=300):
    cfg = effective_config()
    base = (cfg.get("base_url") or "").strip().rstrip("/")
    if not base:
        raise RuntimeError("未配置 API 地址，请打开「AI 设置」填写。")
    if not base.endswith("/v1"):
        # 允许用户填到根地址
        if not re.search(r"/v\d+$", base):
            base += "/v1"
    url = base + "/chat/completions"
    headers = {"Content-Type": "application/json"}
    key = (cfg.get("api_key") or "").strip()
    if key:
        headers["Authorization"] = "Bearer " + key
    payload = {
        "model": (cfg.get("model") or "deepseek-chat").strip(),
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": prompt},
        ],
        "temperature": 0.3,
        "max_tokens": 900,
        "stream": False,
    }
    is_local = ("127.0.0.1" in base) or ("localhost" in base)
    if is_local:
        # 本地思维模型（Qwen3 等）会把整个 token 预算花在思考上，正文为空、
        # finish_reason=length；关掉思考直接出解析。不认这参数的版本会报 400，下面去掉重试。
        payload["reasoning_effort"] = "none"
    try:
        r = requests.post(url, headers=headers, json=payload, timeout=(10, timeout))
        if r.status_code == 400 and "reasoning_effort" in payload:
            payload.pop("reasoning_effort", None)
            r = requests.post(url, headers=headers, json=payload, timeout=(10, timeout))
    except requests.exceptions.Timeout:
        hint = ""
        if "127.0.0.1" in base or "localhost" in base:
            hint = " 本地模型首次加载需要把整模型从磁盘读入显存/内存，27B 级可能要 1–3 分钟，可稍后重试。"
        raise RuntimeError("请求超时：模型响应太慢，或地址不可达。" + hint)
    except requests.exceptions.ConnectionError:
        raise RuntimeError("无法连接 API 地址（" + base + "），请确认服务已启动、地址填写正确。")
    except Exception as e:
        raise RuntimeError("请求失败：" + str(e))
    if r.status_code >= 400:
        msg = r.text[:400].replace("\n", " ")
        if r.status_code == 404 and "model" in msg.lower() and ("127.0.0.1" in base or "localhost" in base):
            msg += "（本地 Ollama 找不到该模型：启动 ollama serve 前须 set OLLAMA_MODELS=D:\\mytools\\ollama\\models，并用 ollama list 核对模型名）"
        raise RuntimeError("API 返回 %s：%s" % (r.status_code, msg))
    try:
        data = r.json()
        msg = data["choices"][0]["message"]
        content = (msg.get("content") or "").strip()
        if not content:
            content = (msg.get("reasoning_content") or "").strip()
        if not content:
            content = (data["choices"][0].get("text") or "").strip()
    except Exception:
        raise RuntimeError("API 响应格式无法识别：" + r.text[:300])
    if not content:
        finish = ""
        try:
            finish = data["choices"][0].get("finish_reason") or ""
        except Exception:
            pass
        if finish == "length":
            hint = " 本地思维模型可能把 token 预算全花在思考上：请重试，或在「AI 设置」换非思维模型。"
            if is_local:
                raise RuntimeError("模型思考超长，正文被截断（finish_reason=length）。" + hint)
            raise RuntimeError("模型输出被长度上限截断（finish_reason=length），请重试。")
        raise RuntimeError("模型返回了空内容，请换一个模型或稍后重试。")
    return content


def question_prompt(q):
    type_cn = {"single": "单选题", "multi": "多选题", "judge": "判断题"}.get(q.get("type"), "题目")
    opts = "\n".join("%s. %s" % (o["k"], o["v"]) for o in q.get("opts") or [])
    return "题型：%s\n题干：%s\n选项：\n%s\n正确答案：%s\n请给出解析。" % (
        type_cn, q.get("stem", ""), opts, q.get("ans", "")
    )


# ---------------------------------------------------------------------------
# 路由
# ---------------------------------------------------------------------------

@app.get("/")
def index():
    return send_from_directory(STATIC_DIR, "index.html")


# ------------------------------- 认证 -------------------------------

@app.post("/api/auth/register")
def api_register():
    data = request.get_json(silent=True) or {}
    fields, err = auth_fields(data)
    if err:
        return jsonify({"error": err}), 400
    email, password, name = fields
    db = get_db()
    if db.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
        return jsonify({"error": "该邮箱已注册，请直接登录"}), 409
    if not mail_ready():
        return jsonify({
            "error": "注册需要邮箱验证码，请先到「我的」页填写 SMTP 信息",
            "need_mail_config": True,
        }), 400
    ok, msg = consume_code(email, "register", data.get("code"))
    if not ok:
        return jsonify({"error": msg}), 400
    cur = db.execute(
        "INSERT INTO users (email, pass_hash, name, created_at, last_login)"
        " VALUES (?, ?, ?, ?, ?)",
        (email, generate_password_hash(password),
         name or email.split("@")[0], now_str(), now_str()),
    )
    db.commit()
    session.permanent = True
    session["uid"] = cur.lastrowid
    return jsonify({"ok": True, "user": current_user()})


@app.post("/api/auth/login")
def api_login():
    data = request.get_json(silent=True) or {}
    email = str(data.get("email") or "").strip().lower()
    password = str(data.get("password") or "")
    db = get_db()
    row = db.execute(
        "SELECT id, pass_hash FROM users WHERE email = ?", (email,)
    ).fetchone()
    if not row or not password or not check_password_hash(row["pass_hash"], password):
        # 统一提示，避免暴露邮箱是否已注册
        return jsonify({"error": "邮箱或密码不正确"}), 401
    db.execute("UPDATE users SET last_login = ? WHERE id = ?", (now_str(), row["id"]))
    db.commit()
    session.permanent = True
    session["uid"] = row["id"]
    return jsonify({"ok": True, "user": current_user()})


@app.post("/api/auth/logout")
def api_logout():
    session.pop("uid", None)
    return jsonify({"ok": True})


@app.post("/api/auth/send-code")
def api_send_code():
    data = request.get_json(silent=True) or {}
    email = str(data.get("email") or "").strip().lower()
    purpose = str(data.get("purpose") or "register").strip().lower()
    if purpose not in ("register", "reset"):
        return jsonify({"error": "未知的验证码用途"}), 400
    if not EMAIL_RE.match(email):
        return jsonify({"error": "邮箱格式不正确"}), 400
    db = get_db()
    exists = db.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone()
    if purpose == "register" and exists:
        return jsonify({"error": "该邮箱已注册，请直接登录"}), 409
    if purpose == "reset" and not exists:
        return jsonify({"error": "该邮箱未注册"}), 404
    if not mail_ready():
        return jsonify({
            "error": "尚未配置邮件服务，请先到「我的」页填写 SMTP 信息",
            "need_mail_config": True,
        }), 400
    now = int(time.time())
    row = db.execute(
        "SELECT sent_at FROM email_codes WHERE email = ? AND purpose = ?",
        (email, purpose),
    ).fetchone()
    if row:
        wait = CODE_COOLDOWN - (now - int(row["sent_at"] or 0))
        if wait > 0:
            return jsonify({
                "error": "发送太频繁，请 %d 秒后再试" % wait,
                "retry_after": wait,
            }), 429
    code = "%06d" % secrets.randbelow(1000000)
    db.execute(
        "INSERT INTO email_codes (email, purpose, code_hash, expires_at, sent_at, attempts)"
        " VALUES (?, ?, ?, ?, ?, 0)"
        " ON CONFLICT(email, purpose) DO UPDATE SET"
        "   code_hash = excluded.code_hash,"
        "   expires_at = excluded.expires_at,"
        "   sent_at = excluded.sent_at,"
        "   attempts = 0",
        (email, purpose, code_hash(code), now + CODE_TTL, now),
    )
    db.commit()
    label = "注册" if purpose == "register" else "重置密码"
    body = (
        "青简 · %s验证码\n\n"
        "你的验证码是：%s\n"
        "%d 分钟内有效，最多尝试 %d 次。\n\n"
        "如果不是你本人操作，请忽略这封邮件。\n"
        % (label, code, CODE_TTL // 60, CODE_MAX_ATTEMPTS)
    )
    try:
        send_mail(email, "青简 · %s验证码" % label, body)
    except Exception as e:
        drop_code(db, email, purpose)
        return jsonify({"error": str(e)}), 502
    return jsonify({"ok": True, "cooldown": CODE_COOLDOWN, "expires_in": CODE_TTL})


@app.post("/api/auth/reset")
def api_reset_password():
    data = request.get_json(silent=True) or {}
    fields, err = auth_fields({
        "email": data.get("email"),
        "password": data.get("password"),
    })
    if err:
        return jsonify({"error": err}), 400
    email, password, _ = fields
    db = get_db()
    row = db.execute("SELECT id FROM users WHERE email = ?", (email,)).fetchone()
    if not row:
        return jsonify({"error": "该邮箱未注册"}), 404
    if not mail_ready():
        return jsonify({
            "error": "尚未配置邮件服务，无法用邮箱重置密码",
            "need_mail_config": True,
        }), 400
    ok, msg = consume_code(email, "reset", data.get("code"))
    if not ok:
        return jsonify({"error": msg}), 400
    db.execute(
        "UPDATE users SET pass_hash = ?, last_login = ? WHERE id = ?",
        (generate_password_hash(password), now_str(), row["id"]),
    )
    db.commit()
    session.permanent = True
    session["uid"] = row["id"]
    return jsonify({"ok": True, "user": current_user()})


@app.post("/api/auth/password")
def api_change_password():
    user = current_user()
    if not user:
        return jsonify({"error": "未登录", "need_login": True}), 401
    data = request.get_json(silent=True) or {}
    old = str(data.get("old_password") or "")
    new = str(data.get("new_password") or "")
    if len(new) < 6:
        return jsonify({"error": "新密码至少 6 位"}), 400
    if len(new) > 128:
        return jsonify({"error": "新密码过长"}), 400
    db = get_db()
    row = db.execute(
        "SELECT pass_hash FROM users WHERE id = ?", (user["id"],)
    ).fetchone()
    if not row or not check_password_hash(row["pass_hash"], old):
        return jsonify({"error": "原密码不正确"}), 400
    db.execute(
        "UPDATE users SET pass_hash = ? WHERE id = ?",
        (generate_password_hash(new), user["id"]),
    )
    db.commit()
    return jsonify({"ok": True})


@app.get("/api/auth/me")
def api_me():
    return jsonify({"user": current_user()})


# ------------------------------- 进度 -------------------------------

@app.get("/api/progress")
def api_get_progress():
    user = current_user()
    if not user:
        return jsonify({"error": "未登录", "need_login": True}), 401
    row = get_db().execute(
        "SELECT done_json, fav_json, updated_at FROM user_progress WHERE user_id = ?",
        (user["id"],),
    ).fetchone()
    done, fav, updated = {}, {}, ""
    if row:
        try:
            done = json.loads(row["done_json"]) or {}
        except Exception:
            done = {}
        try:
            fav = json.loads(row["fav_json"]) or {}
        except Exception:
            fav = {}
        updated = row["updated_at"] or ""
    return jsonify({"ok": True, "done": done, "fav": fav, "updated": updated})


@app.put("/api/progress")
def api_put_progress():
    user = current_user()
    if not user:
        return jsonify({"error": "未登录", "need_login": True}), 401
    data = request.get_json(silent=True) or {}
    done = data.get("done") if isinstance(data.get("done"), dict) else {}
    fav = data.get("fav") if isinstance(data.get("fav"), dict) else {}
    done_json = json.dumps(done, ensure_ascii=False, separators=(",", ":"))
    fav_json = json.dumps(fav, ensure_ascii=False, separators=(",", ":"))
    if len(done_json) > 8 * 1024 * 1024 or len(fav_json) > 4 * 1024 * 1024:
        return jsonify({"error": "进度数据过大，未保存"}), 413
    db = get_db()
    db.execute(
        "INSERT INTO user_progress (user_id, done_json, fav_json, updated_at)"
        " VALUES (?, ?, ?, ?)"
        " ON CONFLICT(user_id) DO UPDATE SET"
        "   done_json = excluded.done_json,"
        "   fav_json = excluded.fav_json,"
        "   updated_at = excluded.updated_at",
        (user["id"], done_json, fav_json, now_str()),
    )
    db.commit()
    return jsonify({"ok": True, "updated": now_str()})


# ------------------------------- 个人资料 -------------------------------

@app.get("/api/profile")
def api_profile():
    user = current_user()
    if not user:
        return jsonify({"error": "未登录", "need_login": True}), 401
    db = get_db()
    row = db.execute(
        "SELECT done_json, fav_json, updated_at FROM user_progress WHERE user_id = ?",
        (user["id"],),
    ).fetchone()
    done, fav, updated = {}, {}, ""
    if row:
        try:
            done = json.loads(row["done_json"]) or {}
        except Exception:
            done = {}
        try:
            fav = json.loads(row["fav_json"]) or {}
        except Exception:
            fav = {}
        updated = row["updated_at"] or ""
    done_n = len(done) if isinstance(done, dict) else 0
    ok_n = sum(
        1 for v in done.values() if isinstance(v, dict) and v.get("ok") is True
    ) if isinstance(done, dict) else 0
    wrong_n = sum(
        1 for v in done.values() if isinstance(v, dict) and v.get("ok") is False
    ) if isinstance(done, dict) else 0
    total_q, bank_n = 0, 0
    for p in BANK_DIR.rglob("*.json"):
        s = bank_summary(p)
        if s:
            bank_n += 1
            total_q += s["total"]
    llm = user_llm_row(user["id"])
    return jsonify({
        "ok": True,
        "user": user,
        "stats": {
            "done": done_n,
            "correct": ok_n,
            "wrong": wrong_n,
            "accuracy": round(ok_n * 100 / done_n) if done_n else 0,
            "fav": len(fav) if isinstance(fav, dict) else 0,
            "banks": bank_n,
            "total": total_q,
            "updated": updated,
        },
        "llm_configured": bool(llm and (llm.get("base_url") or llm.get("api_key"))),
        "mail_configured": mail_ready(),
    })


@app.post("/api/profile")
def api_update_profile():
    user = current_user()
    if not user:
        return jsonify({"error": "未登录", "need_login": True}), 401
    data = request.get_json(silent=True) or {}
    name = str(data.get("name") or "").strip()[:24]
    if not name:
        return jsonify({"error": "称呼不能为空"}), 400
    db = get_db()
    db.execute("UPDATE users SET name = ? WHERE id = ?", (name, user["id"]))
    db.commit()
    return jsonify({"ok": True, "user": current_user()})


# ------------------------------- 邮件服务 -------------------------------

@app.get("/api/mail/config")
def api_mail_config():
    cfg = load_mail_config()
    try:
        port = int(cfg.get("port") or 465)
    except (TypeError, ValueError):
        port = 465
    return jsonify({
        "configured": mail_ready(cfg),
        "host": cfg.get("host") or "",
        "port": port,
        "ssl": bool(cfg.get("ssl", True)),
        "user": cfg.get("user") or "",
        "from_name": cfg.get("from_name") or "",
        "has_password": bool(cfg.get("password")),
    })


@app.post("/api/mail/config")
def api_save_mail_config():
    data = request.get_json(silent=True) or {}
    cfg = load_mail_config()
    host = str(data.get("host") or "").strip()
    host = re.sub(r"^https?://", "", host).strip("/")
    if host and not re.match(r"^[A-Za-z0-9.\-]+$", host):
        return jsonify({"error": "SMTP 服务器只填主机名，如 smtp.qq.com"}), 400
    try:
        port = int(data.get("port") or 465)
    except (TypeError, ValueError):
        return jsonify({"error": "端口必须是数字"}), 400
    if not (1 <= port <= 65535):
        return jsonify({"error": "端口超出范围"}), 400
    user = str(data.get("user") or "").strip()
    if user and not EMAIL_RE.match(user.lower()):
        return jsonify({"error": "发件邮箱格式不正确"}), 400
    cfg.update({
        "host": host,
        "port": port,
        "ssl": bool(data.get("ssl", True)),
        "user": user,
        "from_name": str(data.get("from_name") or "").strip()[:32],
    })
    if data.get("clear_password"):
        cfg["password"] = ""
    else:
        pwd = data.get("password")
        if isinstance(pwd, str) and pwd.strip():
            cfg["password"] = pwd.strip()
    save_mail_config(cfg)
    return jsonify({"ok": True, "configured": mail_ready(cfg)})


@app.post("/api/mail/test")
def api_mail_test():
    data = request.get_json(silent=True) or {}
    cfg = load_mail_config()
    to_addr = (
        str(data.get("to") or "").strip().lower()
        or str(cfg.get("user") or "").strip().lower()
    )
    if not EMAIL_RE.match(to_addr):
        return jsonify({"error": "请先填写发件邮箱，或提供测试收件人"}), 400
    try:
        send_mail(
            to_addr,
            "青简 · 测试邮件",
            "这是一封来自青简刷题系统的测试邮件。\n\n"
            "收到即表示 SMTP 配置可用，注册与找回密码的验证码会通过这个邮箱发出。\n",
        )
    except Exception as e:
        return jsonify({"error": str(e)}), 502
    return jsonify({"ok": True, "to": to_addr})


@app.get("/api/banks")
def api_banks():
    banks = []
    for p in BANK_DIR.rglob("*.json"):
        s = bank_summary(p)
        if s:
            banks.append(s)
    banks.sort(key=lambda b: ((b["group"] == ""), b["group"], b["id"]))
    return jsonify({"banks": banks})


@app.get("/api/bank/<path:bank_id>")
def api_bank(bank_id):
    data = load_bank(bank_id)
    if not data:
        return jsonify({"error": "题库不存在：" + bank_id}), 404
    # 分组以磁盘目录为准（移动文件后旧 JSON 里的 group 可能过期）
    data["group"] = group_of_path(bank_path(bank_id))
    data["id"] = bank_id
    return jsonify(data)


@app.post("/api/banks")
def api_import():
    fmt = (request.form.get("format") or "").strip().lower()
    name = (request.form.get("name") or "").strip()
    group = safe_group_name(request.form.get("group") or "")
    text = request.form.get("text") or ""
    file = request.files.get("file")

    raw_bytes = b""
    if file and file.filename:
        raw_bytes = file.read()
        if not name:
            name = Path(file.filename).stem
        ext = Path(file.filename).suffix.lower()
        if not fmt:
            fmt = {".json": "json", ".txt": "text", ".csv": "csv", ".docx": "docx"}.get(ext, "text")

    if fmt not in ("json", "text", "csv", "docx"):
        return jsonify({"error": "不支持的格式：" + (fmt or "未指定")}), 400

    try:
        if fmt == "docx":
            if not raw_bytes:
                return jsonify({"error": "Word 导入需要选择 .docx 文件（不能粘贴）。"}), 400
            raw, n = parse_docx_questions(raw_bytes)
        else:
            if not text and raw_bytes:
                text = decode_bytes(raw_bytes)
            if not text.strip():
                return jsonify({"error": "内容为空：请粘贴题目或选择文件。"}), 400
            if fmt == "json":
                raw, n = parse_json_questions(text)
            elif fmt == "csv":
                raw, n = parse_csv_questions(text)
            else:
                raw, n = parse_text_questions(text)
    except ValueError as e:
        return jsonify({"error": str(e)}), 400
    except Exception as e:
        return jsonify({"error": "解析失败：" + str(e)}), 400

    questions, stats = qc_questions(raw)
    if not questions:
        return jsonify({
            "error": "没有可入库的题目（格式不符合或全部被质检剔除）。",
            "stats": stats,
        }), 400

    base_name = name or ("导入题库 " + datetime.now().strftime("%m%d-%H%M"))
    bank_id = unique_bank_id(base_name, group)
    save_bank(bank_id, re.sub(r'[\\/:*?"<>|]', "", base_name).strip() or bank_id, questions)
    return jsonify({
        "ok": True,
        "id": bank_id,
        "name": bank_id,
        "group": group or "未分组",
        "kept": stats["kept"],
        "dropped": stats["dropped"],
        "total": stats["total"],
        "reasons": stats["reasons"],
    })


@app.delete("/api/bank/<path:bank_id>")
def api_delete_bank(bank_id):
    p = bank_path(bank_id)
    if not p:
        return jsonify({"error": "题库不存在：" + bank_id}), 404
    parent = p.parent
    try:
        p.unlink()
        if parent != BANK_DIR and not any(parent.iterdir()):
            parent.rmdir()
    except Exception as e:
        return jsonify({"error": "删除失败：" + str(e)}), 500
    return jsonify({"ok": True})


@app.post("/api/bank/<path:bank_id>/group")
def api_move_bank(bank_id):
    src = bank_path(bank_id)
    if not src:
        return jsonify({"error": "题库不存在：" + bank_id}), 404
    data = request.get_json(silent=True) or {}
    group = safe_group_name(data.get("group") or "")
    dest_dir = group_dir(group)
    try:
        dest_dir.mkdir(parents=True, exist_ok=True)
        dest = dest_dir / src.name
        if dest.exists() and dest.resolve() != src.resolve():
            i = 2
            while (dest_dir / (src.stem + f"-{i}.json")).exists():
                i += 1
            dest = dest_dir / (src.stem + f"-{i}.json")
        if dest.resolve() != src.resolve():
            os.replace(src, dest)
            if src.parent != BANK_DIR and not any(src.parent.iterdir()):
                src.parent.rmdir()
        # 文件已移动，同步 JSON 内的 group 字段，避免详情接口读到旧分组
        try:
            payload = json.loads(dest.read_text(encoding="utf-8"))
            payload["group"] = group or ""
            tmp = dest.with_name(dest.name + ".tmp")
            tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
            os.replace(tmp, dest)
        except Exception:
            pass
    except Exception as e:
        return jsonify({"error": "移动失败：" + str(e)}), 500
    return jsonify({"ok": True, "id": rel_bank_id(dest), "group": group or "未分组"})


def migrate_progress_bank(old_id, new_id):
    """题库重命名后，把各账号进度里 "旧id|题号" 的键迁到新 id。"""
    if not old_id or not new_id or old_id == new_id:
        return
    db = get_db()
    rows = db.execute(
        "SELECT user_id, done_json, fav_json FROM user_progress"
    ).fetchall()
    prefix = old_id + "|"
    changed = False
    for row in rows:
        values, row_changed = [], False
        for raw in (row["done_json"], row["fav_json"]):
            try:
                obj = json.loads(raw or "{}")
            except Exception:
                obj = {}
            if not isinstance(obj, dict):
                obj = {}
            if any(str(k).startswith(prefix) for k in obj):
                obj = {
                    (new_id + str(k)[len(old_id):] if str(k).startswith(prefix) else k): v
                    for k, v in obj.items()
                }
                row_changed = True
            values.append(json.dumps(obj, ensure_ascii=False, separators=(",", ":")))
        if row_changed:
            db.execute(
                "UPDATE user_progress SET done_json = ?, fav_json = ?, updated_at = ?"
                " WHERE user_id = ?",
                (values[0], values[1], now_str(), row["user_id"]),
            )
            changed = True
    if changed:
        db.commit()


@app.post("/api/bank/<path:bank_id>/rename")
def api_rename_bank(bank_id):
    src = bank_path(bank_id)
    if not src:
        return jsonify({"error": "题库不存在：" + bank_id}), 404
    data = request.get_json(silent=True) or {}
    raw = str(data.get("name") or "").strip()
    if not raw:
        return jsonify({"error": "题库名不能为空"}), 400
    try:
        payload = json.loads(src.read_text(encoding="utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("bad payload")
    except Exception:
        return jsonify({"error": "题库文件损坏，无法重命名"}), 500

    folder = src.parent
    base = safe_bank_id(raw)
    dest = folder / (base + ".json")
    old_id = rel_bank_id(src)
    try:
        if dest.resolve() != src.resolve():
            if dest.exists():
                i = 2
                while (folder / (f"{base}-{i}.json")).exists():
                    i += 1
                dest = folder / (f"{base}-{i}.json")
            os.replace(src, dest)
        new_id = rel_bank_id(dest)
        payload["name"] = dest.stem
        payload["group"] = group_of_path(dest)
        payload["updated"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        tmp = dest.with_name(dest.name + ".tmp")
        tmp.write_text(
            json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8"
        )
        os.replace(tmp, dest)
    except Exception as e:
        return jsonify({"error": "重命名失败：" + str(e)}), 500

    migrate_progress_bank(old_id, new_id)
    return jsonify({
        "ok": True,
        "id": new_id,
        "name": dest.stem,
        "group": group_of_path(dest),
    })


@app.get("/api/config")
def api_get_config():
    user = current_user()
    row = user_llm_row(user["id"]) if user else None
    if row:
        cfg = dict(DEFAULT_CONFIG)
        cfg.update({k: v for k, v in row.items() if v is not None})
        scope = "user"
    else:
        cfg = load_config()
        scope = "fallback" if user else "global"
    key = (cfg.get("api_key") or "").strip()
    masked = ""
    if key:
        masked = key[:3] + "****" + key[-4:] if len(key) > 8 else "****"
    return jsonify({
        "preset": cfg.get("preset") or "custom",
        "base_url": cfg.get("base_url") or "",
        "model": cfg.get("model") or "",
        "has_key": bool(key),
        "key_masked": masked,
        "presets": PRESETS,
        "scope": scope,
    })


@app.post("/api/config")
def api_set_config():
    data = request.get_json(silent=True) or {}
    user = current_user()
    row = user_llm_row(user["id"]) if user else None
    if user and row:
        cfg = dict(DEFAULT_CONFIG)
        cfg.update({k: v for k, v in row.items() if v is not None})
    else:
        # 未登录或还没保存过个人配置：以全局配置为底，避免只改一项就把其余项冲成默认
        cfg = load_config()
    preset = data.get("preset")
    if preset in PRESETS:
        cfg["preset"] = preset
    if "base_url" in data:
        cfg["base_url"] = str(data.get("base_url") or "").strip()
    if "model" in data:
        cfg["model"] = str(data.get("model") or "").strip()
    if data.get("clear_key"):
        cfg["api_key"] = ""
    elif str(data.get("api_key") or "").strip():
        cfg["api_key"] = str(data.get("api_key")).strip()

    if user:
        db = get_db()
        db.execute(
            "INSERT INTO user_llm (user_id, preset, base_url, api_key, model, updated_at)"
            " VALUES (?, ?, ?, ?, ?, ?)"
            " ON CONFLICT(user_id) DO UPDATE SET"
            "   preset = excluded.preset,"
            "   base_url = excluded.base_url,"
            "   api_key = excluded.api_key,"
            "   model = excluded.model,"
            "   updated_at = excluded.updated_at",
            (user["id"], cfg.get("preset") or "", cfg.get("base_url") or "",
             cfg.get("api_key") or "", cfg.get("model") or "", now_str()),
        )
        db.commit()
        return jsonify({"ok": True, "scope": "user"})

    save_config(cfg)
    return jsonify({"ok": True, "scope": "global"})


@app.post("/api/explain/test")
def api_explain_test():
    try:
        content = call_llm("请只回复两个字：可用", system="你是连接测试助手。", timeout=240)
        return jsonify({"ok": True, "msg": content[:100]})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.post("/api/explain")
def api_explain():
    data = request.get_json(silent=True) or {}
    bank_id = data.get("bank")
    qid = str(data.get("qid") or "")
    force = bool(data.get("force"))
    payload = load_bank(bank_id)
    if not payload:
        return jsonify({"error": "题库不存在：" + str(bank_id)}), 404
    questions = payload.get("questions") or []
    target = None
    for q in questions:
        if str(q.get("id")) == qid:
            target = q
            break
    if not target:
        return jsonify({"error": "题目不存在：" + qid}), 404
    if (target.get("exp") or "").strip() and not force:
        return jsonify({"ok": True, "exp": target["exp"], "cached": True})
    try:
        exp = call_llm(question_prompt(target))
    except Exception as e:
        return jsonify({"error": str(e)}), 502
    target["exp"] = exp.strip()
    path = bank_path(bank_id)
    payload.setdefault("name", bank_id)
    payload["updated"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, path)
    return jsonify({"ok": True, "exp": target["exp"], "cached": False})


# ---------------------------------------------------------------------------

def main():
    if not CONFIG_PATH.exists():
        save_config(DEFAULT_CONFIG)
    init_db()
    print("=" * 56)
    print("  青简 · 智能刷题系统")
    print("  题库目录：%s" % BANK_DIR)
    print("  账号库：%s" % DB_PATH)
    print("  打开：http://127.0.0.1:%d/" % PORT)
    print("  关闭本窗口即停止服务")
    print("=" * 56)
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    app.run(host="127.0.0.1", port=PORT, debug=False, threaded=True)


if __name__ == "__main__":
    main()
