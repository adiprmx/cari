"""CARI Server v0.7 "Belajar Sendiri" — 100% stdlib, tanpa pip install.

Mesin pencari yang belajar sendiri:
  Pilar 1 — Belajar dari pengguna (learning to rank, 100% lokal):
    * Setiap query & klik dicatat di tabel events (persisten di SQLite).
    * Dokumen yang sering diklik untuk query X otomatis naik peringkat
      untuk query X (click boost: skor BM25 + BETA*ln(1+klik)).
    * Query diperkaya otomatis dengan istilah dari dokumen yang diklik
      (relevance feedback ala Rocchio) — disimpan di query_terms.
    * Saran query + toleransi typo dari riwayat pencarian (GET /suggest).
    * Tren pencarian 7 hari terakhir (GET /trends).
  Pilar 2 — Cari tahu sendiri (auto-ingest & enrichment):
    * POST /ingest {url}: fetch halaman web -> ekstrak teks -> index otomatis.
      (Catatan: di PythonAnywhere gratis, outbound hanya ke situs whitelist —
      error fetch dijelaskan dengan jujur di respons.)
    * Setiap dokumen otomatis: deteksi bahasa (id/en), ekstraksi keyword,
      ringkasan ekstraktif 2 kalimat -> tabel doc_meta.
    * Dokumen terkait via overlap keyword (GET /related).
    * Jawaban langsung ekstraktif: kalimat paling relevan + sumbernya
      (POST /answer).
  Pilar 3 — Index inkremental: database TIDAK dihapus tiap restart
    (perbaikan kritis dari v0.6 — data belajar harus persisten).
    POST /reindex untuk rebuild penuh manual, POST /learn untuk
    "belajar ulang" dari seluruh event klik (dipanggil via scheduled task
    harian: curl -X POST -H "X-API-Key: ..." https://.../learn).

Deploy sama seperti v0.6: upload file ini ke ~/cari-server, WSGI config:
    import os, sys
    sys.path.insert(0, '/home/USERNAME/cari-server')
    os.environ['CARI_API_KEY'] = 'kunci-rahasia-buatanmu'
    from wsgi_api import application
"""

from __future__ import annotations

import base64
import hashlib
import hmac
import json
import math
import os
import re
import sqlite3
import time
import urllib.parse
import urllib.request

VERSION = "0.7.0"
ENGINE_NAME = "local"

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
DB_PATH = os.path.join(BASE_DIR, "cari.db")

# Dokumen bawaan (base64) — di-inject saat build. {nama_file: b64}
SEED_DOCS: dict[str, str] = {'catatan-python.md': 'IyBDYXRhdGFuIEJlbGFqYXIgUHl0aG9uCgpQeXRob24gYWRhbGFoIGJhaGFzYSBwZW1yb2dyYW1hbiB5YW5nIHBvcHVsZXIgdW50dWsgZGF0YSBzY2llbmNlIGRhbiB3ZWIgZGV2ZWxvcG1lbnQuCkZ1bmdzaSBkaWRlZmluaXNpa2FuIGRlbmdhbiBrYXRhIGt1bmNpIGBkZWZgLCBzZWRhbmdrYW4gY2xhc3MgZGVuZ2FuIGBjbGFzc2AuCgpMaXN0IGNvbXByZWhlbnNpb24gYWRhbGFoIGNhcmEgcmluZ2thcyBtZW1idWF0IGxpc3Q6Cmhhc2lsID0gW3gqMiBmb3IgeCBpbiByYW5nZSgxMCkgaWYgeCAlIDIgPT0gMF0KClZpcnR1YWwgZW52aXJvbm1lbnQgc2ViYWlrbnlhIHNlbGFsdSBkaXBha2FpIHBlciBwcm95ZWs6CnB5dGhvbiAtbSB2ZW52IC52ZW52CgpVbnR1ayBIVFRQIHJlcXVlc3QsIGxpYnJhcnkgYHJlcXVlc3RzYCBhdGF1IHN0ZGxpYiBgdXJsbGliYCBiaXNhIGRpcGFrYWkuClVudHVrIHdlYiBzY3JhcGluZyBzZWRlcmhhbmEsIEJlYXV0aWZ1bFNvdXAgbWVtYmFudHUgcGFyc2luZyBIVE1MLgo=', 'rencana-liburan-jepang.md': 'IyBSZW5jYW5hIExpYnVyYW4ga2UgSmVwYW5nCgpJdGluZXJhcnkgNyBoYXJpOiBUb2t5byAoMyBoYXJpKSwgS3lvdG8gKDIgaGFyaSksIE9zYWthICgyIGhhcmkpLgpCdWRnZXQgZXN0aW1hc2k6IHRpa2V0IHBlc2F3YXQgOCBqdXRhLCBob3RlbCA2IGp1dGEsIG1ha2FuIGRhbiB0cmFuc3BvcnQgNSBqdXRhLgoKRGkgVG9reW8gd2FqaWIga2U6IEFzYWt1c2EsIFNoaWJ1eWEgY3Jvc3NpbmcsIEFraWhhYmFyYSwgZGFuIHRlYW1MYWIgUGxhbmV0cy4KRGkgS3lvdG86IEZ1c2hpbWkgSW5hcmksIEFyYXNoaXlhbWEgYmFtYm9vIGdyb3ZlLCBkYW4gR2lvbi4KRGkgT3Nha2E6IERvdG9uYm9yaSwgT3Nha2EgQ2FzdGxlLCBkYW4gZGF5IHRyaXAga2UgTmFyYSB1bnR1ayBtZWxpaGF0IHJ1c2EuCgpUaXBzOiBiZWxpIEpSIFBhc3Mgc2ViZWx1bSBiZXJhbmdrYXQsIGJhd2EgY2FzaCBzZWN1a3VwbnlhIGthcmVuYSBiYW55YWsKdGVtcGF0IGtlY2lsIGhhbnlhIHRlcmltYSB0dW5haSwgZGFuIGRvd25sb2FkIGFwbGlrYXNpIHBldGEgb2ZmbGluZS4KTXVzaW0gdGVyYmFpazogc2FrdXJhIChha2hpciBNYXJldCkgYXRhdSBtb21pamkgKE5vdmVtYmVyKS4K', 'resep-rendang.md': 'IyBSZXNlcCBSZW5kYW5nIFNhcGkKCkJhaGFuIHV0YW1hOiAxIGtnIGRhZ2luZyBzYXBpLCBzYW50YW4gZGFyaSAzIGJ1dGlyIGtlbGFwYSwgZGFuIGJ1bWJ1IGhhbHVzLgpCdW1idSBoYWx1cyB0ZXJkaXJpIGRhcmkgY2FiYWkgbWVyYWgsIGJhd2FuZyBtZXJhaCwgYmF3YW5nIHB1dGloLCBqYWhlLApsZW5na3Vhcywga3VueWl0LCBkYW4ga2VtaXJpLgoKQ2FyYSBtZW1hc2FrOgoxLiBUdW1pcyBidW1idSBoYWx1cyBzYW1wYWkgaGFydW0gZGFuIG1hdGFuZy4KMi4gTWFzdWtrYW4gZGFnaW5nLCBhZHVrIHNhbXBhaSBiZXJ1YmFoIHdhcm5hLgozLiBUdWFuZyBzYW50YW4sIG1hc2FrIGRlbmdhbiBhcGkga2VjaWwgc2FtYmlsIHNlc2VrYWxpIGRpYWR1ay4KNC4gTWFzYWsgMy00IGphbSBzYW1wYWkgc2FudGFuIG1lbnl1c3V0IGRhbiBiZXJtaW55YWsuCgpLdW5jaSByZW5kYW5nIGVuYWs6IGFwaSBrZWNpbCwgc2FiYXIsIGRhbiBzYW50YW4ga2VudGFsIHlhbmcgYmVya3VhbGl0YXMuCkphbmdhbiBkaWFkdWsgdGVybGFsdSBzZXJpbmcgc3VwYXlhIGRhZ2luZyB0aWRhayBoYW5jdXIuCg=='}

# ------------------------------------------------------------- konfigurasi
CHUNK_SIZE = 800
CHUNK_OVERLAP = 120
SNIPPET_TOKENS = 24
CLICK_BETA = 2.0          # bobot click boost: skor += BETA * ln(1+klik)
EXPANSION_TERMS = 6       # istilah ekspansi query dari relevance feedback
EXPANSION_KEEP = 12       # istilah tersimpan per query (query_terms)
SUMMARY_SENTENCES = 2
KEYWORD_TOPN = 10
INGEST_MAX_BYTES = 700_000
INGEST_TIMEOUT = 12
EVENT_TTL_DAYS = 90
TREND_DAYS = 7

STOP_ID = frozenset("""yang dan di ke dari untuk pada dengan adalah itu ini tidak juga sudah
akan dalam sebagai oleh karena atau saat para setiap lebih sangat bisa ada mereka kami kita
saya kamu dia apa bagaimana mengapa kapan mana tersebut nya lah kah pun per antara terhadap
mengenai tentang agar supaya jika kalau bahwa serta dengan tanpa sampai sambil lalu mau pun
dong deh kok sih nah lho yuk ayo tolong mohon""".split())
STOP_EN = frozenset("""the a an and or of to in on for with is are was were be been being
this that these those it its as at by from will would can could should have has had not
no yes you your we our they their he she him her his hers i me my we us our ours but if
then than so such only just about into over after before between more most other some any
do does did done how what when where which who whom why""".split())
STOPWORDS = STOP_ID | STOP_EN

SCHEMA = """
CREATE TABLE IF NOT EXISTS docs (
    id    INTEGER PRIMARY KEY,
    path  TEXT UNIQUE NOT NULL,
    title TEXT NOT NULL,
    mtime REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS chunks (
    id     INTEGER PRIMARY KEY,
    doc_id INTEGER NOT NULL REFERENCES docs(id) ON DELETE CASCADE,
    n      INTEGER NOT NULL,
    text   TEXT NOT NULL
);
CREATE VIRTUAL TABLE IF NOT EXISTS chunks_fts USING fts5(
    text, chunk_id UNINDEXED, doc_id UNINDEXED, tokenize='unicode61'
);
CREATE INDEX IF NOT EXISTS idx_chunks_doc ON chunks(doc_id);
CREATE TABLE IF NOT EXISTS doc_meta (
    doc_id   INTEGER PRIMARY KEY REFERENCES docs(id) ON DELETE CASCADE,
    lang     TEXT NOT NULL DEFAULT 'id',
    keywords TEXT NOT NULL DEFAULT '[]',
    summary  TEXT NOT NULL DEFAULT ''
);
CREATE TABLE IF NOT EXISTS events (
    id       INTEGER PRIMARY KEY,
    ts       REAL NOT NULL,
    kind     TEXT NOT NULL,
    query    TEXT NOT NULL DEFAULT '',
    doc_path TEXT NOT NULL DEFAULT '',
    chunk_n  INTEGER NOT NULL DEFAULT -1
);
CREATE INDEX IF NOT EXISTS idx_events_q ON events(query, kind);
CREATE INDEX IF NOT EXISTS idx_events_ts ON events(ts);
CREATE TABLE IF NOT EXISTS query_terms (
    query   TEXT PRIMARY KEY,
    terms   TEXT NOT NULL DEFAULT '{}',
    updated REAL NOT NULL
);
"""


# ------------------------------------------------------------- util teks
def _tokens(text: str) -> list[str]:
    return [t for t in re.findall(r"[a-z0-9_]+", text.lower())
            if len(t) >= 3 and t not in STOPWORDS and not t.isdigit()]


def _sentences(text: str) -> list[str]:
    text = re.sub(r"^#+\s*", "", text.strip(), flags=re.M)
    parts = re.split(r"(?<=[.!?])\s+|\n+", text.strip())
    return [p.strip() for p in parts if len(p.strip()) >= 12]


def _detect_lang(text: str) -> str:
    toks = set(re.findall(r"[a-z]+", text.lower()))
    id_hits = len(toks & STOP_ID)
    en_hits = len(toks & STOP_EN)
    return "en" if en_hits > id_hits else "id"


def _keywords(text: str, topn: int = KEYWORD_TOPN) -> list[str]:
    freq: dict[str, int] = {}
    for t in _tokens(text):
        freq[t] = freq.get(t, 0) + 1
    return [w for w, _ in sorted(freq.items(), key=lambda kv: (-kv[1], kv[0]))[:topn]]


def _summarize(text: str, keywords: list[str]) -> str:
    kw = set(keywords)
    sents = _sentences(text)
    if not sents:
        return text.strip()[:300]
    scored = []
    for s in sents:
        toks = set(_tokens(s))
        overlap = len(toks & kw)
        scored.append((overlap, -len(s), s))
    scored.sort(reverse=True)
    top = [s for _, _, s in scored[:SUMMARY_SENTENCES]]
    # kembalikan urutan asli kemunculan
    order = {s: i for i, s in enumerate(sents)}
    top.sort(key=lambda s: order.get(s, 0))
    return " ".join(top)[:600]


def _enrich(con: sqlite3.Connection, doc_id: int, text: str) -> dict:
    lang = _detect_lang(text)
    kws = _keywords(text)
    summ = _summarize(text, kws)
    con.execute(
        "INSERT OR REPLACE INTO doc_meta(doc_id, lang, keywords, summary)"
        " VALUES (?, ?, ?, ?)",
        (doc_id, lang, json.dumps(kws, ensure_ascii=False), summ),
    )
    return {"lang": lang, "keywords": kws, "summary": summ}


# ------------------------------------------------------------- indexer
def chunk_text(text: str, size: int = CHUNK_SIZE, overlap: int = CHUNK_OVERLAP):
    text = text.strip()
    if not text:
        return
    paras = [p.strip() for p in text.split("\n\n") if p.strip()]
    buf = ""
    for p in paras:
        if len(buf) + len(p) + 2 <= size:
            buf = (buf + "\n\n" + p).strip() if buf else p
        else:
            if buf:
                yield buf
                buf = buf[-overlap:] + "\n\n" + p if len(buf) > overlap else p
                if len(buf) > size:
                    yield buf[:size]
                    buf = buf[size - overlap:]
            else:
                yield p[:size]
                buf = p[size - overlap:] if len(p) > size else ""
    if buf.strip():
        yield buf.strip()


def _connect() -> sqlite3.Connection:
    con = sqlite3.connect(DB_PATH)
    con.execute("PRAGMA foreign_keys = ON")
    return con


def _index_file(con: sqlite3.Connection, path: str) -> dict | None:
    try:
        with open(path, encoding="utf-8") as f:
            text = f.read().strip()
    except Exception:
        return None
    if not text:
        return None
    mtime = os.path.getmtime(path)
    row = con.execute("SELECT id, mtime FROM docs WHERE path = ?", (path,)).fetchone()
    if row and abs(row[1] - mtime) < 1e-6:
        return {"doc_id": row[0], "skipped": True, "chunks": 0}
    if row:
        con.execute("DELETE FROM docs WHERE id = ?", (row[0],))
    fn = os.path.basename(path)
    cur = con.execute(
        "INSERT INTO docs(path, title, mtime) VALUES (?, ?, ?)", (path, fn, mtime))
    doc_id = cur.lastrowid
    n_chunks = 0
    for i, ch in enumerate(chunk_text(text)):
        cur = con.execute(
            "INSERT INTO chunks(doc_id, n, text) VALUES (?, ?, ?)", (doc_id, i, ch))
        con.execute(
            "INSERT INTO chunks_fts(text, chunk_id, doc_id) VALUES (?, ?, ?)",
            (ch, cur.lastrowid, doc_id))
        n_chunks += 1
    meta = _enrich(con, doc_id, text)
    return {"doc_id": doc_id, "skipped": False, "chunks": n_chunks, "meta": meta}


def build_index() -> dict:
    """Index inkremental: hanya file baru/berubah yang diproses. Aman restart."""
    t0 = time.time()
    os.makedirs(DATA_DIR, exist_ok=True)
    for name, b64 in SEED_DOCS.items():
        dest = os.path.join(DATA_DIR, name)
        if not os.path.exists(dest):
            with open(dest, "wb") as f:
                f.write(base64.b64decode(b64))
    con = _connect()
    con.executescript(SCHEMA)
    seen, n_docs, n_chunks = set(), 0, 0
    for dirpath, _dn, filenames in os.walk(DATA_DIR):
        for fn in sorted(filenames):
            if not fn.lower().endswith((".md", ".txt", ".markdown")):
                continue
            path = os.path.join(dirpath, fn)
            seen.add(path)
            res = _index_file(con, path)
            if res and not res.get("skipped"):
                n_docs += 1
                n_chunks += res["chunks"]
    # hapus dokumen yang file-nya sudah tidak ada
    for (doc_id, path) in con.execute("SELECT id, path FROM docs").fetchall():
        if path not in seen:
            con.execute("DELETE FROM docs WHERE id = ?", (doc_id,))
    con.execute("INSERT INTO chunks_fts(chunks_fts) VALUES('optimize')")
    con.commit()
    total_docs = con.execute("SELECT COUNT(*) FROM docs").fetchone()[0]
    con.close()
    return {"docs": total_docs, "indexed_now": n_docs, "chunks_now": n_chunks,
            "seconds": round(time.time() - t0, 2)}


def index_document(doc_id: str, title: str, text: str) -> dict:
    os.makedirs(DATA_DIR, exist_ok=True)
    fname = "".join(c if (c.isalnum() or c in "-_") else "_" for c in doc_id)[:80] or "doc"
    path = os.path.join(DATA_DIR, f"{fname}.md")
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"# {title or doc_id}\n\n{text}")
    # pastikan mtime berubah agar index ulang terpicu
    os.utime(path, (time.time(), time.time()))
    con = _connect()
    con.executescript(SCHEMA)
    res = _index_file(con, path) or {"doc_id": None, "chunks": 0}
    con.execute("INSERT INTO chunks_fts(chunks_fts) VALUES('optimize')")
    con.commit()
    con.close()
    return {"doc_id": doc_id, "chunks": res["chunks"],
            "shard_plan": {"local": res["chunks"]}}


# ------------------------------------------------------------- learning
def _log_event(kind: str, query: str = "", doc_path: str = "", chunk_n: int = -1):
    try:
        con = _connect()
        con.execute(
            "INSERT INTO events(ts, kind, query, doc_path, chunk_n)"
            " VALUES (?, ?, ?, ?, ?)",
            (time.time(), kind, query.strip().lower(), doc_path, chunk_n))
        con.commit()
        con.close()
    except Exception:
        pass


def _get_expansion(query: str) -> list[str]:
    try:
        con = _connect()
        row = con.execute("SELECT terms FROM query_terms WHERE query = ?",
                          (query.strip().lower(),)).fetchone()
        con.close()
    except Exception:
        return []
    if not row:
        return []
    try:
        counts = json.loads(row[0])
    except Exception:
        return []
    qtoks = set(_tokens(query))
    ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    return [t for t, _ in ranked if t not in qtoks][:EXPANSION_TERMS]


def _learn_from_click(query: str, doc_id: int, chunk_n: int):
    """Relevance feedback: serap istilah dari chunk yang diklik ke query_terms."""
    q = query.strip().lower()
    if not q:
        return
    try:
        con = _connect()
        row = con.execute("SELECT text FROM chunks WHERE doc_id = ? AND n = ?",
                          (doc_id, chunk_n)).fetchone()
        if not row:
            con.close()
            return
        counts: dict[str, int] = {}
        old = con.execute("SELECT terms FROM query_terms WHERE query = ?",
                          (q,)).fetchone()
        if old:
            try:
                counts = json.loads(old[0])
            except Exception:
                counts = {}
        qtoks = set(_tokens(q))
        for t in _tokens(row[0]):
            if t not in qtoks:
                counts[t] = counts.get(t, 0) + 1
        # simpan top-N
        top = dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:EXPANSION_KEEP])
        con.execute(
            "INSERT OR REPLACE INTO query_terms(query, terms, updated)"
            " VALUES (?, ?, ?)",
            (q, json.dumps(top, ensure_ascii=False), time.time()))
        con.commit()
        con.close()
    except Exception:
        pass


def _click_boosts(query: str) -> dict[int, int]:
    """{doc_id: jumlah_klik} untuk query ini."""
    try:
        con = _connect()
        rows = con.execute(
            """SELECT d.id, COUNT(*)
               FROM events e JOIN docs d ON d.path = e.doc_path
               WHERE e.kind = 'click' AND e.query = ?
               GROUP BY d.id""",
            (query.strip().lower(),)).fetchall()
        con.close()
        return {r[0]: r[1] for r in rows}
    except Exception:
        return {}


def learn_all() -> dict:
    """Belajar ulang dari seluruh event klik + prune event lama. Untuk cron harian."""
    t0 = time.time()
    con = _connect()
    con.executescript(SCHEMA)
    cutoff = time.time() - EVENT_TTL_DAYS * 86400
    pruned = con.execute("DELETE FROM events WHERE ts < ?", (cutoff,)).rowcount or 0
    con.execute("DELETE FROM query_terms")
    # agregat: query -> chunk yang diklik -> istilah
    rows = con.execute(
        """SELECT e.query, c.text
           FROM events e JOIN docs d ON d.path = e.doc_path
           JOIN chunks c ON c.doc_id = d.id AND c.n = e.chunk_n
           WHERE e.kind = 'click'""").fetchall()
    agg: dict[str, dict[str, int]] = {}
    for q, text in rows:
        q = (q or "").strip().lower()
        if not q or not text:
            continue
        qtoks = set(_tokens(q))
        d = agg.setdefault(q, {})
        for t in _tokens(text):
            if t not in qtoks:
                d[t] = d.get(t, 0) + 1
    n_q = 0
    for q, counts in agg.items():
        top = dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:EXPANSION_KEEP])
        if top:
            con.execute(
                "INSERT OR REPLACE INTO query_terms(query, terms, updated)"
                " VALUES (?, ?, ?)",
                (q, json.dumps(top, ensure_ascii=False), time.time()))
            n_q += 1
    con.commit()
    con.close()
    return {"queries_learned": n_q, "events_pruned": pruned,
            "seconds": round(time.time() - t0, 2)}


# ------------------------------------------------------------- search
def _fts_query(q: str) -> str:
    raw = [t for t in q.split() if t.strip('*\"')]
    # buang stopword & token pendek — kalau habis, pakai mentah (fallback)
    toks = [t for t in raw
            if len(t) >= 3 and t.lower() not in STOPWORDS and not t.isdigit()]
    if not toks:
        toks = raw[:8]
    if not toks:
        return ""
    return " AND ".join(f'"{t.replace(chr(34), chr(34)*2)}"*' for t in toks)


def search(query: str, limit: int = 10, log: bool = True) -> list[dict]:
    query = query.strip()
    if not query or not os.path.exists(DB_PATH):
        return []
    fts_q = _fts_query(query)
    if not fts_q:
        return []
    exp = _get_expansion(query)
    if exp:
        exp_q = " OR ".join(f'"{t}"*' for t in exp)
        fts_q = f"({fts_q}) OR ({exp_q})"
    con = _connect()
    con.row_factory = sqlite3.Row
    rows = con.execute(
        """
        SELECT c.id AS chunk_id, c.doc_id, c.n, c.text, d.path, d.title,
               bm25(chunks_fts) AS rank,
               snippet(chunks_fts, 0, '<b>', '</b>', ' … ', ?) AS snip
        FROM chunks_fts
        JOIN chunks c ON c.id = chunks_fts.chunk_id
        JOIN docs d   ON d.id = chunks_fts.doc_id
        WHERE chunks_fts MATCH ?
        ORDER BY rank
        LIMIT ?
        """,
        (SNIPPET_TOKENS, fts_q, limit * 3),
    ).fetchall()
    con.close()
    boosts = _click_boosts(query)
    hits = []
    for r in rows:
        base = -r["rank"]
        b = boosts.get(r["doc_id"], 0)
        score = base + (CLICK_BETA * math.log1p(b) if b else 0.0)
        hits.append({
            "doc_id": r["doc_id"],
            "title": r["title"],
            "path": r["path"],
            "chunk": r["n"],
            "score": round(score, 3),
            "snippet": r["snip"],
            "backend": "local",
            "meta": {"clicks": b} if b else {},
        })
    hits.sort(key=lambda h: -h["score"])
    hits = hits[:limit]
    if log:
        _log_event("search", query=query)
    return hits


# ------------------------------------------------------------- fitur v0.7
def record_feedback(query: str, doc_id: int, chunk_n: int) -> dict:
    con = _connect()
    row = con.execute("SELECT path FROM docs WHERE id = ?", (doc_id,)).fetchone()
    con.close()
    if not row:
        raise ValueError("doc_id tidak dikenal")
    _log_event("click", query=query, doc_path=row[0], chunk_n=chunk_n)
    _learn_from_click(query, doc_id, chunk_n)
    return {"ok": True, "query": query.strip().lower()}


def _lev(a: str, b: str) -> int:
    if abs(len(a) - len(b)) > 3:
        return 99
    dp = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        ndp = [i]
        for j, cb in enumerate(b, 1):
            ndp.append(min(dp[j] + 1, ndp[-1] + 1, dp[j - 1] + (ca != cb)))
        dp = ndp
    return dp[-1]


def suggest(prefix: str, limit: int = 8) -> dict:
    p = prefix.strip().lower()
    out: dict = {"suggestions": [], "did_you_mean": None}
    if not p or not os.path.exists(DB_PATH):
        return out
    try:
        con = _connect()
        rows = con.execute(
            """SELECT query, COUNT(*) AS c FROM events
               WHERE kind = 'search' AND query LIKE ? || '%'
               GROUP BY query ORDER BY c DESC LIMIT ?""",
            (p, limit)).fetchall()
        out["suggestions"] = [r[0] for r in rows if r[0] != p]
        if not out["suggestions"]:
            past = [r[0] for r in con.execute(
                "SELECT DISTINCT query FROM events WHERE kind='search' LIMIT 500").fetchall()]
            best, best_d = None, 99
            for q in past:
                if q == p or not q:
                    continue
                d = _lev(p, q)
                if d < best_d:
                    best, best_d = q, d
            if best and best_d <= max(2, len(p) // 4):
                out["did_you_mean"] = best
        con.close()
    except Exception:
        pass
    return out


def trends(days: int = TREND_DAYS) -> dict:
    out: dict = {"top_queries": [], "top_docs": [],
                 "total_searches": 0, "total_clicks": 0, "days": days}
    if not os.path.exists(DB_PATH):
        return out
    try:
        con = _connect()
        cutoff = time.time() - days * 86400
        out["top_queries"] = [
            {"query": r[0], "searches": r[1]}
            for r in con.execute(
                """SELECT query, COUNT(*) AS c FROM events
                   WHERE kind='search' AND ts > ? GROUP BY query
                   ORDER BY c DESC LIMIT 10""", (cutoff,)).fetchall()]
        out["top_docs"] = [
            {"title": r[0], "clicks": r[1]}
            for r in con.execute(
                """SELECT d.title, COUNT(*) AS c FROM events e
                   JOIN docs d ON d.path = e.doc_path
                   WHERE e.kind='click' AND e.ts > ?
                   GROUP BY d.title ORDER BY c DESC LIMIT 10""",
                (cutoff,)).fetchall()]
        out["total_searches"] = con.execute(
            "SELECT COUNT(*) FROM events WHERE kind='search' AND ts > ?",
            (cutoff,)).fetchone()[0]
        out["total_clicks"] = con.execute(
            "SELECT COUNT(*) FROM events WHERE kind='click' AND ts > ?",
            (cutoff,)).fetchone()[0]
        con.close()
    except Exception:
        pass
    return out


def related(doc_id: int, limit: int = 5) -> list[dict]:
    try:
        con = _connect()
        con.row_factory = sqlite3.Row
        me = con.execute("SELECT keywords FROM doc_meta WHERE doc_id = ?",
                         (doc_id,)).fetchone()
        if not me:
            con.close()
            return []
        kw = set(json.loads(me["keywords"]))
        if not kw:
            con.close()
            return []
        rows = con.execute(
            """SELECT m.doc_id, d.title, d.path, m.keywords, m.summary
               FROM doc_meta m JOIN docs d ON d.id = m.doc_id
               WHERE m.doc_id != ?""", (doc_id,)).fetchall()
        con.close()
    except Exception:
        return []
    scored = []
    for r in rows:
        try:
            k2 = set(json.loads(r["keywords"]))
        except Exception:
            continue
        if not k2:
            continue
        inter = len(kw & k2)
        if not inter:
            continue
        jacc = inter / len(kw | k2)
        scored.append((jacc, {"doc_id": r["doc_id"], "title": r["title"],
                              "path": r["path"], "score": round(jacc, 3),
                              "summary": r["summary"][:200]}))
    scored.sort(key=lambda x: -x[0])
    return [s for _, s in scored[:limit]]


def answer(query: str) -> dict:
    hits = search(query, limit=5, log=False)
    if not hits:
        _log_event("search", query=query)
        return {"query": query, "answer": None, "source": None}
    qtoks = set(_tokens(query)) | set(_get_expansion(query))
    best, best_score, best_hit = None, -1, None
    for h in hits:
        con = _connect()
        row = con.execute("SELECT text FROM chunks WHERE doc_id = ? AND n = ?",
                          (h["doc_id"], h["chunk"])).fetchone()
        con.close()
        if not row:
            continue
        for s in _sentences(row[0]):
            toks = set(_tokens(s))
            ov = len(toks & qtoks)
            # utama: jumlah overlap; penyeimbang: kalimat utuh > potongan pendek
            score = ov * 1000 + min(len(s), 300)
            if ov > 0 and score > best_score:
                best, best_score, best_hit = s, score, h
    _log_event("search", query=query)
    if not best:
        return {"query": query, "answer": None, "source": None}
    return {"query": query, "answer": best,
            "source": {"doc_id": best_hit["doc_id"], "title": best_hit["title"],
                       "chunk": best_hit["chunk"]}}


def _html_to_text(html: str) -> tuple[str, str]:
    title = ""
    m = re.search(r"<title[^>]*>(.*?)</title>", html, re.I | re.S)
    if m:
        title = re.sub(r"\s+", " ", m.group(1)).strip()[:200]
    text = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", html, flags=re.I | re.S)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\s+", " ", text).strip()
    # unescape entitas umum tanpa html module
    for ent, ch in (("&amp;", "&"), ("&lt;", "<"), ("&gt;", ">"),
                    ("&quot;", '"'), ("&#39;", "'"), ("&nbsp;", " ")):
        text = text.replace(ent, ch)
    return title, text


def ingest_url(url: str) -> dict:
    url = url.strip()
    try:
        parts = urllib.parse.urlparse(url)
    except Exception:
        raise ValueError("URL tidak valid")
    if parts.scheme not in ("http", "https") or not parts.netloc:
        raise ValueError("hanya URL http/https yang didukung")
    req = urllib.request.Request(
        url, headers={"User-Agent": "CARI/0.7 (+personal-search-engine)"})
    try:
        with urllib.request.urlopen(req, timeout=INGEST_TIMEOUT) as r:
            ctype = r.headers.get("Content-Type", "")
            if "html" not in ctype and "text" not in ctype:
                raise ValueError(f"tipe konten tidak didukung: {ctype or 'unknown'}")
            raw = r.read(INGEST_MAX_BYTES + 1)
    except ValueError:
        raise
    except Exception as e:
        raise ValueError(
            "gagal fetch URL "
            f"({type(e).__name__}: {e}). Di PythonAnywhere gratis, situs harus "
            "masuk whitelist outbound — coba URL dari situs umum populer.") from e
    if len(raw) > INGEST_MAX_BYTES:
        raise ValueError("halaman terlalu besar (>700KB)")
    m = re.search(r"charset=([\w-]+)", ctype or "")
    html = raw.decode(m.group(1) if m else "utf-8", errors="replace")
    title, text = _html_to_text(html)
    if len(text) < 50:
        raise ValueError("tidak cukup teks yang bisa diekstrak dari halaman ini")
    slug = re.sub(r"[^a-z0-9]+", "-", (parts.netloc + parts.path).lower()).strip("-")[:60]
    doc_id = f"web-{slug or 'page'}-{int(time.time()) % 100000}"
    res = index_document(doc_id, title or doc_id, text[:20000])
    res["url"] = url
    res["title"] = title or doc_id
    return res


def reindex_full() -> dict:
    if os.path.exists(DB_PATH):
        os.remove(DB_PATH)
    return build_index()


# ------------------------------------------------------------- WSGI app
CORS = [
    ("Access-Control-Allow-Origin", "*"),
    ("Access-Control-Allow-Methods", "GET, POST, OPTIONS"),
    ("Access-Control-Allow-Headers", "X-API-Key, Content-Type"),
]


def _json(start_response, status: str, obj, code: int = 200):
    body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
    start_response(f"{code} {status}", [("Content-Type", "application/json; charset=utf-8"),
                                       ("Content-Length", str(len(body))), *CORS])
    return [body]


def _read_json(environ) -> dict:
    try:
        n = int(environ.get("CONTENT_LENGTH") or 0)
    except ValueError:
        n = 0
    raw = environ["wsgi.input"].read(n) if n > 0 else b""
    try:
        return json.loads(raw.decode("utf-8")) if raw else {}
    except Exception:
        return {}


def _query_params(environ) -> dict:
    return {k: v[0] for k, v in
            urllib.parse.parse_qs(environ.get("QUERY_STRING", "")).items() if v}


def _authorized(environ) -> tuple[bool, str]:
    expected = os.environ.get("CARI_API_KEY", "")
    if not expected:
        return False, "CARI_API_KEY belum di-set di WSGI configuration file"
    got = environ.get("HTTP_X_API_KEY", "")
    if not got or not hmac.compare_digest(got, expected):
        return False, "API key tidak valid / tidak ada"
    return True, ""


# Build index sekali saat worker pertama start (inkremental — aman restart).
_build_stats = build_index()


def application(environ, start_response):
    method = environ.get("REQUEST_METHOD", "GET")
    path = environ.get("PATH_INFO", "/") or "/"

    if method == "OPTIONS":
        start_response("200 OK", [("Content-Length", "0"), *CORS])
        return [b""]

    if path == "/health" and method == "GET":
        return _json(start_response, "OK",
                     {"status": "ok", "version": VERSION, "engine": ENGINE_NAME})

    if path == "/ready" and method == "GET":
        return _json(start_response, "OK", {"ready": True, "engine": ENGINE_NAME})

    # --- sisanya butuh API key ---
    ok, msg = _authorized(environ)
    if not ok:
        return _json(start_response, "Unauthorized", {"detail": msg}, 401)

    if path == "/search" and method == "POST":
        body = _read_json(environ)
        q = str(body.get("query", "")).strip()
        try:
            limit = max(1, min(50, int(body.get("limit", 10))))
        except (TypeError, ValueError):
            limit = 10
        if not q:
            return _json(start_response, "Bad Request",
                         {"detail": "query wajib diisi"}, 400)
        try:
            hits = search(q, limit)
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Pencarian gagal: {e}"}, 502)
        return _json(start_response, "OK",
                     {"query": q, "engine": ENGINE_NAME, "count": len(hits), "hits": hits})

    if path == "/documents" and method == "POST":
        body = _read_json(environ)
        doc_id = str(body.get("doc_id", "")).strip()
        text = str(body.get("text", ""))
        title = str(body.get("title", ""))
        if not doc_id or not text.strip():
            return _json(start_response, "Bad Request",
                         {"detail": "doc_id dan text wajib diisi"}, 400)
        try:
            res = index_document(doc_id, title, text)
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Index gagal: {e}"}, 502)
        return _json(start_response, "Created", res, 201)

    if path == "/backends" and method == "GET":
        return _json(start_response, "OK",
                     [{"name": "local", "tier": "fts", "state": "ok",
                       "needs_live_key": False, "quota_used_bytes": 0,
                       "quota_bytes": 0, "quota_pct": 0.0,
                       "learn": True, "version": VERSION}])

    # --- fitur v0.7 ---
    if path == "/feedback" and method == "POST":
        body = _read_json(environ)
        q = str(body.get("query", "")).strip()
        try:
            doc_id = int(body.get("doc_id", 0))
            chunk_n = int(body.get("chunk", 0))
        except (TypeError, ValueError):
            return _json(start_response, "Bad Request",
                         {"detail": "doc_id/chunk harus angka"}, 400)
        if not q or not doc_id:
            return _json(start_response, "Bad Request",
                         {"detail": "query dan doc_id wajib diisi"}, 400)
        try:
            res = record_feedback(q, doc_id, chunk_n)
        except ValueError as e:
            return _json(start_response, "Bad Request", {"detail": str(e)}, 400)
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Feedback gagal: {e}"}, 502)
        return _json(start_response, "OK", res)

    if path == "/suggest" and method == "GET":
        qp = _query_params(environ)
        return _json(start_response, "OK",
                     suggest(qp.get("q", ""), limit=8))

    if path == "/trends" and method == "GET":
        return _json(start_response, "OK", trends())

    if path == "/related" and method == "GET":
        qp = _query_params(environ)
        try:
            doc_id = int(qp.get("doc_id", 0))
        except (TypeError, ValueError):
            doc_id = 0
        if not doc_id:
            return _json(start_response, "Bad Request",
                         {"detail": "doc_id wajib diisi"}, 400)
        return _json(start_response, "OK",
                     {"doc_id": doc_id, "related": related(doc_id)})

    if path == "/answer" and method == "POST":
        body = _read_json(environ)
        q = str(body.get("query", "")).strip()
        if not q:
            return _json(start_response, "Bad Request",
                         {"detail": "query wajib diisi"}, 400)
        try:
            res = answer(q)
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Answer gagal: {e}"}, 502)
        return _json(start_response, "OK", res)

    if path == "/ingest" and method == "POST":
        body = _read_json(environ)
        url = str(body.get("url", "")).strip()
        if not url:
            return _json(start_response, "Bad Request",
                         {"detail": "url wajib diisi"}, 400)
        try:
            res = ingest_url(url)
        except ValueError as e:
            return _json(start_response, "Bad Request", {"detail": str(e)}, 400)
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Ingest gagal: {e}"}, 502)
        return _json(start_response, "Created", res, 201)

    if path == "/learn" and method == "POST":
        try:
            res = learn_all()
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Learn gagal: {e}"}, 502)
        return _json(start_response, "OK", res)

    if path == "/reindex" and method == "POST":
        try:
            res = reindex_full()
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Reindex gagal: {e}"}, 502)
        return _json(start_response, "OK", res)

    return _json(start_response, "Not Found", {"detail": "tidak dikenal"}, 404)


# Tes lokal: CARI_API_KEY=rahasia python wsgi_api.py -> http://localhost:8000/health
if __name__ == "__main__":
    from wsgiref.simple_server import make_server
    port = int(os.environ.get("PORT", "8000"))
    print(f"CARI WSGI {VERSION} — index: {_build_stats} — http://localhost:{port}")
    make_server("127.0.0.1", port, application).serve_forever()
