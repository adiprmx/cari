"""CARI Server v0.8 "Web Mode" — 100% stdlib, tanpa pip install.

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
    * POST /ingest {url}: fetch halaman -> ekstrak teks -> index otomatis.
      Jika situs di luar whitelist, otomatis dicoba via Jina Reader proxy.
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
  Pilar 4 — Web Mode / metasearch (v0.8+):
    * GET /web/search?q=... : cari di web lewat 14 backend resmi tanpa API key
      (v0.9): Wikipedia, DuckDuckGo Instant Answer, DuckDuckGo Lite (hasil
      web umum), Qwant (hasil web umum), Hacker News (Algolia),
      Stack Exchange, GitHub (user + repo), OpenAlex (paper), arXiv (paper),
      PubMed (medis), Open Library (buku), Internet Archive (arsip),
      npm (paket JS), Wikidata (entitas). Semua berjalan paralel;
      yang ke-block whitelist diam-diam dilewati (try/except per backend).
    * Setiap hasil web OTOMATIS di-index permanen ke database lokal
      (path web/<sumber>/<slug>) -> index tumbuh dari pencarianmu:
      mesin yang benar-benar belajar sendiri.
    * Hasil mentah di-cache 24 jam (tabel web_cache, v0.8.3: kunci cache
      berversi -> otomatis invalid tiap upgrade; hasil kosong tidak di-cache).
    * GitHub backend punya backoff 10 menit saat kena 403/429 (IP gratisan
      dipakai bersama, rawan rate-limit).
    * Siap Brave Search API: cukup set env BRAVE_API_KEY di WSGI config,
      backend brave ikut dipakai (perlu api.search.brave.com di-whitelist).

Deploy sama seperti v0.6: upload file ini ke ~/cari-server, WSGI config:
    import os, sys
    sys.path.insert(0, '/home/USERNAME/cari-server')
    os.environ['CARI_API_KEY'] = 'kunci-rahasia-buatanmu'
    from wsgi_api import application
"""

from __future__ import annotations

import base64
import concurrent.futures
import hashlib
import hmac
import html as htmlmod
import json
import math
import os
import re
import sqlite3
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

VERSION = "0.9.0"
ENGINE_NAME = "local"

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
DB_PATH = os.path.join(BASE_DIR, "cari.db")

# Dokumen bawaan (base64) — di-inject saat build. {nama_file: b64}
# Dokumen bawaan (base64) — dibuat otomatis dari seeds/*.md, jangan edit manual.
SEED_DOCS: dict[str, str] = {
    'budgeting-50-30-20.md': 'IyBCdWRnZXRpbmcgNTAtMzAtMjAKCkF0dXJhbiBzZWRlcmhhbmEgbWVtYmFnaSBwZW5naGFzaWxhbiBidWxhbmFuOgoKLSA1MCUga2VidXR1aGFuIChuZWVkcyk6IGtvcywgbWFrYW4sIHRyYW5zcG9ydCwgcHVsc2EsIGNpY2lsYW4gd2FqaWIuCi0gMzAlIGtlaW5naW5hbiAod2FudHMpOiBqYWphbiwgbm9uZ2tyb25nLCBsYW5nZ2FuYW4gaGlidXJhbi4KLSAyMCUgdGFidW5nYW4gJiBpbnZlc3Rhc2k6IGRhbmEgZGFydXJhdCwgaW52ZXN0YXNpLgoKQ29udG9oIGdhamkgNSBqdXRhOiAyLDUganQga2VidXR1aGFuLCAxLDUganQga2VpbmdpbmFuLCAxIGp0IGRpdGFidW5nL2RpaW52ZXN0YXNpa2FuLgoKTGFuZ2thaCBtdWxhaToKCjEuIENhdGF0IHNlbXVhIHBlbmdlbHVhcmFuIDEgYnVsYW4gKGFwbGlrYXNpIGF0YXUgbm90ZXMgSFApLgoyLiBLZWxvbXBva2thbiBrZSAzIHBvcyBkaSBhdGFzLgozLiBQb3RvbmcgcG9zIGtlaW5naW5hbiB5YW5nIG1lbWJlbmdrYWsg4oCUIGJpYXNhbnlhIGxhbmdnYW5hbiB0YWsgdGVycGFrYWkgZGFuIGphamFuIGltcHVsc2lmLgoKS3VuY2k6IGJheWFyIGRpcmltdSBkdWx1IOKAlCBzaXNpaGthbiAyMCUgZGkgYXdhbCBidWxhbiAoYXV0by1kZWJldCksIGJ1a2FuIGRhcmkgc2lzYS4gWWFuZyB0aWRhayBkaXVrdXIgdGlkYWsgYmlzYSBkaWtlbG9sYS4K',
    'cara-kerja-internet.md': 'IyBDYXJhIEtlcmphIEludGVybmV0CgpJbnRlcm5ldCBhZGFsYWggamFyaW5nYW4ga29tcHV0ZXIgZ2xvYmFsIHlhbmcgc2FsaW5nIHRlcmh1YnVuZy4KClNldGlhcCBwZXJhbmdrYXQgcHVueWEgYWxhbWF0IElQLCBtaXMuIGAxNDIuMjUwLjE5MC4xNGAuIEthcmVuYSBzdWxpdCBkaWhhZmFsLCBhZGEgRE5TIChEb21haW4gTmFtZSBTeXN0ZW0pIOKAlCBidWt1IHRlbGVwb24gaW50ZXJuZXQgeWFuZyBtZW5lcmplbWFoa2FuIGBnb29nbGUuY29tYCBtZW5qYWRpIGFsYW1hdCBJUC4KClNhYXQga2FtdSBidWthIHNpdHVzLCB0ZXJqYWRpOgoKMS4gQnJvd3NlciB0YW55YSBETlM6ICJiZXJhcGEgSVAgZ29vZ2xlLmNvbT8iCjIuIEJyb3dzZXIgbWVtYnVrYSBrb25la3NpIFRDUCBrZSBJUCBpdHUgKGJpYXNhbnlhIHBvcnQgNDQzIHVudHVrIEhUVFBTKS4KMy4gQnJvd3NlciBraXJpbSBIVFRQIHJlcXVlc3Q6IGBHRVQgLyBIVFRQLzEuMWAuCjQuIFNlcnZlciBtZW5qYXdhYiBkZW5nYW4gSFRUUCByZXNwb25zZSBiZXJpc2kgSFRNTC4KNS4gQnJvd3NlciBtZS1yZW5kZXIgaGFsYW1hbi4KCkhUVFBTID0gSFRUUCArIGVua3JpcHNpIFRMUywgc2VoaW5nZ2EgZGF0YSB0aWRhayBiaXNhIGRpaW50aXAgZGkgdGVuZ2FoIGphbGFuLiBHZW1ib2sgZGkgYWRkcmVzcyBiYXIgbWVuYW5kYWthbm55YS4KCkRhdGEgZGlwZWNhaCBqYWRpIHBha2V0LXBha2V0IGtlY2lsIHlhbmcgZGlydXRla2FuIGxld2F0IGJhbnlhayByb3V0ZXIgc2ViZWx1bSBkaXN1c3VuIHVsYW5nIGRpIHR1anVhbi4gSW5pbGFoIGtlbmFwYSBpbnRlcm5ldCB0ZXRhcCBqYWxhbiB3YWxhdSBzYXR1IGphbHVyIHB1dHVzLgo=',
    'catatan-efektif.md': 'IyBDYXRhdGFuIEVmZWt0aWYKCk1lbnlhbGluIHNsaWRlIHZlcmJhdGltIGl0dSBtZW5pcHUg4oCUIHRlcmFzYSBwYWhhbSBwYWRhaGFsIHRpZGFrLiBUdWxpcyBkZW5nYW4ga2F0YS1rYXRhbXUgc2VuZGlyaS4KClByaW5zaXAgY2F0YXRhbiBhdG9taWs6IDEgY2F0YXRhbiA9IDEgaWRlLiBDYXRhdGFuIHBlbmRlayB5YW5nIGZva3VzIGxlYmloIG11ZGFoIGRpY2FyaSBkYW4gZGlodWJ1bmdrYW4gZGFyaXBhZGEgMSBkb2t1bWVuIHJha3Nhc2EuCgpNZXRvZGUgY2VwYXQ6CgotIEp1ZHVsIGplbGFzOiAiY2FyYSBrZXJqYSBETlMiLCBidWthbiAiY2F0YXRhbiAxMiIuCi0gUG9pbi1wb2luLCBidWthbiBwYXJhZ3JhZiBwYW5qYW5nLgotIENvbnRvaCBrb25rcmV0IHRpYXAga29uc2VwIGFic3RyYWsuCi0gVHVsaXMgcGVydGFueWFhbiB5YW5nIGJlbHVtIHRlcmphd2FiLgoKUmV2aWV3OiBiYWNhIHVsYW5nIGNhdGF0YW4gZGFsYW0gMjQgamFtIChtZW5ndWF0a2FuIG1lbW9yaSAyeCBsaXBhdCksIGxhbHUgdWppIGRpcmltdSB0YW5wYSBtZWxpaGF0IOKAlCBhY3RpdmUgcmVjYWxsLgoKSHVidW5na2FuIGFudGFyLWNhdGF0YW4gKG1pcy4gImxpaGF0IGp1Z2E6IGNhcmEga2VyamEgaW50ZXJuZXQiKSBhZ2FyIGphZGkgamFyaW5nYW4gcGVuZ2V0YWh1YW4sIGJ1a2FuIHR1bXB1a2FuIGFyc2lwIG1hdGkuCg==',
    'catatan-python.md': 'IyBDYXRhdGFuIEJlbGFqYXIgUHl0aG9uCgpQeXRob24gYWRhbGFoIGJhaGFzYSBwZW1yb2dyYW1hbiB5YW5nIHBvcHVsZXIgdW50dWsgZGF0YSBzY2llbmNlIGRhbiB3ZWIgZGV2ZWxvcG1lbnQuCkZ1bmdzaSBkaWRlZmluaXNpa2FuIGRlbmdhbiBrYXRhIGt1bmNpIGBkZWZgLCBzZWRhbmdrYW4gY2xhc3MgZGVuZ2FuIGBjbGFzc2AuCgpMaXN0IGNvbXByZWhlbnNpb24gYWRhbGFoIGNhcmEgcmluZ2thcyBtZW1idWF0IGxpc3Q6Cmhhc2lsID0gW3gqMiBmb3IgeCBpbiByYW5nZSgxMCkgaWYgeCAlIDIgPT0gMF0KClZpcnR1YWwgZW52aXJvbm1lbnQgc2ViYWlrbnlhIHNlbGFsdSBkaXBha2FpIHBlciBwcm95ZWs6CnB5dGhvbiAtbSB2ZW52IC52ZW52CgpVbnR1ayBIVFRQIHJlcXVlc3QsIGxpYnJhcnkgYHJlcXVlc3RzYCBhdGF1IHN0ZGxpYiBgdXJsbGliYCBiaXNhIGRpcGFrYWkuClVudHVrIHdlYiBzY3JhcGluZyBzZWRlcmhhbmEsIEJlYXV0aWZ1bFNvdXAgbWVtYmFudHUgcGFyc2luZyBIVE1MLgo=',
    'dana-darurat.md': 'IyBEYW5hIERhcnVyYXQKCkRhbmEgZGFydXJhdCBhZGFsYWggdGFidW5nYW4ga2h1c3VzIHVudHVrIGtlamFkaWFuIHRhayB0ZXJkdWdhOiBQSEssIHNha2l0LCBtb3RvciBydXNhay4gQnVrYW4gdW50dWsgZGlza29uIGF0YXUgZ2FkZ2V0LgoKQmVzYXJhbiBpZGVhbDoKCi0gTGFqYW5nIHRhbnBhIHRhbmdndW5nYW46IDN4IHBlbmdlbHVhcmFuIGJ1bGFuYW4uCi0gU3VkYWggbWVuaWthaDogNnguCi0gRnJlZWxhbmNlci9wZW5naGFzaWxhbiB0YWsgdGV0YXA6IDEyeC4KCkNvbnRvaDogcGVuZ2VsdWFyYW4gMyBqdC9idWxhbiBkYW4gbWFzaWggbGFqYW5nIOKGkiB0YXJnZXQgOSBqdC4KClRlbXBhdCBzaW1wYW46IGhhcnVzIGxpa3VpZCAobXVkYWggZGljYWlya2FuKSBkYW4gdGVycGlzYWggZGFyaSByZWtlbmluZyBoYXJpYW4g4oCUIHRhYnVuZ2FuIGJpYXNhLCByZWtzYWRhbmEgcGFzYXIgdWFuZywgYXRhdSBkZXBvc2l0byB5YW5nIGJpc2EgZGljYWlya2FuIGNlcGF0LiBCVUtBTiBkaSBzYWhhbSBhdGF1IGtyaXB0by4KCkNhcmEgbWVuZ3VtcHVsa2FuOiBzaXNpaGthbiBub21pbmFsIHRldGFwIHRpYXAgZ2FqaWFuIChtaXMuIDUwMCByYiksIGFuZ2dhcCBzZWJhZ2FpICJ0YWdpaGFuIi4gTXVsYWkgZGFyaSB0YXJnZXQga2VjaWwgZHVsdSAoMSBqdCBwZXJ0YW1hKSBhZ2FyIHRlcm1vdGl2YXNpLgoKUGFrYWkgaGFueWEgdW50dWsgZGFydXJhdCBiZXR1bGFuLCBkYW4gaXNpIHVsYW5nIHNldGVsYWggZGlwYWthaS4K',
    'git-cheatsheet.md': 'IyBHaXQgQ2hlYXRzaGVldAoKR2l0IGFkYWxhaCB2ZXJzaW9uIGNvbnRyb2wgdW50dWsgbWVsYWNhayBwZXJ1YmFoYW4ga29kZS4KClNldHVwIGF3YWw6CgpgYGAKZ2l0IGNvbmZpZyAtLWdsb2JhbCB1c2VyLm5hbWUgIk5hbWFtdSIKZ2l0IGNvbmZpZyAtLWdsb2JhbCB1c2VyLmVtYWlsICJlbWFpbEBrYW11LmNvbSIKYGBgCgpNdWxhaSByZXBvOgoKYGBgCmdpdCBpbml0CmdpdCBhZGQgLgpnaXQgY29tbWl0IC1tICJwZXNhbiBjb21taXQgeWFuZyBqZWxhcyIKYGBgCgpDZWsgc3RhdHVzIGRhbiByaXdheWF0OgoKYGBgCmdpdCBzdGF0dXMKZ2l0IGxvZyAtLW9uZWxpbmUKZ2l0IGRpZmYKYGBgCgpCcmFuY2ggdW50dWsga2VyamEgcGFyYWxlbDoKCmBgYApnaXQgYnJhbmNoIGZpdHVyLWJhcnUKZ2l0IHN3aXRjaCBmaXR1ci1iYXJ1CmdpdCBzd2l0Y2ggLWMgZml0dXItYmFydSAgICMgYnVhdCArIHBpbmRhaCBzZWthbGlndXMKYGBgCgpHYWJ1bmcgYnJhbmNoOgoKYGBgCmdpdCBzd2l0Y2ggbWFpbgpnaXQgbWVyZ2UgZml0dXItYmFydQpgYGAKClJlbW90ZSAoR2l0SHViKToKCmBgYApnaXQgcmVtb3RlIGFkZCBvcmlnaW4gaHR0cHM6Ly9naXRodWIuY29tL3VzZXIvcmVwby5naXQKZ2l0IHB1c2ggLXUgb3JpZ2luIG1haW4KZ2l0IHB1bGwKYGBgCgpNZW55aW1wYW4gc2VtZW50YXJhOiBgZ2l0IHN0YXNoYCwga2VtYmFsaWthbiBkZW5nYW4gYGdpdCBzdGFzaCBwb3BgLgoKQmF0YWxrYW4gcGVydWJhaGFuOiBgZ2l0IHJlc3RvcmUgZmlsZWAgKGJlbHVtIGRpLWNvbW1pdCksIGBnaXQgcmV2ZXJ0IEhFQURgIChhbWFuLCBidWF0IGNvbW1pdCBiYXJ1IHlhbmcgbWVtYmF0YWxrYW4pLgoKSmFuZ2FuIHBha2FpIGBnaXQgcHVzaCAtLWZvcmNlYCBkaSBicmFuY2ggeWFuZyBkaXBha2FpIG9yYW5nIGxhaW4uCg==',
    'gizi-seimbang.md': 'IyBHaXppIFNlaW1iYW5nCgpQYW5kdWFuICJJc2kgUGlyaW5na3UiOiBzZXRlbmdhaCBwaXJpbmcgc2F5dXIgZGFuIGJ1YWgsIHNlcGVyZW1wYXQgbGF1ayBwcm90ZWluLCBzZXBlcmVtcGF0IG1ha2FuYW4gcG9rb2suCgpQcm90ZWluOiB0ZWx1ciwgYXlhbSwgaWthbiwgdGVtcGUsIHRhaHUg4oCUIHBlbnRpbmcgdW50dWsgb3RvdCBkYW4ga2VueWFuZyBsZWJpaCBsYW1hLiBUYXJnZXQga2FzYXI6IDEgZ3JhbSBwZXIga2cgYmVyYXQgYmFkYW4gcGVyIGhhcmkuCgpTZXJhdCBkYXJpIHNheXVyLCBidWFoLCBkYW4ga2FjYW5nLWthY2FuZ2FuIG1lbGFuY2Fya2FuIHBlbmNlcm5hYW4gZGFuIG1lbnN0YWJpbGthbiBndWxhIGRhcmFoLgoKQmF0YXNpOiBtaW51bWFuIG1hbmlzIChzdW1iZXIgZ3VsYSB0ZXJiZXNhciB5YW5nIHRhayBkaXNhZGFyaSksIGdvcmVuZ2FuIGJlcmxlYmloYW4sIGRhbiBtYWthbmFuIHVsdHJhLXByb3Nlcy4KCkFpcjogc2VraXRhciAyIGxpdGVyIHBlciBoYXJpLCBsZWJpaCBqaWthIGJlcmtlcmluZ2F0LiBSYXNhIGhhdXMgc2VyaW5nIGRpc2FuZ2thIGxhcGFyLgoKVGlkYWsgcGVybHUgZGlldCBla3N0cmVtLiBQZXJ1YmFoYW4ga2VjaWwgeWFuZyBiZXJ0YWhhbiDigJQgbWlzLiBnYW50aSAxIGdlbGFzIHRlaCBtYW5pcyBkZW5nYW4gYWlyIHB1dGloIOKAlCBoYXNpbG55YSBsZWJpaCBiZXNhciBkYXJpIGRpZXQga2V0YXQgc2VtaW5nZ3UgbGFsdSBtZW55ZXJhaC4K',
    'gtd-dasar.md': 'IyBHVEQgRGFzYXIKCkdldHRpbmcgVGhpbmdzIERvbmUgKERhdmlkIEFsbGVuKTogc2lzdGVtIGFnYXIga2VwYWxhIGtvc29uZyBkYXJpICJqYW5nYW4gbHVwYSIuCgpMaW1hIGxhbmdrYWg6CgoxLiBDYXB0dXJlOiB0dWxpcyBTRU1VQSB5YW5nIG1lbmdnYW5nZ3UgcGlraXJhbiBrZSBpbmJveCAobm90ZXMgSFApLgoyLiBDbGFyaWZ5OiB1bnR1ayB0aWFwIGl0ZW0sIHRhbnlhICJpbmkgYmlzYSBkaXRpbmRha2xhbmp1dGk/IiBLYWxhdSB0aWRhayDihpIgYnVhbmcsIGFyc2lwLCBhdGF1IHNvbWVkYXkuCjMuIE9yZ2FuaXplOiB5YW5nIGJpc2EgPCAyIG1lbml0IOKGkiBrZXJqYWthbiBsYW5nc3VuZy4gU2lzYW55YSBtYXN1ayBkYWZ0YXI6IG5leHQgYWN0aW9uLCBtZW51bmdndSBvcmFuZyBsYWluLCBhdGF1IGthbGVuZGVyIChrYWxhdSBhZGEgZGVhZGxpbmUpLgo0LiBSZWZsZWN0OiByZXZpZXcgbWluZ2d1YW4g4oCUIGJlcnNpaGthbiBpbmJveCwgcGVyYmFydWkgZGFmdGFyLgo1LiBFbmdhZ2U6IGtlcmpha2FuIGJlcmRhc2Fya2FuIGtvbnRla3MsIGVuZXJnaSwgZGFuIHByaW9yaXRhcy4KCkF0dXJhbiAyIG1lbml0IHNhbmdhdCBwb3dlcmZ1bDoga2ViYW55YWthbiB0dWdhcyBrZWNpbCBtZW51bXB1ayBoYW55YSBrYXJlbmEgdGlkYWsgbGFuZ3N1bmcgZGlrZXJqYWthbi4KCkt1bmNpIEdURDogb3RhayB1bnR1ayBiZXJwaWtpciwgYnVrYW4gbWVueWltcGFuLiBTZW11YSBoYXJ1cyB0ZXJ0dWxpcyBkaSBzaXN0ZW0geWFuZyBkaXBlcmNheWEuCg==',
    'http-api.md': 'IyBIVFRQICYgQVBJCgpIVFRQIGFkYWxhaCBwcm90b2tvbCBrb211bmlrYXNpIHdlYi4gQ2xpZW50IChicm93c2VyL2FwbGlrYXNpKSBtZW5naXJpbSByZXF1ZXN0LCBzZXJ2ZXIgbWVuamF3YWIgZGVuZ2FuIHJlc3BvbnNlLgoKTWV0aG9kIHV0YW1hOgoKLSBgR0VUYCDigJQgYW1iaWwgZGF0YSAodGlkYWsgbWVuZ3ViYWggYXBhLWFwYSkKLSBgUE9TVGAg4oCUIGtpcmltL2J1YXQgZGF0YSBiYXJ1Ci0gYFBVVGAvYFBBVENIYCDigJQgdWJhaCBkYXRhCi0gYERFTEVURWAg4oCUIGhhcHVzIGRhdGEKClN0YXR1cyBjb2RlOgoKLSBgMnh4YCBzdWtzZXMgKDIwMCBPSywgMjAxIENyZWF0ZWQpCi0gYDN4eGAgcmVkaXJlY3QgKDMwMSwgMzA0KQotIGA0eHhgIHNhbGFoIGRpIGNsaWVudCAoNDAwIEJhZCBSZXF1ZXN0LCA0MDEgVW5hdXRob3JpemVkLCA0MDQgTm90IEZvdW5kKQotIGA1eHhgIHNhbGFoIGRpIHNlcnZlciAoNTAwIEludGVybmFsIFNlcnZlciBFcnJvcikKCkhlYWRlciBwZW50aW5nOiBgQ29udGVudC1UeXBlOiBhcHBsaWNhdGlvbi9qc29uYCwgYEF1dGhvcml6YXRpb246IEJlYXJlciA8dG9rZW4+YCwgYFgtQVBJLUtleWAuCgpSRVNUIEFQSSBtZW1ha2FpIFVSTCBzZXBlcnRpIGAvdXNlcnMvMTIzYCBkZW5nYW4gbWV0aG9kIEhUVFAgeWFuZyB0ZXBhdCwgZGFuIGJlcnR1a2FyIGRhdGEgSlNPTjoKCmBgYGpzb24KeyAibmFtYSI6ICJBZGlwIiwgInVtdXIiOiAyMCB9CmBgYAoKT3RlbnRpa2FzaSB1bXVtOiBBUEkga2V5IGRpIGhlYWRlciwgQmVhcmVyIHRva2VuLCBhdGF1IE9BdXRoLgoKRGkgUHl0aG9uLCBgdXJsbGliLnJlcXVlc3RgIGJhd2FhbiBzdGRsaWIgY3VrdXAgdW50dWsgcmVxdWVzdCBzZWRlcmhhbmEgdGFucGEgaW5zdGFsbCBhcGEgcHVuLgo=',
    'investasi-dasar.md': 'IyBJbnZlc3Rhc2kgRGFzYXIKCkludmVzdGFzaSA9IG1lbmFydWggdWFuZyBhZ2FyIGJlcnR1bWJ1aCBtZW5nYWxhaGthbiBpbmZsYXNpLiBQcmluc2lwIGludGk6IHJldHVybiB0aW5nZ2kgPSByaXNpa28gdGluZ2dpLiBUaWRhayBhZGEgeWFuZyBwYXN0aSB1bnR1bmcuCgpNdWxhaSBkYXJpIHR1anVhbiBkYW4gamFuZ2thIHdha3R1OgoKLSA8IDEgdGFodW46IGphbmdhbiBpbnZlc3Rhc2ksIHRhcnVoIGRpIHRhYnVuZ2FuL2RlcG9zaXRvLgotIDEtNSB0YWh1bjogcmVrc2FkYW5hIGNhbXB1cmFuL3BlbmRhcGF0YW4gdGV0YXAsIG9ibGlnYXNpLgotID4gNSB0YWh1bjogcmVrc2FkYW5hIHNhaGFtL0VURiwgc2FoYW0uCgpEaXZlcnNpZmlrYXNpOiBqYW5nYW4gdGFydWggc2VtdWEgZGkgc2F0dSBpbnN0cnVtZW4uIFBlcGF0YWhueWEgImRvbid0IHB1dCBhbGwgZWdncyBpbiBvbmUgYmFza2V0Ii4KClVudHVrIHBlbXVsYSBJbmRvbmVzaWE6IHJla3NhZGFuYSBwYXNhciB1YW5nIChyaXNpa28gcmVuZGFoLCBsaWt1aWQpLCBsYWx1IHJla3NhZGFuYSBpbmRla3MvRVRGIChiaWF5YSByZW5kYWgsIGlrdXQgcGFzYXIpLiBCZWxpIHJ1dGluIHRpYXAgYnVsYW4gKGRvbGxhciBjb3N0IGF2ZXJhZ2luZykgbWVuZ2FsYWhrYW4gY29iYS1jb2JhIHRpbWluZyBwYXNhci4KCllhbmcgZGloaW5kYXJpOiB0aXRpcCBkYW5hIGtlIG9yYW5nIHRhayBkaWtlbmFsLCBpbWluZy1pbWluZyByZXR1cm4gdGV0YXAgdGluZ2dpIHBlciBidWxhbiAoY2lyaSBza2VtYSBwb256aSksIGRhbiBpbnZlc3Rhc2kgcGFrYWkgdXRhbmcgYXRhdSBkYW5hIGRhcnVyYXQuCgpVcnV0YW5ueWE6IGRhbmEgZGFydXJhdCBkdWx1LCBiYXJ1IGludmVzdGFzaS4K',
    'javascript-dasar.md': 'IyBKYXZhU2NyaXB0IERhc2FyCgpKYXZhU2NyaXB0IGFkYWxhaCBiYWhhc2EgcGVtcm9ncmFtYW4gdW50dWsgd2ViLiBCZXJqYWxhbiBkaSBicm93c2VyIGRhbiBkaSBzZXJ2ZXIgdmlhIE5vZGUuanMuCgpWYXJpYWJlbDogZ3VuYWthbiBgY29uc3RgIHVudHVrIG5pbGFpIHRldGFwIGRhbiBgbGV0YCB1bnR1ayB5YW5nIGJlcnViYWguIEhpbmRhcmkgYHZhcmAuCgpgYGBqcwpjb25zdCBuYW1hID0gIkFkaXAiOwpsZXQgdW11ciA9IDIwOwp1bXVyID0gMjE7CmBgYAoKVGlwZSBkYXRhOiBzdHJpbmcsIG51bWJlciwgYm9vbGVhbiwgYXJyYXksIG9iamVjdCwgbnVsbCwgdW5kZWZpbmVkLgoKRnVuZ3NpOgoKYGBganMKZnVuY3Rpb24gc2FwYShuYW1hKSB7CiAgcmV0dXJuICJIYWxvLCAiICsgbmFtYTsKfQpjb25zdCBzYXBhMiA9IChuYW1hKSA9PiBgSGFsbywgJHtuYW1hfWA7CmBgYAoKQXJyYXkgcHVueWEgbWV0aG9kIHByYWt0aXM6IGBtYXBgLCBgZmlsdGVyYCwgYGZpbmRgLCBgZm9yRWFjaGAuCgpgYGBqcwpjb25zdCBhbmdrYSA9IFsxLCAyLCAzLCA0XTsKY29uc3QgZ2VuYXAgPSBhbmdrYS5maWx0ZXIoeCA9PiB4ICUgMiA9PT0gMCk7CmNvbnN0IGthbGlEdWEgPSBhbmdrYS5tYXAoeCA9PiB4ICogMik7CmBgYAoKRE9NOiBgZG9jdW1lbnQucXVlcnlTZWxlY3RvcigiI2lkIilgIG1lbWlsaWggZWxlbWVuLCBgYWRkRXZlbnRMaXN0ZW5lcigiY2xpY2siLCAuLi4pYCBtZW5hbmdhbmkga2xpay4KCkZldGNoIEFQSSB1bnR1ayBIVFRQIHJlcXVlc3Q6CgpgYGBqcwpmZXRjaCgiaHR0cHM6Ly9hcGkuY29udG9oLmNvbS9kYXRhIikKICAudGhlbihyID0+IHIuanNvbigpKQogIC50aGVuKGRhdGEgPT4gY29uc29sZS5sb2coZGF0YSkpOwpgYGAKCkFzeW5jL2F3YWl0IG1lbWJ1YXQga29kZSBhc2lua3JvbiBsZWJpaCByYXBpOgoKYGBganMKYXN5bmMgZnVuY3Rpb24gYW1iaWwoKSB7CiAgY29uc3QgciA9IGF3YWl0IGZldGNoKCJodHRwczovL2FwaS5jb250b2guY29tL2RhdGEiKTsKICByZXR1cm4gYXdhaXQgci5qc29uKCk7Cn0KYGBgCgpQZXJiYW5kaW5nYW46IGA9PT1gIG1lbWJhbmRpbmdrYW4gbmlsYWkgZGFuIHRpcGUgKHN0cmljdCksIHNlZGFuZ2thbiBgPT1gIG1lbGFrdWthbiBrb252ZXJzaSB0aXBlIGR1bHUuIFNlbGFsdSBwYWthaSBgPT09YC4K',
    'keamanan-digital.md': 'IyBLZWFtYW5hbiBEaWdpdGFsCgpEYXNhci1kYXNhciBtZW5qYWdhIGFrdW4gZGFuIGRhdGE6CgpQYXNzd29yZDogcGFrYWkgcGFzc3dvcmQgbWFuYWdlciAobWlzLiBCaXR3YXJkZW4geWFuZyBncmF0aXMpIGFnYXIgdGlhcCBzaXR1cyBwdW55YSBwYXNzd29yZCB1bmlrIGRhbiBwYW5qYW5nLiBKYW5nYW4gcGFrYWkgdWxhbmcgcGFzc3dvcmQgeWFuZyBzYW1hLgoKMkZBOiBha3RpZmthbiBhdXRlbnRpa2FzaSBkdWEgZmFrdG9yIGRpIGVtYWlsLCBiYW5rLCBkYW4gbWVkaWEgc29zaWFsLiBBcGxpa2FzaSBhdXRoZW50aWNhdG9yIGxlYmloIGFtYW4gZGFyaSBTTVMuCgpQaGlzaGluZzogd2FzcGFkYSBsaW5rIGRhbiBsYW1waXJhbiBkYXJpIHBlbmdpcmltIHRhayBkaWtlbmFsLCB3YWxhdSBtZW5nYXRhc25hbWFrYW4gYmFuayBhdGF1IGluc3RhbnNpLiBDZWsgYWxhbWF0IHBlbmdpcmltIGFzbGksIGphbmdhbiBrbGlrIHRlcmJ1cnUtYnVydS4gQmFuayB0aWRhayBwZXJuYWggbWludGEgcGFzc3dvcmQgdmlhIFdoYXRzQXBwLgoKVXBkYXRlOiBwYXNhbmcgdXBkYXRlIHNpc3RlbSBkYW4gYXBsaWthc2kg4oCUIGtlYmFueWFrYW4gYmVyaXNpIHRhbWJhbGFuIGtlYW1hbmFuLgoKQmFja3VwOiBzYWxpbiBkYXRhIHBlbnRpbmcga2UgMiB0ZW1wYXQgKG1pcy4gY2xvdWQgKyBoYXJkZGlzaykuIFByaW5zaXAgMy0yLTE6IDMgc2FsaW5hbiwgMiBtZWRpYSBiZXJiZWRhLCAxIGRpIGxva2FzaSBiZXJiZWRhLgoKSXppbiBhcGxpa2FzaTogY2FidXQgYWtzZXMgbG9rYXNpL2tvbnRhayB5YW5nIHRpZGFrIHBlcmx1LiBEaSBIUCwgY2VrIGJlcmthbGEgYXBsaWthc2kgeWFuZyBqYXJhbmcgZGlwYWthaS4K',
    'nasi-goreng.md': 'IyBOYXNpIEdvcmVuZwoKQmFoYW46IDIgcGlyaW5nIG5hc2kgZGluZ2luIChuYXNpIGtlbWFyaW4gbGViaWggYmFndXMsIHRpZGFrIGxlbWJlayksIDIgdGVsdXIsIGF5YW0vc29zaXMgc2VjdWt1cG55YSwga2VjYXAgbWFuaXMgMiBzZG0sIGtlY2FwIGFzaW4gMSBzZHQsIGdhcmFtLCBtZXJpY2EsIG1pbnlhay4KCkJ1bWJ1IGhhbHVzOiA0IGJhd2FuZyBtZXJhaCwgMiBiYXdhbmcgcHV0aWgsIDMgY2FiYWkgbWVyYWggKHNlc3VhaSBzZWxlcmEpLCAxIHNkdCB0ZXJhc2kgYmFrYXIuCgpDYXJhOgoKMS4gVHVtaXMgYnVtYnUgaGFsdXMgc2FtcGFpIGhhcnVtIGRhbiBtYXRhbmcuCjIuIE1hc3Vra2FuIGF5YW0vc29zaXMsIGFkdWsgc2FtcGFpIGJlcnViYWggd2FybmEuCjMuIFBpbmdnaXJrYW4sIG9yYWstYXJpayB0ZWx1ciBkaSBzaXNpIHdhamFuLgo0LiBNYXN1a2thbiBuYXNpLCBhZHVrIHRla2FuLXRla2FuIGFnYXIgdGlkYWsgbWVuZ2d1bXBhbC4KNS4gVGFtYmFoIGtlY2FwIG1hbmlzLCBrZWNhcCBhc2luLCBnYXJhbSwgbWVyaWNhLiBBZHVrIHNhbXBhaSByYXRhIGRhbiBzZWRpa2l0IGJlcmFzYXAuCjYuIFNhamlrYW4gZGVuZ2FuIGtlcnVwdWssIGFjYXIsIGRhbiBpcmlzYW4gdGltdW4uCgpUaXBzOiBhcGkgYmVzYXIgZGFuIHdhamFuIHBhbmFzIG1lbWJlcmkgYXJvbWEgc21va3kga2hhcy4gSmFuZ2FuIHBha2FpIG5hc2kgYmFydSB5YW5nIGxlbWJlayDigJQgaGFzaWxueWEgamFkaSBidWJ1ciBnb3JlbmcuCg==',
    'olahraga-pemula.md': 'IyBPbGFocmFnYSB1bnR1ayBQZW11bGEKCkF0dXJhbiBub21vciBzYXR1OiBrb25zaXN0ZW5zaSBtZW5nYWxhaGthbiBpbnRlbnNpdGFzLiAyMCBtZW5pdCB0aWFwIGhhcmkgbGViaWggYmFpayBkYXJpIDIgamFtIHNlbWluZ2d1IHNla2FsaS4KCk11bGFpIGRhcmkgeWFuZyBwYWxpbmcgbXVkYWg6IGphbGFuIGtha2kgMjAtMzAgbWVuaXQuIFNldGVsYWggMiBtaW5nZ3UgbnlhbWFuLCB0YW1iYWggZHVyYXNpIGF0YXUgc2VsaW5naSBqb2dnaW5nIHJpbmdhbiAoaW50ZXJ2YWw6IDEgbWVuaXQgbGFyaSwgMiBtZW5pdCBqYWxhbiwgdWxhbmcpLgoKTGF0aWhhbiBrZWt1YXRhbiAyeCBzZW1pbmdndTogc3F1YXQsIHB1c2gtdXAgKGJpc2EgbXVsYWkgZGFyaSBsdXR1dCksIHBsYW5rLiBDdWt1cCBkZW5nYW4gYmVyYXQgYmFkYW4gZHVsdS4KClByb2dyZXNpOiBuYWlra2FuIGJlYmFuL2R1cmFzaSBtYWtzaW1hbCAxMCUgcGVyIG1pbmdndSB1bnR1ayBoaW5kYXJpIGNlZGVyYS4KClBlbWFuYXNhbiA1IG1lbml0ICsgcGVuZGluZ2luYW4gZGFuIHN0cmV0Y2hpbmcgc2V0ZWxhaG55YS4KCklzdGlyYWhhdCBpdHUgYmFnaWFuIGRhcmkgcHJvZ3JhbTogb3RvdCB0dW1idWggc2FhdCByZWNvdmVyeS4gVGlkdXIgY3VrdXAgZGFuIGphbmdhbiBsYXRpaCBvdG90IHlhbmcgc2FtYSAyIGhhcmkgYmVydHVydXQtdHVydXQuCgpQaWxpaCB5YW5nIGthbXUgbmlrbWF0aSDigJQgeWFuZyBiZXJ0YWhhbiBhZGFsYWggeWFuZyB0aWRhayB0ZXJhc2Egc2VwZXJ0aSBodWt1bWFuLgo=',
    'pengantar-ai.md': 'IyBQZW5nYW50YXIgQUkKCkFJIChrZWNlcmRhc2FuIGJ1YXRhbikgYWRhbGFoIGJpZGFuZyBpbG11IHlhbmcgbWVtYnVhdCBtZXNpbiBtZWxha3VrYW4gdHVnYXMgeWFuZyBidXR1aCBrZWNlcmRhc2FuIG1hbnVzaWEuCgpNYWNoaW5lIGxlYXJuaW5nIGFkYWxhaCBjYWJhbmcgQUk6IGFsaWgtYWxpaCBkaXByb2dyYW0gYXR1cmFuIG1hbnVhbCwgbW9kZWwgQkVMQUpBUiBwb2xhIGRhcmkgZGF0YS4gQ29udG9oOiBkaWJlcmkgcmlidWFuIGZvdG8ga3VjaW5nIGRhbiBhbmppbmcgYmVybGFiZWwsIG1vZGVsIGJlbGFqYXIgbWVtYmVkYWthbm55YSBzZW5kaXJpLgoKSmVuaXMgdXRhbWE6CgotIFN1cGVydmlzZWQgbGVhcm5pbmc6IGJlbGFqYXIgZGFyaSBkYXRhIGJlcmxhYmVsIChrbGFzaWZpa2FzaSwgcHJlZGlrc2kgaGFyZ2EpLgotIFVuc3VwZXJ2aXNlZCBsZWFybmluZzogbWVuY2FyaSBwb2xhIHRhbnBhIGxhYmVsIChjbHVzdGVyaW5nLCBzZWdtZW50YXNpIHBlbGFuZ2dhbikuCi0gUmVpbmZvcmNlbWVudCBsZWFybmluZzogYmVsYWphciBkYXJpIHRyaWFsLWVycm9yIGRhbiByZXdhcmQgKEFJIG1haW4gZ2FtZSkuCgpEZWVwIGxlYXJuaW5nIG1lbWFrYWkgbmV1cmFsIG5ldHdvcmsgYmVybGFwaXMtbGFwaXMg4oCUIHNhbmdhdCBrdWF0IHVudHVrIGdhbWJhciwgc3VhcmEsIGRhbiBiYWhhc2EuIExMTSAobGFyZ2UgbGFuZ3VhZ2UgbW9kZWwpIHNlcGVydGkgeWFuZyBtZW5qYXdhYiBwZXJ0YW55YWFubXUgYWRhbGFoIGRlZXAgbGVhcm5pbmcgeWFuZyBkaWxhdGloIGRpIHRla3MgcmFrc2FzYS4KCktldGVyYmF0YXNhbjogQUkgdGlkYWsgInBhaGFtIiBzZXBlcnRpIG1hbnVzaWEg4oCUIGlhIG1lbmdlbmFsaSBwb2xhIHN0YXRpc3Rpay4gQmlzYSBzYWxhaCBkZW5nYW4gcGVyY2F5YSBkaXJpIChoYWx1c2luYXNpKSwgYmlhcyBkYXJpIGRhdGEgbGF0aWgsIGRhbiBidXR1aCB2ZXJpZmlrYXNpIHVudHVrIGhhbCBwZW50aW5nLgo=',
    'regex-praktis.md': 'IyBSZWdleCBQcmFrdGlzCgpSZWd1bGFyIGV4cHJlc3Npb24gKHJlZ2V4KSBhZGFsYWggcG9sYSB1bnR1ayBtZW5jYXJpIHRla3MuCgpTaW1ib2wgZGFzYXI6CgotIGAuYCBrYXJha3RlciBhcGEgc2FqYQotIGAqYCBub2wgYXRhdSBsZWJpaCwgYCtgIHNhdHUgYXRhdSBsZWJpaCwgYD9gIG5vbCBhdGF1IHNhdHUKLSBgXmAgYXdhbCBzdHJpbmcsIGAkYCBha2hpciBzdHJpbmcKLSBgW2FiY11gIHNhbGFoIHNhdHUgZGFyaSBhL2IvYywgYFswLTldYCBkaWdpdAotIGBcZGAgZGlnaXQsIGBcd2AgaHVydWYvYW5na2EvdW5kZXJzY29yZSwgYFxzYCBzcGFzaQotIGAoKWAgZ3J1cCwgYHxgIGF0YXUKCkNvbnRvaCBwcmFrdGlzOgoKRW1haWwgc2VkZXJoYW5hOiBgW1x3Li1dK0BbXHctXStcLlx3K2AKClRhbmdnYWwgREQtTU0tWVlZWTogYFxkezJ9LVxkezJ9LVxkezR9YAoKTm9tb3IgSFAgSW5kb25lc2lhOiBgMDhcZHs5LDExfWAKCkh1cnVmIGthcGl0YWwgdGlhcCBrYXRhIGJpc2EgZGljZWsgZGVuZ2FuIGBeW0EtWl1bYS16XSsoIFtBLVpdW2Etel0rKSokYC4KCkRpIFB5dGhvbjoKCmBgYHB5dGhvbgppbXBvcnQgcmUKcmUuZmluZGFsbChyIlxkKyIsICJ1bXVyIDIwIGRhbiAyNSIpICAjIFsnMjAnLCAnMjUnXQpyZS5zdWIociJccysiLCAiICIsICJhICAgYiIpICAgICAgICAgICMgJ2EgYicKYGBgCgpUaXBzOiByZWdleCBpdHUgZ3JlZWR5IHNlY2FyYSBkZWZhdWx0IOKAlCBgLipgIG1lbmdhbWJpbCBzZXBhbmphbmcgbXVuZ2tpbi4gVGFtYmFoa2FuIGA/YCB1bnR1ayBub24tZ3JlZWR5OiBgLio/YC4KClVqaSBwb2xhbXUgZGkgcmVnZXgxMDEuY29tIHNlYmVsdW0gZGlwYWthaSBkaSBrb2RlLgo=',
    'rencana-liburan-jepang.md': 'IyBSZW5jYW5hIExpYnVyYW4ga2UgSmVwYW5nCgpJdGluZXJhcnkgNyBoYXJpOiBUb2t5byAoMyBoYXJpKSwgS3lvdG8gKDIgaGFyaSksIE9zYWthICgyIGhhcmkpLgpCdWRnZXQgZXN0aW1hc2k6IHRpa2V0IHBlc2F3YXQgOCBqdXRhLCBob3RlbCA2IGp1dGEsIG1ha2FuIGRhbiB0cmFuc3BvcnQgNSBqdXRhLgoKRGkgVG9reW8gd2FqaWIga2U6IEFzYWt1c2EsIFNoaWJ1eWEgY3Jvc3NpbmcsIEFraWhhYmFyYSwgZGFuIHRlYW1MYWIgUGxhbmV0cy4KRGkgS3lvdG86IEZ1c2hpbWkgSW5hcmksIEFyYXNoaXlhbWEgYmFtYm9vIGdyb3ZlLCBkYW4gR2lvbi4KRGkgT3Nha2E6IERvdG9uYm9yaSwgT3Nha2EgQ2FzdGxlLCBkYW4gZGF5IHRyaXAga2UgTmFyYSB1bnR1ayBtZWxpaGF0IHJ1c2EuCgpUaXBzOiBiZWxpIEpSIFBhc3Mgc2ViZWx1bSBiZXJhbmdrYXQsIGJhd2EgY2FzaCBzZWN1a3VwbnlhIGthcmVuYSBiYW55YWsKdGVtcGF0IGtlY2lsIGhhbnlhIHRlcmltYSB0dW5haSwgZGFuIGRvd25sb2FkIGFwbGlrYXNpIHBldGEgb2ZmbGluZS4KTXVzaW0gdGVyYmFpazogc2FrdXJhIChha2hpciBNYXJldCkgYXRhdSBtb21pamkgKE5vdmVtYmVyKS4K',
    'resep-rendang.md': 'IyBSZXNlcCBSZW5kYW5nIFNhcGkKCkJhaGFuIHV0YW1hOiAxIGtnIGRhZ2luZyBzYXBpLCBzYW50YW4gZGFyaSAzIGJ1dGlyIGtlbGFwYSwgZGFuIGJ1bWJ1IGhhbHVzLgpCdW1idSBoYWx1cyB0ZXJkaXJpIGRhcmkgY2FiYWkgbWVyYWgsIGJhd2FuZyBtZXJhaCwgYmF3YW5nIHB1dGloLCBqYWhlLApsZW5na3Vhcywga3VueWl0LCBkYW4ga2VtaXJpLgoKQ2FyYSBtZW1hc2FrOgoxLiBUdW1pcyBidW1idSBoYWx1cyBzYW1wYWkgaGFydW0gZGFuIG1hdGFuZy4KMi4gTWFzdWtrYW4gZGFnaW5nLCBhZHVrIHNhbXBhaSBiZXJ1YmFoIHdhcm5hLgozLiBUdWFuZyBzYW50YW4sIG1hc2FrIGRlbmdhbiBhcGkga2VjaWwgc2FtYmlsIHNlc2VrYWxpIGRpYWR1ay4KNC4gTWFzYWsgMy00IGphbSBzYW1wYWkgc2FudGFuIG1lbnl1c3V0IGRhbiBiZXJtaW55YWsuCgpLdW5jaSByZW5kYW5nIGVuYWs6IGFwaSBrZWNpbCwgc2FiYXIsIGRhbiBzYW50YW4ga2VudGFsIHlhbmcgYmVya3VhbGl0YXMuCkphbmdhbiBkaWFkdWsgdGVybGFsdSBzZXJpbmcgc3VwYXlhIGRhZ2luZyB0aWRhayBoYW5jdXIuCg==',
    'sambal.md': 'IyBBbmVrYSBTYW1iYWwKClNhbWJhbCB0ZXJhc2k6IDEwIGNhYmFpIG1lcmFoLCA1IGNhYmFpIHJhd2l0LCA0IGJhd2FuZyBtZXJhaCwgMiBiYXdhbmcgcHV0aWgsIDEgc2R0IHRlcmFzaSBiYWthciwgZ2FyYW0sIGd1bGEgbWVyYWguIEdvcmVuZyBzZW11YSBiYWhhbiwgdWxlayBrYXNhci4KClNhbWJhbCBtYXRhaCAoQmFsaSk6IDggY2FiYWkgcmF3aXQgaXJpcyB0aXBpcywgNSBiYXdhbmcgbWVyYWggaXJpcywgMSBiYXRhbmcgc2VyYWkgaXJpcyBoYWx1cywgMiBsZW1iYXIgZGF1biBqZXJ1ayBpcmlzLCBnYXJhbSwgcGVyYXNhbiBqZXJ1ayBsaW1hdSwgMyBzZG0gbWlueWFrIGtlbGFwYSBwYW5hcy4gQ2FtcHVyIG1lbnRhaCwgc2lyYW0gbWlueWFrIHBhbmFzLgoKU2FtYmFsIGJhd2FuZzogMTUgY2FiYWkgcmF3aXQgKyA0IGJhd2FuZyBwdXRpaCBkaWdvcmVuZyBzYW1wYWkgbGF5dSwgdWxlayBkZW5nYW4gZ2FyYW0uIFNpcmFtIG1pbnlhayBwYW5hcyBiZWthcyBtZW5nZ29yZW5nLgoKU2FtYmFsIGlqbyAoUGFkYW5nKTogMTAgY2FiYWkgaGlqYXUgYmVzYXIsIDUgY2FiYWkgcmF3aXQgaGlqYXUsIDQgYmF3YW5nIG1lcmFoLCAyIHRvbWF0IGhpamF1LiBSZWJ1cyBzZWJlbnRhciwgdWxlayBrYXNhciwgdHVtaXMgZGVuZ2FuIG1pbnlhayBzYW1wYWkgbWF0YW5nLgoKUHJpbnNpcCB1bXVtOiBiYWhhbiBzZWdhciwgamFuZ2FuIHVsZWsgdGVybGFsdSBoYWx1cyAodGVrc3R1ciBrYXNhciBsZWJpaCBuaWttYXQpLCBkYW4gc2VpbWJhbmdrYW4gYXNpbi1tYW5pcy1hc2FtLiBTYW1iYWwgdGFoYW4gMy01IGhhcmkgZGkga3Vsa2FzIGRhbGFtIHdhZGFoIHRlcnR1dHVwIGRlbmdhbiBsYXBpc2FuIG1pbnlhayBkaSBhdGFzbnlhLgo=',
    'soto-ayam.md': 'IyBTb3RvIEF5YW0KCkJhaGFuOiA1MDAgZ3IgYXlhbSAoZGFkYS9wYWhhKSwgMiBsaXRlciBhaXIsIDIgYmF0YW5nIHNlcmFpLCAzIGxlbWJhciBkYXVuIGplcnVrLCAyIGNtIGxlbmdrdWFzLCAyIGNtIGt1bnlpdCBiYWthciwgZ2FyYW0sIGd1bGEsIG1lcmljYS4KCkJ1bWJ1IGhhbHVzOiA2IGJhd2FuZyBtZXJhaCwgNCBiYXdhbmcgcHV0aWgsIDMga2VtaXJpIHNhbmdyYWksIDEgc2R0IGtldHVtYmFyLCAxLzIgc2R0IGppbnRlbi4KCkNhcmE6CgoxLiBSZWJ1cyBheWFtIHNhbXBhaSBlbXB1aywgYW5na2F0LCBzdXdpci1zdXdpci4gU2ltcGFuIGthbGR1bnlhLgoyLiBUdW1pcyBidW1idSBoYWx1cyArIHNlcmFpICsgZGF1biBqZXJ1ayArIGxlbmdrdWFzIHNhbXBhaSBoYXJ1bS4KMy4gTWFzdWtrYW4gdHVtaXNhbiBrZSBrYWxkdSwgZGlkaWhrYW4gMTUgbWVuaXQuIEJ1bWJ1aSBnYXJhbSwgZ3VsYSwgbWVyaWNhLgo0LiBTYWppa2FuOiBzb3VuLCB0YXVnZSwga29sLCB0ZWx1ciByZWJ1cywgc3V3aXJhbiBheWFtLCBzaXJhbSBrdWFoIHBhbmFzLgo1LiBUYWJ1cmkgYmF3YW5nIGdvcmVuZywgc2VsZWRyaSwgZGFuIHBlcmFzYW4gamVydWsgbmlwaXMuIFNhbWJhbCB0ZXJwaXNhaC4KClRpcHM6IGt1bnlpdCB5YW5nIGRpYmFrYXIgZHVsdSBtZW1iZXJpIHdhcm5hIGt1bmluZyBjYW50aWsgZGFuIGFyb21hIGxlYmloIGRhbGFtLiBLYWxkdSBqYW5nYW4gZGlkaWRpaGthbiB0ZXJsYWx1IGxhbWEgc2V0ZWxhaCBidW1idSBtYXN1ayBhZ2FyIHRldGFwIGJlbmluZy4K',
    'sql-dasar.md': 'IyBTUUwgRGFzYXIKClNRTCBhZGFsYWggYmFoYXNhIHVudHVrIG1lbmdlbG9sYSBkYXRhYmFzZSByZWxhc2lvbmFsLgoKQW1iaWwgZGF0YToKCmBgYHNxbApTRUxFQ1QgbmFtYSwgdW11ciBGUk9NIHBlbmdndW5hOwpTRUxFQ1QgKiBGUk9NIHBlbmdndW5hIFdIRVJFIHVtdXIgPj0gMTg7ClNFTEVDVCAqIEZST00gcGVuZ2d1bmEgT1JERVIgQlkgbmFtYSBBU0MgTElNSVQgMTA7CmBgYAoKRmlsdGVyOiBgV0hFUkVgIGRlbmdhbiBgPWAsIGA+YCwgYDxgLCBgTElLRWAsIGBJTmAsIGBCRVRXRUVOYCwgYEFORGAsIGBPUmAsIGBOT1RgLgoKYGBgc3FsClNFTEVDVCAqIEZST00gcHJvZHVrIFdIRVJFIGhhcmdhIEJFVFdFRU4gMTAwMDAgQU5EIDUwMDAwOwpTRUxFQ1QgKiBGUk9NIHBlbmdndW5hIFdIRVJFIG5hbWEgTElLRSAnQW5kaSUnOwpgYGAKClRhbWJhaCwgdWJhaCwgaGFwdXM6CgpgYGBzcWwKSU5TRVJUIElOVE8gcGVuZ2d1bmEgKG5hbWEsIHVtdXIpIFZBTFVFUyAoJ0J1ZGknLCAyNSk7ClVQREFURSBwZW5nZ3VuYSBTRVQgdW11ciA9IDI2IFdIRVJFIG5hbWEgPSAnQnVkaSc7CkRFTEVURSBGUk9NIHBlbmdndW5hIFdIRVJFIHVtdXIgPCAxNzsKYGBgCgpIYXRpLWhhdGk6IGBVUERBVEVgIGRhbiBgREVMRVRFYCB0YW5wYSBgV0hFUkVgIG1lbmd1YmFoL21lbmdoYXB1cyBTRU1VQSBiYXJpcy4KCkdhYnVuZyB0YWJlbCAoSk9JTik6CgpgYGBzcWwKU0VMRUNUIHAubmFtYSwgby50YW5nZ2FsCkZST00gcGVuZ2d1bmEgcApJTk5FUiBKT0lOIHBlc2FuYW4gbyBPTiBvLnVzZXJfaWQgPSBwLmlkOwpgYGAKCmBJTk5FUiBKT0lOYCBoYW55YSBiYXJpcyB5YW5nIGNvY29rIGRpIGtlZHVhIHRhYmVsLCBgTEVGVCBKT0lOYCBtZW55ZXJ0YWthbiBzZW11YSBiYXJpcyB0YWJlbCBraXJpLgoKQWdyZWdhdCBkYW4gZ3J1cDoKCmBgYHNxbApTRUxFQ1Qga2F0ZWdvcmksIENPVU5UKCopLCBBVkcoaGFyZ2EpCkZST00gcHJvZHVrCkdST1VQIEJZIGthdGVnb3JpCkhBVklORyBDT1VOVCgqKSA+IDU7CmBgYAoKRnVuZ3NpIGFncmVnYXQ6IGBDT1VOVGAsIGBTVU1gLCBgQVZHYCwgYE1JTmAsIGBNQVhgLiBgV0hFUkVgIG1lbWZpbHRlciBzZWJlbHVtIGdydXAsIGBIQVZJTkdgIHNlc3VkYWggZ3J1cC4K',
    'teknik-pomodoro.md': 'IyBUZWtuaWsgUG9tb2Rvcm8KCk1ldG9kZSBmb2t1czogMjUgbWVuaXQga2VyamEgcGVudWgsIDUgbWVuaXQgaXN0aXJhaGF0LiBTYXR1IHNpa2x1cyA9IDEgcG9tb2Rvcm8uIFNldGVsYWggNCBwb21vZG9ybywgaXN0aXJhaGF0IHBhbmphbmcgMTUtMzAgbWVuaXQuCgpMYW5na2FoOgoKMS4gUGlsaWggMSB0dWdhcyBzcGVzaWZpay4KMi4gU2luZ2tpcmthbiBkaXN0cmFrc2kgKEhQIHNpbGVudCwgdHV0dXAgdGFiIHRhayBwZXJsdSkuCjMuIFNldCB0aW1lciAyNSBtZW5pdCwga2VyamFrYW4gc2FtcGFpIGJ1bnlpLgo0LiBJc3RpcmFoYXQgNSBtZW5pdCDigJQgYmVyZGlyaSwgbWludW0sIGphdWggZGFyaSBsYXlhci4KNS4gVGFuZGFpIDEgcG9tb2Rvcm8gc2VsZXNhaSwgdWxhbmdpLgoKQXR1cmFuOiBrYWxhdSBhZGEgaW50ZXJ1cHNpLCBjYXRhdCBjZXBhdCBsYWx1IGtlbWJhbGkg4oCUIGphbmdhbiBtdWx0aXRhc2tpbmcuIEthbGF1IHR1Z2FzIHNlbGVzYWkgc2ViZWx1bSAyNSBtZW5pdCwgcGFrYWkgc2lzYSB3YWt0dSB1bnR1ayByZXZpZXcuCgpNb2RpZmlrYXNpOiB1bnR1ayB0dWdhcyBiZXJhdCBiaXNhIDUwLTEwLiBJbnRpbnlhIGJsb2sgZm9rdXMgKyBqZWRhIHRlcmphZHdhbCwgYnVrYW4gZHVyYXNpbnlhIHlhbmcgc2FrcmFsLgoKQ29jb2sgdW50dWsgYmVsYWphciwgbmdvZGluZywgZGFuIG1lbnVsaXMuCg==',
    'tidur-berkualitas.md': 'IyBUaWR1ciBCZXJrdWFsaXRhcwoKRGV3YXNhIGJ1dHVoIDctOSBqYW0gdGlkdXIgcGVyIG1hbGFtLiBLdXJhbmcgdGlkdXIgbWVudXJ1bmthbiBmb2t1cywgaW11biwgZGFuIG1vb2QuCgpTbGVlcCBoeWdpZW5lOgoKLSBKYW0gdGlkdXIgZGFuIGJhbmd1biBrb25zaXN0ZW4sIHRlcm1hc3VrIGFraGlyIHBla2FuLgotIEthbWFyIGdlbGFwLCBzZWp1aywgZGFuIHNlcGkuCi0gU3RvcCBsYXlhciAzMC02MCBtZW5pdCBzZWJlbHVtIHRpZHVyIChjYWhheWEgYmlydSBtZW5la2FuIG1lbGF0b25pbikuCi0gSGluZGFyaSBrYWZlaW4gc2V0ZWxhaCBqYW0gMiBzaWFuZyDigJQgcGFydWggd2FrdHVueWEgNS02IGphbS4KLSBIaW5kYXJpIG1ha2FuIGJlcmF0IGRhbiBvbGFocmFnYSBpbnRlbnMgMiBqYW0gc2ViZWx1bSB0aWR1ci4KClJpdHVhbDogbWFuZGkgYWlyIGhhbmdhdCwgYmFjYSBidWt1IGZpc2lrLCBhdGF1IHBlcmVnYW5nYW4gcmluZ2FuIG1lbWJlcmkgc2lueWFsICJ3YWt0dW55YSB0aWR1ciIga2UgdHVidWguCgpLYWxhdSB0aWRhayBiaXNhIHRpZHVyIHNldGVsYWggMjAgbWVuaXQsIGJhbmd1biBkYW4gbGFrdWthbiBoYWwgbWVtYm9zYW5rYW4gZGkgdGVtcGF0IHJlZHVwLCBqYW5nYW4gYmVyZ3VsaW5nIHNhbWJpbCBtYWluIEhQLgoKS29uc2lzdGVuc2kgbWVuZ2FsYWhrYW4gZHVyYXNpIHNlc2VrYWxpOiB0aWR1ciA3IGphbSB0aWFwIGhhcmkgbGViaWggYmFpayBkYXJpIGJlZ2FkYW5nIGxhbHUgImJhbGFzIGRlbmRhbSIgZGkgd2Vla2VuZC4K',
    'tips-packing.md': 'IyBUaXBzIFBhY2tpbmcKClJ1bXVzIDUtNC0zLTItMSB1bnR1ayBzZW1pbmdndTogNSBhdGFzYW4sIDQgYmF3YWhhbiwgMyBwYXNhbmcgc2VwYXR1IChwYWthaSAxKSwgMiBqYWtldCwgMSB0b3BpLiBTZXN1YWlrYW4gaWtsaW0uCgpLYXRlZ29yaSB3YWppYjoKCi0gRG9rdW1lbjogS1RQLCB0aWtldCwgYm9va2luZyBob3RlbCAoc2NyZWVuc2hvdCBvZmZsaW5lKS4KLSBVYW5nOiB0dW5haSBzZWN1a3VwbnlhICsgMSBrYXJ0dSBjYWRhbmdhbi4KLSBFbGVrdHJvbmlrOiBIUCwgY2hhcmdlciwgcG93ZXJiYW5rLCBlYXJwaG9uZS4KLSBPYmF0IHByaWJhZGkgKyBQM0sgbWluaS4KLSBUb2lsZXRyaWVzIHVrdXJhbiB0cmF2ZWwuCgpUZWtuaWs6IGd1bHVuZyAocm9sbGluZykgYmFqdSBtZW5naGVtYXQgdGVtcGF0IGRhbiBhbnRpIGt1c3V0LiBQYWthaSBwYWNraW5nIGN1YmUgdW50dWsga2Vsb21wb2trYW4ga2F0ZWdvcmkuIElzaSByb25nZ2Egc2VwYXR1IGRlbmdhbiBrYXVzIGtha2kuCgpCYXdhIGRpIGthYmluOiBkb2t1bWVuLCBlbGVrdHJvbmlrLCAxIHNldCBiYWp1IGdhbnRpLCBvYmF0IOKAlCBqYWdhLWphZ2EgYmFnYXNpIGRlbGF5LgoKSmFuZ2FuIGJhd2EgImp1c3QgaW4gY2FzZSIgYmVybGViaWhhbi4gQXR1cmFuOiBrYWxhdSByYWd1IGJ1dHVoIGF0YXUgdGlkYWssIHRpbmdnYWxrYW4uCg==',
    'wisata-bali.md': 'IyBXaXNhdGEgQmFsaQoKUGFuZHVhbiBhcmVhOgoKLSBLdXRhL0xlZ2lhbjogcGFudGFpIHN1bnNldCwgcmFtYWksIGNvY29rIHBlcnRhbWEga2FsaS4KLSBDYW5nZ3U6IGthZmUsIHN1cmZpbmcgc2FudGFpLCBhbmFrIG11ZGEuCi0gVWJ1ZDogYnVkYXlhLCBzYXdhaCBUZWdhbGFsYW5nLCB5b2dhLCBsZWJpaCB0ZW5hbmcuCi0gVWx1d2F0dTogdGViaW5nLCBQdXJhIFVsdXdhdHUgKyB0YXJpIGtlY2FrIHNhYXQgc3Vuc2V0LgotIE51c2EgUGVuaWRhOiBLZWxpbmdraW5nIEJlYWNoLCBBbmdlbCdzIEJpbGxhYm9uZyAoc2V3YSBtb3Rvci9iYXdhIHRvdXIpLgoKV2FrdHUgdGVyYmFpazogQXByaWzigJNPa3RvYmVyIChtdXNpbSBrZW1hcmF1KS4gSGluZGFyaSBsaWJ1ciBwYW5qYW5nIGthbGF1IHRpZGFrIHN1a2EgbWFjZXQuCgpUcmFuc3BvcnQ6IHNld2EgbW90b3IgNzUtMTAwIHJiL2hhcmkgcGFsaW5nIGZsZWtzaWJlbC4gTW9iaWwgKyBzdXBpciA1MDAtNzAwIHJiL2hhcmkgdW50dWsgcm9tYm9uZ2FuLgoKVGlwczogYmF3YSB1YW5nIHR1bmFpIHNlY3VrdXBueWEgKGJhbnlhayB3YXJ1bmcga2VjaWwpLCBob3JtYXRpIGFkYXQgKHNvcGFuIGRpIHB1cmEsIGphbmdhbiBpbmphayBzZXNhamVuL2NhbmFuZyksIGRhbiBqYW5nYW4gYmVyaSBtYWthbiBtb255ZXQgZGkgVWx1d2F0dS9VYnVkIHNhbWJpbCBsZW5nYWguCgpFc3RpbWFzaSBoZW1hdDogMzAwLTUwMCByYi9oYXJpIHN1ZGFoIG55YW1hbiB1bnR1ayBtYWthbiBsb2thbCArIG1vdG9yICsgcGVuZ2luYXBhbiBidWRnZXQuCg==',
}

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
    fts_base = fts_q
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
    if not rows and " AND " in fts_base:
        # fallback recall: AND tak dapat apa-apa -> coba OR
        fts_or = fts_base.replace(" AND ", " OR ")
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
            (SNIPPET_TOKENS, fts_or, limit * 3),
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
    except Exception:
        # Fallback: Jina Reader — proxy yang bisa menjangkau situs di luar
        # whitelist outbound PythonAnywhere.
        try:
            rj = urllib.request.Request("https://r.jina.ai/" + url,
                                        headers={"User-Agent": "CARI/0.9"})
            with urllib.request.urlopen(rj, timeout=25) as r:
                raw = r.read(INGEST_MAX_BYTES + 1)
            ctype = "text/markdown"
        except Exception as e2:
            raise ValueError(
                "gagal fetch URL "
                f"({type(e2).__name__}). Di PythonAnywhere gratis, situs harus "
                "masuk whitelist outbound — coba URL dari situs umum populer.") from e2
    if len(raw) > INGEST_MAX_BYTES:
        raise ValueError("halaman terlalu besar (>700KB)")
    m = re.search(r"charset=([\w-]+)", ctype or "")
    html = raw.decode(m.group(1) if m else "utf-8", errors="replace")
    title, text = _html_to_text(html)
    if not title and ctype == "text/markdown":
        # format Jina Reader diawali "Title: ...\nURL Source: ..."
        mt = re.search(r"^Title:\s*(.+)$", html, re.M)
        if mt:
            title = mt.group(1).strip()[:200]
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


# ------------------------------------------------------------- v0.8 Web Mode (metasearch)
# CARI jadi metasearch: narik hasil dari backend web resmi (tanpa API key),
# lalu setiap hasil OTOMATIS di-index permanen ke database lokal -> index
# tumbuh dari pencarianmu (mesin yang benar-benar belajar sendiri).
# Siap Brave Search API: set env BRAVE_API_KEY -> backend brave ikut dipakai
# (perlu api.search.brave.com lolos whitelist outbound).

WEB_UA = {"User-Agent": "CARI/0.9 (personal search engine; +https://adiprmx.github.io/cari/)"}
WEB_TIMEOUT = 10
WEB_CACHE_TTL = 24 * 3600  # detik — hasil web mentah di-cache 1 hari

SCHEMA_WEB = """
CREATE TABLE IF NOT EXISTS web_cache (
    q            TEXT PRIMARY KEY,
    results_json TEXT NOT NULL,
    ts           REAL NOT NULL
);
"""


def _http_get_json(url: str, headers: dict | None = None,
                   timeout: int = WEB_TIMEOUT) -> dict:
    h = dict(WEB_UA)
    if headers:
        h.update(headers)
    req = urllib.request.Request(url, headers=h)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8", "replace"))


def _web_wikipedia(query: str) -> list[dict]:
    """Wikipedia API (id -> fallback en). Resmi, tanpa key."""
    out: list[dict] = []
    for lang in ("id", "en"):
        try:
            u = f"https://{lang}.wikipedia.org/w/api.php?" + urllib.parse.urlencode({
                "action": "query", "list": "search", "srsearch": query,
                "srlimit": 8, "format": "json", "formatversion": "2"})
            d = _http_get_json(u)
            for it in d.get("query", {}).get("search", []):
                title = it.get("title", "")
                url = (f"https://{lang}.wikipedia.org/wiki/"
                       + urllib.parse.quote(title.replace(" ", "_")))
                snip = htmlmod.unescape(re.sub(r"<[^>]+>", "", it.get("snippet", "")))
                out.append({"title": title, "url": url, "snippet": snip.strip(),
                            "source": "wikipedia"})
            if out:
                break
        except Exception:
            continue
    return out


def _web_duckduckgo(query: str) -> list[dict]:
    """DuckDuckGo Instant Answer API. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        u = "https://api.duckduckgo.com/?" + urllib.parse.urlencode(
            {"q": query, "format": "json", "no_html": "1", "skip_disambig": "1"})
        d = _http_get_json(u)

        def walk(topics):
            for t in topics:
                if "Topics" in t:
                    walk(t["Topics"])
                elif t.get("FirstURL"):
                    txt = t.get("Text", "")
                    out.append({
                        "title": (txt.split(" - ")[0].strip()[:90] or t["FirstURL"]),
                        "url": t["FirstURL"],
                        "snippet": txt,
                        "source": "duckduckgo"})

        if d.get("AbstractURL") and d.get("AbstractText"):
            out.append({"title": d.get("Heading") or query,
                        "url": d["AbstractURL"],
                        "snippet": d["AbstractText"],
                        "source": "duckduckgo"})
        walk(d.get("RelatedTopics", []))
    except Exception:
        pass
    return out[:12]


def _web_brave(query: str) -> list[dict]:
    """Brave Search API — aktif kalau env BRAVE_API_KEY di-set."""
    key = os.environ.get("BRAVE_API_KEY", "").strip()
    if not key:
        return []
    try:
        u = "https://api.search.brave.com/res/v1/web/search?" + urllib.parse.urlencode(
            {"q": query, "count": 10, "search_lang": "id", "safesearch": "moderate"})
        d = _http_get_json(u, headers={"X-Subscription-Token": key,
                                       "Accept": "application/json"})
        return [{"title": r.get("title", ""), "url": r.get("url", ""),
                 "snippet": r.get("description", ""), "source": "brave"}
                for r in d.get("web", {}).get("results", []) if r.get("url")]
    except Exception:
        return []


def _web_hackernews(query: str) -> list[dict]:
    """Hacker News via Algolia API. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        u = "https://hn.algolia.com/api/v1/search?" + urllib.parse.urlencode(
            {"query": query, "tags": "story", "hitsPerPage": 8})
        d = _http_get_json(u)
        for h in d.get("hits", []):
            title = h.get("title") or ""
            if not title:
                continue
            url = h.get("url") or \
                f"https://news.ycombinator.com/item?id={h.get('objectID')}"
            out.append({
                "title": title, "url": url,
                "snippet": (f"{h.get('points', 0)} poin · "
                            f"{h.get('num_comments', 0)} komentar · Hacker News"),
                "source": "hackernews"})
    except Exception:
        pass
    return out


def _web_stackexchange(query: str) -> list[dict]:
    """Stack Exchange API (Stack Overflow). Resmi, tanpa key."""
    out: list[dict] = []
    try:
        u = "https://api.stackexchange.com/2.3/search/advanced?" + urllib.parse.urlencode(
            {"order": "desc", "sort": "relevance", "q": query,
             "site": "stackoverflow", "pagesize": 8})
        d = _http_get_json(u)
        for it in d.get("items", []):
            ans = "terjawab" if it.get("is_answered") else "belum terjawab"
            out.append({
                "title": htmlmod.unescape(it.get("title", "")),
                "url": it.get("link", ""),
                "snippet": (f"{ans} · {it.get('answer_count', 0)} jawaban · "
                            f"skor {it.get('score', 0)} · Stack Overflow"),
                "source": "stackexchange"})
    except Exception:
        pass
    return out


WEB_SOURCES = ["wikipedia", "duckduckgo", "ddg_lite", "qwant", "hackernews",
               "stackexchange", "github", "openalex", "arxiv", "pubmed",
               "openlibrary", "archive", "npm", "wikidata"]


# Backoff GitHub saat kena rate-limit (403/429) di IP bersama.
_GITHUB_BACKOFF_UNTIL = 0.0


def _web_github(query: str) -> list[dict]:
    """GitHub user + repo search. Resmi, tanpa key (limit anonim 10 req/mnt).

    IP gratisan dipakai rame-rame -> kalau kena 403/429, backoff 10 menit
    agar tidak menghambat pencarian lain."""
    global _GITHUB_BACKOFF_UNTIL
    if time.time() < _GITHUB_BACKOFF_UNTIL:
        return []
    out: list[dict] = []
    try:
        u = "https://api.github.com/search/users?" + urllib.parse.urlencode(
            {"q": query, "per_page": 4})
        d = _http_get_json(u)
        for it in d.get("items", []):
            if not it.get("html_url"):
                continue
            out.append({
                "title": f"{it.get('login')} (GitHub)",
                "url": it["html_url"],
                "snippet": (it.get("bio") or "Profil GitHub") +
                           f" · {it.get('public_repos', 0)} repo publik",
                "source": "github"})
        u = "https://api.github.com/search/repositories?" + urllib.parse.urlencode(
            {"q": query, "per_page": 6, "sort": "stars", "order": "desc"})
        d = _http_get_json(u)
        for it in d.get("items", []):
            if not it.get("html_url"):
                continue
            out.append({
                "title": it.get("full_name", ""),
                "url": it["html_url"],
                "snippet": (it.get("description") or "Repositori GitHub") +
                            f" · ★ {it.get('stargazers_count', 0)}",
                "source": "github"})
    except urllib.error.HTTPError as e:
        if e.code in (403, 429):
            _GITHUB_BACKOFF_UNTIL = time.time() + 600
        return []
    except Exception:
        return []
    return out[:10]


def _web_ddg_lite(query: str) -> list[dict]:
    """DuckDuckGo Lite (HTML) — hasil web umum. Scraping ringan."""
    out: list[dict] = []
    try:
        u = "https://lite.duckduckgo.com/lite/?" + urllib.parse.urlencode({"q": query})
        req = urllib.request.Request(u, headers={**WEB_UA, "Accept": "text/html"})
        with urllib.request.urlopen(req, timeout=10) as r:
            raw = r.read(300_000).decode("utf-8", "replace")
        for m in re.finditer(
                r'<a[^>]*rel="nofollow"[^>]*href="//duckduckgo\.com/l/\?uddg=([^"&]+)[^"]*"[^>]*>(.*?)</a>',
                raw, re.S):
            url = urllib.parse.unquote(m.group(1))
            title = re.sub(r"<[^>]+>", "", htmlmod.unescape(m.group(2))).strip()
            if url.startswith("http") and title and "duckduckgo.com" not in url:
                out.append({"title": title, "url": url,
                            "snippet": "Hasil web via DuckDuckGo",
                            "source": "ddg_lite"})
            if len(out) >= 6:
                break
    except Exception:
        pass
    return out


def _web_qwant(query: str) -> list[dict]:
    """Qwant API v3 — hasil web umum (Eropa). Tanpa key."""
    out: list[dict] = []
    try:
        u = "https://api.qwant.com/v3/search/web?" + urllib.parse.urlencode(
            {"t": "web", "q": query, "locale": "id_ID", "count": 8, "safesearch": 1})
        d = _http_get_json(u, timeout=10)
        items = d.get("data", {}).get("result", {}).get("items", []) or []
        for it in items:
            url = it.get("url") or ""
            title = htmlmod.unescape((it.get("title") or "").strip())
            if not (url.startswith("http") and title):
                continue
            desc = htmlmod.unescape(re.sub(r"<[^>]+>", "", it.get("desc") or ""))
            out.append({"title": title, "url": url,
                        "snippet": desc[:300] or "Hasil web via Qwant",
                        "source": "qwant"})
            if len(out) >= 6:
                break
    except Exception:
        pass
    return out


def _web_openalex(query: str) -> list[dict]:
    """OpenAlex — paper & jurnal akademik. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        u = "https://api.openalex.org/works?" + urllib.parse.urlencode(
            {"search": query, "per-page": 5,
             "select": "id,doi,title,publication_year,cited_by_count,primary_location"})
        for w in _http_get_json(u, timeout=10).get("results", []):
            title = w.get("title") or ""
            if not title:
                continue
            url = ("https://doi.org/" + w["doi"]) if w.get("doi") else (w.get("id") or "")
            src = ((w.get("primary_location") or {}).get("source") or {})
            meta = " · ".join(x for x in
                              [src.get("display_name") or "",
                               str(w.get("publication_year") or ""),
                               f"disitasi {w.get('cited_by_count', 0)}"] if x)
            out.append({"title": htmlmod.unescape(title), "url": url,
                        "snippet": meta or "Paper akademik", "source": "openalex"})
    except Exception:
        pass
    return out


def _web_arxiv(query: str) -> list[dict]:
    """arXiv — paper ilmiah. Resmi, tanpa key (ATOM XML)."""
    out: list[dict] = []
    try:
        u = "https://export.arxiv.org/api/query?" + urllib.parse.urlencode(
            {"search_query": f'all:"{query}"', "start": 0, "max_results": 5,
             "sortBy": "relevance", "sortOrder": "descending"})
        req = urllib.request.Request(u, headers=dict(WEB_UA))
        with urllib.request.urlopen(req, timeout=12) as r:
            raw = r.read(300_000)
        root = ET.fromstring(raw)
        ns = {"a": "http://www.w3.org/2005/Atom"}
        for e in root.findall("a:entry", ns)[:5]:
            title = re.sub(r"\s+", " ", (e.findtext("a:title", default="",
                                                   namespaces=ns) or "")).strip()
            link = (e.findtext("a:id", default="", namespaces=ns) or "").strip()
            summary = re.sub(r"\s+", " ", (e.findtext("a:summary", default="",
                                                     namespaces=ns) or "")).strip()
            if title and link.startswith("http"):
                out.append({"title": title, "url": link,
                            "snippet": summary[:300] or "Paper arXiv",
                            "source": "arxiv"})
    except Exception:
        pass
    return out


def _web_pubmed(query: str) -> list[dict]:
    """PubMed/NCBI — literatur medis. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        base = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
        s = _http_get_json(base + "esearch.fcgi?" + urllib.parse.urlencode(
            {"db": "pubmed", "term": query, "retmax": 5, "retmode": "json",
             "sort": "relevance", "tool": "cari"}), timeout=10)
        ids = (s.get("esearchresult") or {}).get("idlist", [])
        if not ids:
            return []
        d = _http_get_json(base + "esummary.fcgi?" + urllib.parse.urlencode(
            {"db": "pubmed", "id": ",".join(ids), "retmode": "json",
             "tool": "cari"}), timeout=10)
        res = d.get("result", {})
        for i in res.get("uids", []):
            it = res.get(i) or {}
            title = it.get("title") or ""
            if not title:
                continue
            meta = " · ".join(x for x in
                              [it.get("source") or "", it.get("pubdate") or ""] if x)
            out.append({"title": htmlmod.unescape(title),
                        "url": f"https://pubmed.ncbi.nlm.nih.gov/{i}/",
                        "snippet": meta or "PubMed", "source": "pubmed"})
    except Exception:
        pass
    return out


def _web_openlibrary(query: str) -> list[dict]:
    """Open Library — buku. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        u = "https://openlibrary.org/search.json?" + urllib.parse.urlencode(
            {"q": query, "limit": 5,
             "fields": "key,title,author_name,first_publish_year"})
        for b in _http_get_json(u, timeout=10).get("docs", []):
            key, title = b.get("key") or "", b.get("title") or ""
            if not (key and title):
                continue
            auth = ", ".join(b.get("author_name") or [])
            meta = " · ".join(x for x in
                              [auth, str(b.get("first_publish_year") or "")] if x)
            out.append({"title": title,
                        "url": "https://openlibrary.org" + key,
                        "snippet": meta or "Buku", "source": "openlibrary"})
    except Exception:
        pass
    return out


def _web_archive(query: str) -> list[dict]:
    """Internet Archive — buku/teks/media arsip. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        params = [("q", query), ("fl[]", "identifier"), ("fl[]", "title"),
                  ("fl[]", "description"), ("rows", 5), ("output", "json")]
        u = "https://archive.org/advancedsearch.php?" + urllib.parse.urlencode(params)
        docs = _http_get_json(u, timeout=12).get("response", {}).get("docs", [])
        for it in docs:
            ident = it.get("identifier") or ""
            if not ident:
                continue
            desc = it.get("description") or ""
            if isinstance(desc, list):
                desc = desc[0] if desc else ""
            out.append({"title": it.get("title") or ident,
                        "url": f"https://archive.org/details/{ident}",
                        "snippet": str(desc)[:300] or "Arsip Internet Archive",
                        "source": "archive"})
    except Exception:
        pass
    return out


def _web_npm(query: str) -> list[dict]:
    """npm registry — paket JavaScript. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        u = "https://registry.npmjs.org/-/v1/search?" + urllib.parse.urlencode(
            {"text": query, "size": 5})
        for o in _http_get_json(u, timeout=10).get("objects", []):
            p = o.get("package") or {}
            name = p.get("name") or ""
            if not name:
                continue
            ver = p.get("version") or ""
            out.append({"title": f"{name} {ver}".strip(),
                        "url": f"https://www.npmjs.com/package/{name}",
                        "snippet": (p.get("description") or "Paket npm")[:300],
                        "source": "npm"})
    except Exception:
        pass
    return out


def _web_wikidata(query: str) -> list[dict]:
    """Wikidata — entitas pengetahuan terstruktur. Resmi, tanpa key."""
    out: list[dict] = []
    try:
        u = "https://www.wikidata.org/w/api.php?" + urllib.parse.urlencode(
            {"action": "wbsearchentities", "search": query, "language": "id",
             "uselang": "id", "format": "json", "limit": 5, "formatversion": "2"})
        for it in _http_get_json(u, timeout=10).get("search", []):
            qid = it.get("id") or ""
            if not qid:
                continue
            out.append({"title": it.get("label") or qid,
                        "url": f"https://www.wikidata.org/wiki/{qid}",
                        "snippet": (it.get("description") or "Entitas Wikidata")[:300],
                        "source": "wikidata"})
    except Exception:
        pass
    return out


def _web_slug(url: str) -> str:
    s = re.sub(r"^https?://(www\.)?", "", url.strip().lower())
    s = re.sub(r"[^a-z0-9]+", "-", s).strip("-")
    return s[:80] or "doc"


def _web_rank(query: str, results: list[dict]) -> list[dict]:
    """Re-rank ringan: dahulukan yang judul/snippet-nya memuat kata query."""
    toks = [t for t in _tokens(query) if t not in STOPWORDS] or _tokens(query)

    def score(r: dict) -> int:
        text = (r.get("title", "") + " " + r.get("snippet", "")).lower()
        return sum(1 for t in toks if t in text)

    return sorted(results, key=score, reverse=True)


def web_search(query: str, limit: int = 10) -> dict:
    q = query.strip()
    # kunci cache menyertakan versi engine -> otomatis invalid tiap upgrade,
    # jadi cache basi (mis. hasil kosong sebelum backend baru ada) tak dipakai.
    qn = f"v{VERSION}\x00{q.lower()}"
    brave_on = bool(os.environ.get("BRAVE_API_KEY", "").strip())
    con = _connect()
    con.executescript(SCHEMA_WEB)
    row = con.execute("SELECT results_json, ts FROM web_cache WHERE q = ?", (qn,)).fetchone()
    now = time.time()
    if row and now - row[1] < WEB_CACHE_TTL:
        con.close()
        results = _web_rank(q, json.loads(row[0]))
        _log_event("search", query=q)
        return {"query": q, "results": results[:limit],
                "sources": sorted({r["source"] for r in results}),
                "cached": True, "brave": brave_on, "learned": 0}
    results: list[dict] = []
    backends = [_web_wikipedia, _web_duckduckgo, _web_ddg_lite, _web_qwant,
                _web_hackernews, _web_stackexchange, _web_github,
                _web_openalex, _web_arxiv, _web_pubmed, _web_openlibrary,
                _web_archive, _web_npm, _web_wikidata, _web_brave]
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(backends)) as ex:
        futs = [ex.submit(fn, q) for fn in backends]
        for f in concurrent.futures.as_completed(futs):
            try:
                results.extend(f.result() or [])
            except Exception:
                pass
    seen, uniq = set(), []
    for r in results:
        u = (r.get("url") or "").rstrip("/")
        if u and u not in seen:
            seen.add(u)
            uniq.append(r)
    uniq = uniq[:max(limit * 2, 20)]
    # jangan cache hasil kosong: backend bisa pulih (mis. rate-limit reda),
    # dan hasil kosong yang di-cache menutupi hasil baru selama 24 jam.
    if uniq:
        con.execute("INSERT OR REPLACE INTO web_cache(q, results_json, ts) VALUES (?,?,?)",
                    (qn, json.dumps(uniq, ensure_ascii=False), now))
        con.commit()
    # --- belajar: index permanen ke database lokal (skip kalau sudah ada) ---
    learned = 0
    for r in uniq:
        doc_id = f"web-{r['source']}-{_web_slug(r['url'])}"
        fname = "".join(c if (c.isalnum() or c in "-_") else "_" for c in doc_id)[:80]
        exists = con.execute(
            "SELECT 1 FROM docs WHERE path = ?",
            (os.path.join(DATA_DIR, fname + ".md"),)).fetchone()
        if exists:
            continue
        try:
            index_document(doc_id, r["title"] or doc_id,
                           f"Sumber: {r['url']}\n\n{r['snippet']}")
            learned += 1
        except Exception:
            pass
    _log_event("search", query=q)
    con.close()
    uniq = _web_rank(q, uniq)
    return {"query": q, "results": uniq[:limit],
            "sources": sorted({r["source"] for r in uniq}),
            "cached": False, "brave": brave_on, "learned": learned}


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
                     {"status": "ok", "version": VERSION, "engine": ENGINE_NAME,
                      "web": True,
                      "web_sources": WEB_SOURCES
                      + (["brave"] if os.environ.get("BRAVE_API_KEY", "").strip() else [])})

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

    # --- v0.8 Web Mode (metasearch + belajar otomatis) ---
    if path == "/web/search" and method == "GET":
        qp = _query_params(environ)
        q = qp.get("q", "").strip()
        if not q:
            return _json(start_response, "Bad Request",
                         {"detail": "parameter q wajib diisi"}, 400)
        try:
            limit = max(1, min(int(qp.get("limit", "10")), 20))
        except (TypeError, ValueError):
            limit = 10
        try:
            return _json(start_response, "OK", web_search(q, limit))
        except Exception as e:
            return _json(start_response, "Bad Gateway",
                         {"detail": f"Web search gagal: {e}"}, 502)

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
