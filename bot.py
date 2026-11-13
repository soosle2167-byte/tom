import json
from pathlib import Path
import base64
import secrets
import string
import zipfile
import asyncio
import requests
import datetime
import re
import random
from playwright.async_api import async_playwright
from telegram import Update, ReplyKeyboardMarkup, ReplyKeyboardRemove, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes, ConversationHandler, CallbackQueryHandler

# --- الإعدادات الفنية وصناديق التخزين الموثوقة ---
ADMIN_IDS = [1955621195, 1087964579]
BASE_DIR = Path(__file__).resolve().parent
BACKUPS_DIR = BASE_DIR / "backups"

def data_file(filename):
    return BASE_DIR / filename

VOUCHERS_FILE = data_file("vouchers.json")
BALANCE_FILE = data_file("user_balance.json")
BANNED_FILE = data_file("banned_users.json")
SETTINGS_FILE = data_file("settings.json")
ACCOUNTS_FILE = data_file("accounts.json")
REFERRALS_FILE = data_file("referrals.json")
PENDING_REQ_FILE = data_file("pending_requests.json")
USER_DETAILS_FILE = data_file("user_details.json")
FREE_JOIN_BONUS_FILE = data_file("free_join_bonus_claimed.json")
BOT_PROGRESS_FILE = data_file("bot_progress.json")
USED_TX_FILE = data_file("used_transactions.json")
UNCLAIMED_TX_FILE = data_file("unclaimed_transactions.json")
ACCOUNT_DAILY_LIMIT = 5
ACCOUNT_COOLDOWN_SECONDS = 24 * 60 * 60

# مراحل المحادثة (الكومبنيشن)
CHANGE_PRICE = 0
BROADCAST_MSG = 1
BAN_USER = 2
SELECT_QUANTITY = 3
SEND_PAYMENT_INFO = 4
LINK_WAITING = 5
CODE_WAITING = 6
CHANGE_WALLET = 7
AUTO_MSG_WAITING = 8
CHECK_USER_BAL_WAITING = 9
MODIFY_USER_BAL_QTY = 10
GIVE_CODE_POINTS = 11
MANAGE_PURCHASE_OFFERS = 12

COMMON_HEADERS = {
    'accept': 'application/json, text/plain, */*',
    'accept-language': 'en-US,en;q=0.9,ar;q=0.8',
    'cache-control': 'no-cache',
    'content-type': 'application/json',
    'origin': 'https://www.midasbuy.com',
    'pragma': 'no-cache',
    'priority': 'u=1, i',
    'referer': 'https://www.midasbuy.com/',
    'sec-ch-ua': '"(Not(A:Brand";v="99", "Google Chrome";v="134", "Chromium";v="134"',
    'sec-ch-ua-full-version-list': '"(Not(A:Brand";v="99.0.0.0", "Google Chrome";v="134", "Chromium";v="134"',
    'sec-ch-ua-mobile': '?0',
    'sec-ch-ua-platform': '"Windows"',
    'sec-fetch-dest': 'empty',
    'sec-fetch-mode': 'cors',
    'sec-fetch-site': 'same-site'
}

# --- دالات الوقت وتحديد الجدولة بتوقيت مصر ---
def get_egypt_time():
    """الحصول على توقيت القاهرة الفعلي تزامناً مع التوقيت الصيفي/الشتوي"""
    try:
        from zoneinfo import ZoneInfo
        return datetime.datetime.now(ZoneInfo("Africa/Cairo"))
    except Exception:
        # حساب التوقيت الصيفي/الشتوي لمصر يدوياً بدقة فائقة كبديل آمن لحالة عدم توفر tzdata
        utc_now = datetime.datetime.utcnow()
        year = utc_now.year
        
        # ليلة الجمعة الأخيرة من أبريل يبدأ التوقيت الصيفي (UTC+3)
        last_friday_april = datetime.datetime(year, 4, 30, 23, 0, 0)
        while last_friday_april.weekday() != 4:  # 4 هو الجمعة
            last_friday_april -= datetime.timedelta(days=1)
            
        # ليلة الخميس الأخيرة من أكتوبر ينتهي التوقيت الصيفي ويعود للشتوي (UTC+2)
        last_thursday_october = datetime.datetime(year, 10, 31, 23, 0, 0)
        while last_thursday_october.weekday() != 3:  # 3 هو الخميس
            last_thursday_october -= datetime.timedelta(days=1)
            
        if last_friday_april <= utc_now <= last_thursday_october:
            return utc_now + datetime.timedelta(hours=3)
        else:
            return utc_now + datetime.timedelta(hours=2)

def get_egypt_quota_day():
    """تحديد يوم الكوتا الحالي لتوقيت القاهرة - يتغير تلقائياً عند الساعة ٢ فجراً"""
    egypt_now = get_egypt_time()
    if egypt_now.hour < 2:
        # قبل الساعة ٢ فجراً، نحسب اليوم السابق كجزء من الكوتا الجارية
        egypt_now = egypt_now - datetime.timedelta(days=1)
    return egypt_now.strftime("%Y-%m-%d")

def check_and_reset_accounts_quota(accounts):
    """التحقق وتصفير العداد لجميع الحسابات إذا دخل يوم كوتا جديد"""
    current_quota_day = get_egypt_quota_day()
    modified = False
    for acc in accounts:
        quota_day = acc.get("lastHelpQuotaDay") or acc.get("last_help_quota_day")
        if quota_day != current_quota_day:
            if is_account_in_cooldown(acc):
                continue
            acc["helpCountToday"] = 0
            acc["lastHelpQuotaDay"] = current_quota_day
            acc["cooldown_until"] = None
            if "help_count_today" in acc:
                acc["help_count_today"] = 0
            if "last_help_quota_day" in acc:
                acc["last_help_quota_day"] = current_quota_day
            modified = True
    return modified

def get_account_help_count(acc):
    value = acc.get("helpCountToday")
    if value is None:
        value = acc.get("help_count_today", 0)
    try:
        return int(value or 0)
    except (TypeError, ValueError):
        return 0

def get_account_display_name(acc, index=None):
    for key in ("label", "name", "username", "userId", "user_id", "id", "playerId", "player_id"):
        value = acc.get(key)
        if value:
            return str(value)
    if index is not None:
        return f"account #{index + 1}"
    return "unknown account"

def get_current_timestamp():
    return datetime.datetime.now(datetime.timezone.utc).timestamp()

def parse_cooldown_until(value):
    if not value:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            try:
                text = value.replace("Z", "+00:00")
                dt = datetime.datetime.fromisoformat(text)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=datetime.timezone.utc)
                return dt.timestamp()
            except ValueError:
                return None
    return None

def format_cooldown_timestamp(ts):
    return datetime.datetime.fromtimestamp(ts, datetime.timezone.utc).isoformat()

def is_account_in_cooldown(acc, now_ts=None):
    now_ts = now_ts if now_ts is not None else get_current_timestamp()
    cooldown_until = parse_cooldown_until(acc.get("cooldown_until"))
    return cooldown_until is not None and cooldown_until > now_ts

def reset_account_help_counter(acc):
    acc["helpCountToday"] = 0
    acc["lastHelpQuotaDay"] = get_egypt_quota_day()
    acc["cooldown_until"] = None
    if "help_count_today" in acc:
        acc["help_count_today"] = 0
    if "last_help_quota_day" in acc:
        acc["last_help_quota_day"] = acc["lastHelpQuotaDay"]

def put_account_to_cooldown(acc, now_ts=None):
    now_ts = now_ts if now_ts is not None else get_current_timestamp()
    acc["cooldown_until"] = format_cooldown_timestamp(now_ts + ACCOUNT_COOLDOWN_SECONDS)

def refresh_account_cooldowns(accounts):
    now_ts = get_current_timestamp()
    modified = False
    for acc in accounts:
        cooldown_until = parse_cooldown_until(acc.get("cooldown_until"))
        if cooldown_until is not None and cooldown_until <= now_ts:
            reset_account_help_counter(acc)
            modified = True
        elif get_account_help_count(acc) >= ACCOUNT_DAILY_LIMIT and not is_account_in_cooldown(acc, now_ts):
            put_account_to_cooldown(acc, now_ts)
            modified = True
    return modified

def get_available_account_indexes(accounts):
    now_ts = get_current_timestamp()
    indexes = []
    for idx, acc in enumerate(accounts):
        if get_account_help_count(acc) >= ACCOUNT_DAILY_LIMIT:
            continue
        if is_account_in_cooldown(acc, now_ts):
            continue
        indexes.append(idx)
    return indexes

def is_same_account(acc1, acc2):
    """التحقق القوي لمعرفة ما إذا كان الحسابان متطابقين باستخدام معرفات وخاصيات فريدة"""
    # 1. التحقق من الرقم التعريفي الرئيسي (تجنب الحقول الفارغة)
    id1 = acc1.get("id")
    id2 = acc2.get("id")
    if id1 and id2 and str(id1).strip() == str(id2).strip() and str(id1).strip() != "":
        return True

    # 2. التحقق من الـ userId بجميع أشكاله (تجنب الحقول الفارغة)
    u_id1 = acc1.get("userId") or acc1.get("user_id")
    u_id2 = acc2.get("userId") or acc2.get("user_id")
    if u_id1 and u_id2 and str(u_id1).strip() == str(u_id2).strip() and str(u_id1).strip() != "":
        return True

    # 3. التحقق من الـ playerId بجميع أشكاله (تجنب الحقول الفارغة)
    pl_id1 = acc1.get("playerId") or acc1.get("player_id")
    pl_id2 = acc2.get("playerId") or acc2.get("player_id")
    if pl_id1 and pl_id2 and str(pl_id1).strip() == str(pl_id2).strip() and str(pl_id1).strip() != "":
        return True

    # 4. التحقق من الـ cookie إذا كانت متطابقة تماماً كبديل أخير (تجنب الحقول الفارغة)
    c1 = acc1.get("cookie")
    c2 = acc2.get("cookie")
    if c1 and c2 and str(c1).strip() == str(c2).strip() and str(c1).strip() != "":
        return True

    return False

# --- دالة توليد رقم المعاملة الفريد ---
def generate_uuid():
    """توليد معرف فريد (UUID) يحاكي تماماً خوارزمية JavaScript بموقع Midasbuy"""
    chars = list("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
    uuid = [None] * 36
    for i in [8, 13, 18, 23]:
        uuid[i] = "-"
    uuid[14] = "4"
    for i in range(36):
        if uuid[i] is None:
            r = random.random() * 16
            if i == 19:
                val = int(r) & 0x3 | 0x8
            else:
                val = int(r)
            uuid[i] = chars[val]
    return "".join(uuid)

# --- دوال إدارة البيانات المساعدة الموثوقة ---
def load_data(file, default):
    file_path = Path(file)
    if file_path.exists():
        try:
            with file_path.open('r', encoding='utf-8') as f:
                return json.load(f)
        except Exception:
            return default
    return default

def save_data(file, data):
    file_path = Path(file)
    file_path.parent.mkdir(parents=True, exist_ok=True)
    tmp_file = Path(str(file_path) + '.tmp')
    with tmp_file.open('w', encoding='utf-8') as f:
        json.dump(data, f, indent=4, ensure_ascii=False)
    tmp_file.replace(file_path)

def load_settings():
    default_settings = {
        "price": 15,
        "wallet": "01036428989",
        "channels": [],
        "group_id": None,
        "delivery_method": "direct",
        "purchase_offers": [],
        "open_mode": False
    }
    settings = load_data(SETTINGS_FILE, default_settings.copy())
    for key, value in default_settings.items():
        settings.setdefault(key, value)
    return settings

def parse_payment_message(text):
    if not text:
        return None
    phones = re.findall(r'\b01[0125]\d{8}\b', text)
    if not phones:
        return None
        
    try:
        settings = load_settings()
        wallet = settings.get("wallet", "")
    except Exception:
        wallet = ""
        
    # If the bot's wallet is in the numbers, filter it out as it is the receiver, not the sender
    sender_phones = [p for p in phones if p != wallet]
    if sender_phones:
        phone = sender_phones[0]
    else:
        phone = phones[0]
        
    # Also attempt to match using "من" context (indicates the sender)
    context_match = re.search(r'من\s+.*?(01[0125]\d{8})', text, re.DOTALL)
    if context_match:
        phone = context_match.group(1)
    
    amount_patterns = [
        r'(?:بمبلغ|مبلغ)\s*(\d+(?:\.\d+)?)',
        r'(\d+(?:\.\d+)?)\s*(?:جنيه|جنية|egp|le|l\.e)'
    ]
    amount = None
    for pattern in amount_patterns:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            try:
                amount = float(match.group(1))
                break
            except ValueError:
                continue
    
    tx_patterns = [
        r'رقم\s+(?:العملية|المعاملة)\s*[:#-]?\s*(\d+)',
        r'transaction\s*(?:id|no|number)?\s*[:#-]?\s*(\d+)'
    ]
    tx_id = None
    for pattern in tx_patterns:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            tx_id = match.group(1)
            break
            
    if not tx_id:
        all_numbers = re.findall(r'\b\d{8,15}\b', text)
        for num in all_numbers:
            if num != phone and num != wallet:
                tx_id = num
                break

    if phone and amount is not None and tx_id:
        if amount.is_integer():
            amount = int(amount)
        return {
            "phone": phone,
            "amount": amount,
            "tx_id": tx_id
        }
    return None

async def auto_confirm_order(uid, qty, total, sender_number, tx_id, context):
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    delivery_method = settings.get("delivery_method", "direct")
    
    if delivery_method == "direct":
        balances = load_data(BALANCE_FILE, {})
        balances[str(uid)] = balances.get(str(uid), 0) + qty
        save_data(BALANCE_FILE, balances)
        
        try:
            await context.bot.send_message(
                chat_id=int(uid), 
                text=f"🎉 <b>رائع! لقد تم التحقق من معاملتك المالية وإضافة {qty} رابط (نقاط) إلى حسابك بنجاح!</b>", 
                parse_mode='HTML'
            )
        except Exception:
            pass
    else:
        generated_codes = []
        vouchers = load_data(VOUCHERS_FILE, {})
        for _ in range(qty):
            code = "LK-BUY-" + ''.join(secrets.choice(string.ascii_uppercase + string.digits) for _ in range(12))
            vouchers[code] = {"status": "active"}
            generated_codes.append(code)
        save_data(VOUCHERS_FILE, vouchers)
        
        codes_formatted = "\n".join([f"<code>{c}</code>" for c in generated_codes])
        try:
            await context.bot.send_message(
                chat_id=int(uid),
                text=f"🎉 <b>تم قبول طلب الشراء الخاص بك بنجاح!</b>\n\n"
                     f"🗝️ لقد أرسلت لك الإدارة أكواد تفعيل روابطك:\n\n"
                     f"{codes_formatted}\n\n"
                     f"قم بنسخ الأكواد واستخدامها لشحن حسابك من قسم '🔑 كود تفعيل'.",
                parse_mode='HTML'
            )
        except Exception:
            pass

    confirm_msg = (
        f"✅ <b>تم التأكيد الأوتوماتيكي بنجاح!</b>\n"
        f"👤 المستخدم: <code>{uid}</code>\n"
        f"📦 الكمية: <code>{qty} رابط</code>\n"
        f"💰 المبلغ: <code>{total} جنيه</code>\n"
        f"🔢 رقم العملية: <code>{tx_id}</code>"
    )
    
    used_tx = load_data(USED_TX_FILE, {})
    used_tx[tx_id] = {
        "uid": uid,
        "phone": sender_number,
        "amount": total,
        "timestamp": get_current_timestamp()
    }
    save_data(USED_TX_FILE, used_tx)
    
    unclaimed = load_data(UNCLAIMED_TX_FILE, {})
    if tx_id in unclaimed:
        del unclaimed[tx_id]
        save_data(UNCLAIMED_TX_FILE, unclaimed)
        
    return confirm_msg


def get_purchase_offers(settings=None):
    settings = settings or load_settings()
    valid_offers = []
    for offer in settings.get("purchase_offers", []):
        try:
            qty = int(offer.get("qty", 0))
            price = int(offer.get("price", 0))
            label = str(offer.get("label", "")).strip()
            if qty > 0 and price > 0:
                valid_offers.append({
                    "label": label or f"{qty} لينك",
                    "qty": qty,
                    "price": price
                })
        except Exception:
                continue
    return valid_offers

def to_arabic_digits(value):
    return str(value).translate(str.maketrans("0123456789", "٠١٢٣٤٥٦٧٨٩"))

def to_english_digits(value):
    return str(value).translate(str.maketrans("٠١٢٣٤٥٦٧٨٩", "0123456789"))

def build_offer_button_text(offer):
    return f"{offer['label']} ب {to_arabic_digits(offer['price'])} ج"

def parse_purchase_offer_text(text):
    cleaned = to_english_digits(text).strip()
    cleaned = re.sub(r"[\u200e\u200f\u202a-\u202e]", "", cleaned)
    if cleaned.startswith("🎁"):
        cleaned = cleaned[1:].strip()
    match = re.match(r"(.+?)\s+(?:ب\s*)?(\d+)\s*(?:ج|جنيه)?\s*$", cleaned)
    if not match:
        match = re.match(r"(.+?)\s*(?:ب|بسعر|=|-)\s*(\d+)\s*(?:ج|جنيه)?\s*$", cleaned)
    if not match:
        return None
    label = match.group(1).strip()
    price = int(match.group(2))
    qty_parts = [int(num) for num in re.findall(r"\d+", label)]
    qty = sum(qty_parts)
    if qty <= 0 or price <= 0:
        return None
    if "🎁" not in label:
        label = f"{label}🎁"
    return {"label": label, "qty": qty, "price": price}

def refund_user_credit(user_id, amount=1):
    if not user_id:
        return None
    user_id = str(user_id)
    balances = load_data(BALANCE_FILE, {})
    balances[user_id] = balances.get(user_id, 0) + amount
    save_data(BALANCE_FILE, balances)
    return balances[user_id]

def grant_free_join_bonus_once(user_id):
    user_id = str(user_id)
    settings = load_settings()
    if not settings.get("channels"):
        return False, None

    claimed = load_data(FREE_JOIN_BONUS_FILE, {})
    if claimed.get(user_id):
        return False, None

    balances = load_data(BALANCE_FILE, {})
    balances[user_id] = balances.get(user_id, 0) + 1
    save_data(BALANCE_FILE, balances)

    claimed[user_id] = {
        "claimed_at": datetime.datetime.utcnow().isoformat(),
        "bonus": 1
    }
    save_data(FREE_JOIN_BONUS_FILE, claimed)
    return True, balances[user_id]

def register_user_details(user):
    if not user:
        return
    try:
        user_id = str(user.id)
        details = load_data(USER_DETAILS_FILE, {})
        username = user.username
        first_name = user.first_name
        
        changed = False
        if user_id not in details:
            details[user_id] = {}
            changed = True
            
        old_username = details[user_id].get("username", "")
        old_first_name = details[user_id].get("first_name", "")
        
        if username and old_username != username:
            details[user_id]["username"] = username
            changed = True
        elif not username and "username" not in details[user_id]:
            details[user_id]["username"] = ""
            changed = True
            
        if first_name and old_first_name != first_name:
            details[user_id]["first_name"] = first_name
            changed = True
        elif not first_name and "first_name" not in details[user_id]:
            details[user_id]["first_name"] = ""
            changed = True
            
        if changed:
            save_data(USER_DETAILS_FILE, details)
    except Exception as e:
        print(f"Error registering user: {e}")

def is_banned(user_id):
    banned = load_data(BANNED_FILE, [])
    return str(user_id) in banned

# استخلاص وتجهيز روابط القنوات/المجموعات للاشتراك الإجباري بشكل آمن
async def get_channel_invite_link(chat_id, context):
    chat_str = str(chat_id)
    if chat_str.startswith("@"):
        return f"https://t.me/{chat_str[1:]}"
    try:
        chat = await context.bot.get_chat(chat_id=chat_id)
        if chat.invite_link:
            return chat.invite_link
        link = await context.bot.export_chat_invite_link(chat_id=chat_id)
        return link
    except Exception as e:
        print(f"Error getting invite link for {chat_id}: {e}")
        if chat_str.startswith("-100"):
            return f"https://t.me/c/{chat_str[4:]}/1"
        return "https://t.me"

# التحقق من الاشتراك الإجباري
async def check_channel_subscription(user_id, context):
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    channels = settings.get("channels", [])
    unsubscribed = []
    for ch in channels:
        try:
            member = await context.bot.get_chat_member(chat_id=ch, user_id=user_id)
            if member.status in ['left', 'kicked']:
                unsubscribed.append(ch)
        except Exception as e:
            print(f"Error checking sub for {ch}: {e}")
            pass
    return unsubscribed

# دالة مساعدة لحفظ قيد البوتات والاشتراك
async def handle_user_prechecks(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id):
    if is_banned(user_id):
        return False
    if 'math_ans' in context.user_data:
        if update.effective_chat.type in ['group', 'supergroup']:
            return False
        await update.message.reply_text("⚠️ <b>يرجى حل المسألة الموضحة بالأعلى أولاً للتحقق من هويتك كعضو حقيقي!</b>", parse_mode='HTML')
        return False
    unsubscribed = await check_channel_subscription(user_id, context)
    if unsubscribed:
        if update.effective_chat.type in ['group', 'supergroup']:
            return False
        keyboard = []
        for ch in unsubscribed:
            url_ch = await get_channel_invite_link(ch, context)
            keyboard.append([InlineKeyboardButton("📢 اشترك في جروب البوت الرسمي", url=url_ch)])
        keyboard.append([InlineKeyboardButton("🔄 تحقق من الاشتراك", callback_data="check_subs")])
        await update.message.reply_text(
            "⚠️ <b>عذراً! يجب عليك الاشتراك في قنوات البوت الرسمية أولاً لتتمكن من استخدام ميزاته:</b>",
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode='HTML'
        )
        return False
    bonus_granted, new_balance = grant_free_join_bonus_once(user_id)
    if bonus_granted and update.effective_chat.type not in ['group', 'supergroup']:
        await update.message.reply_text(
            f"🎁 تم إضافة 1 نقطة مجانية لرصيدك لأول اشتراك ناجح.\nرصيدك الحالي: <code>{new_balance}</code> رابط.",
            parse_mode='HTML'
        )
    return True

# --- دالة استخلاص الرابط النقي لتجنب أخطاء Playwright ---
def extract_clean_url(text):
    match = re.search(r'(https?://[^\s\"\'\<\>]*midasbuy\.com[^\s\"\'\<\>]*)', text)
    if match:
        return match.group(1).strip()
    return None

async def get_purchase_deep_link(context):
    bot_info = await context.bot.get_me()
    return f"https://t.me/{bot_info.username}?start=buy"

async def send_group_buy_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE, text, button_text):
    buy_url = await get_purchase_deep_link(context)
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton(button_text, url=buy_url)]
    ])
    await update.message.reply_text(
        text,
        reply_markup=keyboard,
        parse_mode='HTML',
        reply_to_message_id=update.message.message_id
    )

# --- إدارة المتصفح الدائم المفتوح لتسريع صيد الروابط ---
BROWSER_LOCK = asyncio.Lock()
CAPTURE_LOCK = asyncio.Lock()
PLAYWRIGHT_INSTANCE = None
BROWSER_CONTEXT = None
PERSISTENT_PAGE = None

async def reset_browser_state():
    global PLAYWRIGHT_INSTANCE, BROWSER_CONTEXT, PERSISTENT_PAGE
    old_context = BROWSER_CONTEXT
    old_playwright = PLAYWRIGHT_INSTANCE
    BROWSER_CONTEXT = None
    PLAYWRIGHT_INSTANCE = None
    PERSISTENT_PAGE = None

    try:
        if old_context:
            await old_context.close()
    except Exception:
        pass
    try:
        if old_playwright:
            await old_playwright.stop()
    except Exception:
        pass

async def get_browser_context_and_page():
    global PLAYWRIGHT_INSTANCE, BROWSER_CONTEXT, PERSISTENT_PAGE
    async with BROWSER_LOCK:
        browser_needs_start = BROWSER_CONTEXT is None or PERSISTENT_PAGE is None
        if not browser_needs_start:
            try:
                browser_needs_start = PERSISTENT_PAGE.is_closed()
            except Exception:
                browser_needs_start = True

        if browser_needs_start:
            await reset_browser_state()
            cookies_path = BASE_DIR / "profiles_1"
            profile_id = "capturer"
            new_user_data_dir = cookies_path / f"Profile_{profile_id}_data"
            new_user_data_dir.mkdir(parents=True, exist_ok=True)
            try:
                PLAYWRIGHT_INSTANCE = await async_playwright().start()
                BROWSER_CONTEXT = await PLAYWRIGHT_INSTANCE.chromium.launch_persistent_context(
                    user_data_dir=str(new_user_data_dir),
                    headless=True,
                    args=[
                        "--headless=new",
                        "--no-sandbox",
                        "--disable-dev-shm-usage",
                        "--disable-gpu",
                        "--disable-blink-features=AutomationControlled",
                    ]
                )
                pages = BROWSER_CONTEXT.pages
                if pages:
                    PERSISTENT_PAGE = pages[0]
                else:
                    PERSISTENT_PAGE = await BROWSER_CONTEXT.new_page()
                await PERSISTENT_PAGE.add_init_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined})")
                print("✅ Playwright Chromium browser is open and ready.")
            except Exception:
                await reset_browser_state()
                raise
    return BROWSER_CONTEXT, PERSISTENT_PAGE

async def keep_browser_alive():
    while True:
        try:
            await get_browser_context_and_page()
        except Exception as e:
            print(f"⚠️ فشل فتح متصفح Playwright وسيتم إعادة المحاولة: {e}")
        await asyncio.sleep(10)

# --- دالة صيد الـ mp_help_id المتقدمة الفائقة السرعة ---
async def capture_help_id_from_link(target_link):
    async with CAPTURE_LOCK:
        try:
            _, page = await get_browser_context_and_page()
            try:
                await page.goto(target_link, timeout=6000, wait_until="domcontentloaded")
            except Exception as e:
                print(f"تنبيه goto (يتم المتابعة): {e}")

            try:
                await page.wait_for_timeout(2000)
            except Exception:
                await asyncio.sleep(2)

            full_url = page.url
            if "token=" not in full_url:
                print("تعذر العثور على token في الرابط النهائي")
                return None

            token = full_url.split("token=", 1)[1]
            padding = "=" * (-len(token) % 4)
            data = json.loads(base64.urlsafe_b64decode(token + padding))
            help_id = data["id"]
            print(f"\n🎯 [تم استخراج الـ ID بنجاح]: {help_id}")
            return help_id
        except Exception as e:
            print(f"حدث خطأ أثناء استخراج الـ ID من التوكن: {e}")
            return None

# --- تنفيذ ريكوستات الحساب الواحد وثغرة الدوران ---
def execute_account_api(acc, current_help_id, invite_short_code):
    headers = COMMON_HEADERS.copy()
    
    # دعم التوافق مع camelCase و snake_case
    traceparent_val = acc.get('traceparent') or '00-349f9db193b2a3cdcb9e248f0e0f0981-d3ef9798ef01b17a-01'
    ua_val = acc.get('userAgent') or acc.get('user_agent', 'Mozilla/5.0')
    cookie_val = acc.get('cookie', '')
    login_check_val = acc.get('xTencentLoginCheck') or acc.get('x_tencent_login_check', '1')
    user_id_val = acc.get('userId') or acc.get('user_id', '')
    muid_val = acc.get('muid', '')
    player_id_val = acc.get('playerId') or acc.get('player_id', '')

    headers.update({
        'traceparent': traceparent_val,
        'User-Agent': ua_val,
        'Cookie': cookie_val,
        'x-tencent-login-check': login_check_val
    })

    url_help = "https://pagedooapi.midasbuy.com/api/CallMpgo/osmidas/dd_help_model/HelpInfo"
    payload_help = json.dumps({
        "mp_sub_activity_id": "1765885028499935675DHA",
        "mp_help_id": current_help_id,
        "mp_activity_id": "Activity_1765885024_KZDOIV",
        "mp_app_id": "1450015065",
        "user_id": user_id_val,
        "user_id_type": "hy_gameid",
        "mp_help_meta_data": {
            "ori_zoneid": "1",
            "client_ver": "android",
            "server_id": "1",
            "role_id": "",
            "muid": muid_val,
            "player_id": player_id_val
        }
    })
    
    resp_help_raw = requests.post(url_help, headers=headers, data=payload_help, timeout=2)
    resp_help = resp_help_raw.json()
    current_count = resp_help.get('data', {}).get('mp_help_count', 0)
    max_count = resp_help.get('data', {}).get('mp_help_count_max', 30)
    
    if current_count >= max_count:
        return "STOP_ALL", current_count, max_count

    new_trade_no = generate_uuid()

    url_slave = "https://pagedooapi.midasbuy.com/api/CallMpgo/osmidas/dd_help_model/SlaveHelp"
    payload_slave = json.dumps({
        "mp_activity_trade_no": new_trade_no,
        "mp_help_id": current_help_id,
        "mp_help_meta_data": {
            "ori_zoneid": "1",
            "client_ver": "android",
            "server_id": "1",
            "role_id": "",
            "muid":  muid_val,
            "player_id": player_id_val,
            "pf": f"share.activity.copy.Activity_1765885024_KZDOIV.02182631781323251777219035454#f_099515370c88f03302822d544f2468eb_yy#U24q8jzo9gw7l8#62557827935634728.{invite_short_code}"
        },
        "mp_sub_activity_id": "1765885028499935675DHA",
        "mp_activity_id": "Activity_1765885024_KZDOIV",
        "mp_app_id": "1450015065",
        "user_id": user_id_val,
        "user_id_type": "hy_gameid"
    })
    resp_slave = requests.post(url_slave, headers=headers, data=payload_slave, timeout=2).json()
    result_info = resp_slave.get('result_info', '')
    print(resp_slave)
    print(result_info)
    
    if result_info == "login state check failed" or "login check" in result_info:
        return "LOGIN_FAILED", current_count, max_count  

    # "بس متحطش في اعتبارك رد السيرفر بهيلب لميت تو داي"
    # إذا رجع السيرفر هيلب ليميت تو داي أو نجاح فكلاهما يُعد محاولة مساعدة ناجحة ونحتسبه محلياً ضمن الـ ٥ اليومية
    if result_info == "help limit today":
        return "ACCOUNT_LIMIT", current_count, max_count

    return "SUCCESS", current_count, max_count

# --- دوال حفظ واسترداد حالة التقدم للملف bot_progress.json لمنع الفقدان عند قفل السيرفر ---
def save_bot_progress(chat_id, link, invite_short_code, captured_id, status_msg_id, current_index, success_count, fail_count, start_time, user_name):
    data = {
        "chat_id": chat_id,
        "link": link,
        "invite_short_code": invite_short_code,
        "captured_id": captured_id,
        "status_msg_id": status_msg_id,
        "current_index": current_index,
        "success_count": success_count,
        "fail_count": fail_count,
        "start_time": start_time,
        "user_name": user_name,
        "status": "running"
    }
    save_data(BOT_PROGRESS_FILE, data)

def clear_bot_progress():
    if BOT_PROGRESS_FILE.exists():
        try:
            BOT_PROGRESS_FILE.unlink()
        except Exception:
            pass

# --- المحرك الرئيسي لمعالجة ريكوستات البوت مع شريط تقدم جذاب ودعم كامل للاستئناف والحدود اليومية ---
async def process_bot_link_engine(
    link, chat_id, context, user_name, user_handle, 
    is_group=False, reply_to_message_id=None,
    resume_index=0, resume_success=0, resume_fail=0, resume_start_time=None,
    charged_user_id=None, refund_on_failure=False
):
    refund_done = False

    async def refund_if_needed(reason):
        nonlocal refund_done
        if not refund_on_failure or not charged_user_id or refund_done:
            return
        new_balance = refund_user_credit(charged_user_id, 1)
        refund_done = True
        try:
            await context.bot.send_message(
                chat_id=chat_id,
                text=(
                    "↩️ <b>تم إرجاع الرصيد المخصوم تلقائياً.</b>\n\n"
                    f"السبب: {reason}\n"
                    f"رصيدك الحالي الآن: <code>{new_balance}</code> رابط."
                ),
                parse_mode='HTML',
                reply_to_message_id=reply_to_message_id
            )
        except Exception:
            pass

    if not ACCOUNTS_FILE.exists():
        await context.bot.send_message(chat_id=chat_id, text="❌", reply_to_message_id=reply_to_message_id)
        await refund_if_needed("ملف الحسابات غير موجود")
        return

    with open(ACCOUNTS_FILE, 'r', encoding='utf-8') as f:
        accounts = json.load(f)

    # التحقق من الكوتا اليومية وتصفيرها
    if check_and_reset_accounts_quota(accounts):
        save_data(ACCOUNTS_FILE, accounts)

    status_msg = None
    if resume_index > 0:
        # تفعيل استئناف المعاملة
        try:
            status_msg = await context.bot.send_message(
                chat_id=chat_id, 
                text="⏳ جاري استئناف المعاملة وحسابات المساعدة المتبقية تلقائياً...",
                reply_to_message_id=reply_to_message_id
            )
        except Exception:
            pass

    if not status_msg:
        status_msg = await context.bot.send_message(
            chat_id=chat_id, 
            text="⏳ جاري العمل الآن...",
            reply_to_message_id=reply_to_message_id
        )
    
    invite_short_code = link.split('/')[-1]
    if "?" in invite_short_code:
        invite_short_code = invite_short_code.split('?')[0]

    total_accs = len(accounts)
    if refresh_account_cooldowns(accounts):
        save_data(ACCOUNTS_FILE, accounts)
    
    all_available = get_available_account_indexes(accounts)
    if resume_index > 0:
        available_indexes = [idx for idx in all_available if idx >= resume_index]
    else:
        settings = load_settings()
        last_used = settings.get("last_used_account_index", -1)
        if total_accs > 0:
            start_idx = (last_used + 1) % total_accs
            after_start = [idx for idx in all_available if idx >= start_idx]
            before_start = [idx for idx in all_available if idx < start_idx]
            available_indexes = after_start + before_start
        else:
            available_indexes = []
    if total_accs == 0 or not available_indexes:
        await context.bot.edit_message_text(
            chat_id=chat_id,
            message_id=status_msg.message_id,
            text=(
                "⏸️ <b>لا توجد حسابات متاحة للعمل الآن.</b>\n\n"
                "كل الحسابات المتاحة حالياً وصلت للحد <code>5/5</code> أو في فترة راحة 24 ساعة، لذلك تم إيقاف الطلب بدل تركه على رسالة جاري العمل.\n"
                "سيتم فك الحسابات تلقائياً عند انتهاء وقت الراحة الخاص بكل حساب."
            ),
            parse_mode='HTML'
        )
        clear_bot_progress()
        await refund_if_needed("لا توجد حسابات متاحة حالياً لتنفيذ المساعدة")
        return
    
    captured_id = await capture_help_id_from_link(link)
    
    if not captured_id:
        await context.bot.edit_message_text(
            chat_id=chat_id, 
            message_id=status_msg.message_id, 
            text="❌ فشل استخراج بيانات الرابط! يرجى التأكد أن الرابط المبعوث فعال وصالح لجمع المساعدات."
        )
        clear_bot_progress()
        await refund_if_needed("فشل استخراج بيانات الرابط")
        return

    await context.bot.edit_message_text(
        chat_id=chat_id, 
        message_id=status_msg.message_id, 
        text="📡🚀 جاري تشغيل الدوران التلقائي..."
    )

    success_count = resume_success
    fail_count = resume_fail
    start_time = resume_start_time if resume_start_time is not None else asyncio.get_running_loop().time()
    start_index = resume_index
    skipped_cooldown_count = 0

    # متغيّرات تتبع التقدم الفعلي للرابط
    link_current = 0
    link_max = 30

    available_accounts_with_indices = [(idx, accounts[idx]) for idx in available_indexes if idx < len(accounts)]

    for list_pos, (orig_idx, orig_acc) in enumerate(available_accounts_with_indices, start=1):
        # نقرأ دائمًا الحسابات المحدثة من الملف لضمان دقة الرصيد والحدود والعدادات بعد الدوران الفعلي
        with open(ACCOUNTS_FILE, 'r', encoding='utf-8') as f:
            accounts = json.load(f)
            
        accounts_modified = False
        if check_and_reset_accounts_quota(accounts):
            accounts_modified = True
        if refresh_account_cooldowns(accounts):
            accounts_modified = True
        if accounts_modified:
            save_data(ACCOUNTS_FILE, accounts)

        # البحث عن الحساب المطابق في الملف المحدث
        match_idx = -1
        for f_idx, fresh_acc in enumerate(accounts):
            if is_same_account(orig_acc, fresh_acc):
                match_idx = f_idx
                break
        
        if match_idx == -1:
            continue
            
        acc = accounts[match_idx]
        help_count = get_account_help_count(acc)
        if help_count >= ACCOUNT_DAILY_LIMIT or is_account_in_cooldown(acc):
            skipped_cooldown_count += 1
            continue

        # حفظ التقدم بملف bot_progress.json لضمان الاستئناف في حال الإغلاق غير المتوقع
        save_bot_progress(
            chat_id, link, invite_short_code, captured_id, 
            status_msg.message_id, match_idx, success_count, fail_count, start_time, user_name
        )

        # التحقق من ليميت الحساب محلياً (٥ من ٥)
        try:
                # حفظ مؤشر الحساب الأخير الذي تم الوصول إليه
                settings = load_settings()
                settings["last_used_account_index"] = match_idx
                save_data(SETTINGS_FILE, settings)

                result, current, max_val = await asyncio.to_thread(
                    execute_account_api, acc, captured_id, invite_short_code
                )
                
                if max_val and max_val > 0:
                    link_max = max_val
                link_current = current + (1 if result == "SUCCESS" else 0)
                
                if result == "STOP_ALL":
                    elapsed = int(asyncio.get_running_loop().time() - start_time)
                    await context.bot.send_message(
                        chat_id=chat_id, 
                        text=f"🛑 <b>تم إيقاف المعالجة لأن الحد الأقصى للمساعدات قد اكتمل للرابط! ({current}/{max_val})</b>\n\n⏱️ الوقت المستغرق: `{elapsed}` ثانية.",
                        parse_mode='HTML',
                        reply_to_message_id=reply_to_message_id
                    )
                    try:
                        await context.bot.delete_message(chat_id=chat_id, message_id=status_msg.message_id)
                    except Exception:
                        pass
                    clear_bot_progress()
                    if success_count <= resume_success:
                        await refund_if_needed("الرابط مكتمل أو لم يقبل مساعدات جديدة")
                    return
                elif result == "ACCOUNT_LIMIT":
                    acc["helpCountToday"] = ACCOUNT_DAILY_LIMIT
                    acc["lastHelpQuotaDay"] = get_egypt_quota_day()
                    put_account_to_cooldown(acc)
                    if "help_count_today" in acc:
                        acc["help_count_today"] = acc["helpCountToday"]
                    if "last_help_quota_day" in acc:
                        acc["last_help_quota_day"] = acc["lastHelpQuotaDay"]
                    accounts[match_idx] = acc
                    save_data(ACCOUNTS_FILE, accounts)
                    skipped_cooldown_count += 1
                elif result == "SKIP":
                    fail_count += 1
                elif result == "LOGIN_FAILED":
                    fail_count += 1
                    # حذف الحساب التالف من ملف الحسابات
                    with open(ACCOUNTS_FILE, 'r', encoding='utf-8') as f:
                        fresh_accounts = json.load(f)
                    
                    match_idx_fresh = -1
                    for f_idx, fresh_acc in enumerate(fresh_accounts):
                        if is_same_account(acc, fresh_acc):
                            match_idx_fresh = f_idx
                            break
                    
                    if match_idx_fresh != -1:
                        fresh_accounts.pop(match_idx_fresh)
                        save_data(ACCOUNTS_FILE, fresh_accounts)
                        print(f"🗑️ [حذف حساب]: تم حذف الحساب التالف (فشل تسجيل الدخول) بنجاح.")
                elif result == "SUCCESS":
                    success_count += 1
                    
                    # تدوين كوتا المساعدة اليومية للحساب المعني وحفظه للملف
                    acc["helpCountToday"] = get_account_help_count(acc) + 1
                    acc["lastHelpQuotaDay"] = get_egypt_quota_day()
                    if acc["helpCountToday"] >= ACCOUNT_DAILY_LIMIT:
                        put_account_to_cooldown(acc)
                    if "help_count_today" in acc:
                        acc["help_count_today"] = acc["helpCountToday"]
                    if "last_help_quota_day" in acc:
                        acc["last_help_quota_day"] = acc["lastHelpQuotaDay"]

                    # تحديث مستودع حسابات accounts.json وحفظه
                    with open(ACCOUNTS_FILE, 'r', encoding='utf-8') as f:
                        fresh_accounts = json.load(f)
                    
                    # 1. أولاً نقوم بفحص الحساب في نفس الترتيب الحالي (الاحتمالية الأعلى بنسبة 99%)
                    match_idx_fresh = -1
                    if match_idx < len(fresh_accounts):
                        cand = fresh_accounts[match_idx]
                        cand_id = cand.get("id")
                        acc_id = acc.get("id")
                        if cand_id and acc_id and str(cand_id) == str(acc_id):
                            match_idx_fresh = match_idx
                        elif not cand_id and not acc_id:
                            cand_user = cand.get("userId") or cand.get("user_id")
                            acc_user = acc.get("userId") or acc.get("user_id")
                            if cand_user and acc_user and str(cand_user) == str(acc_user):
                                match_idx_fresh = match_idx
                            elif not cand_user and not acc_user:
                                match_idx_fresh = match_idx

                    # 2. إذا لم نعثر على مطابقة في نفس المؤشر، نبحث بشكل خطي في القائمة بحثاً دقيقاً
                    if match_idx_fresh == -1:
                        for f_idx, fresh_acc in enumerate(fresh_accounts):
                            if is_same_account(acc, fresh_acc):
                                match_idx_fresh = f_idx
                                break
                    
                    # 3. وإذا تعذر تماماً، نستخدم الترتيب كخيار أخير كلياً
                    if match_idx_fresh == -1 and match_idx < len(fresh_accounts):
                        match_idx_fresh = match_idx
                        
                    if match_idx_fresh != -1:
                        fresh_accounts[match_idx_fresh]["helpCountToday"] = acc["helpCountToday"]
                        fresh_accounts[match_idx_fresh]["lastHelpQuotaDay"] = acc["lastHelpQuotaDay"]
                        fresh_accounts[match_idx_fresh]["cooldown_until"] = acc.get("cooldown_until")
                        if "help_count_today" in fresh_accounts[match_idx_fresh]:
                            fresh_accounts[match_idx_fresh]["help_count_today"] = acc["helpCountToday"]
                        if "last_help_quota_day" in fresh_accounts[match_idx_fresh]:
                            fresh_accounts[match_idx_fresh]["last_help_quota_day"] = acc["lastHelpQuotaDay"]
                            
                    save_data(ACCOUNTS_FILE, fresh_accounts)
                else:
                    fail_count += 1
                    
        except Exception as e:
            print(f"Error executing help inside loop: {e}")
            fail_count += 1

        if list_pos % 4 == 0 or list_pos == len(available_indexes):
            elapsed = int(asyncio.get_running_loop().time() - start_time)
            
            # احتساب النسبة المئوية على التقدم الفعلي للرابط (الوصول لـ 30 مساعدة) بدلاً من عدد حساباتنا
            progress_ratio = min(link_current, link_max) / link_max
            percent = int(progress_ratio * 100)
            filled_blocks = int(progress_ratio * 10)
            progress_bar = "🟩" * filled_blocks + "⬛" * (10 - filled_blocks)
            
            new_report = f"""
⚡ <b>جاري إرسال المساعدات التلقائية الآن...</b>

⚙️ التقدم الفعلي للرابط: `{link_current}/{link_max}` ({percent}%)
[{progress_bar}]

⏱️ الوقت المنقضي: `{elapsed}` ثانية
🟢 مساعدات ناجحة جديدة: `{success_count}`
🔴 لم تكتمل (بسبب ليميت مسبق): `{fail_count}`


👤 العميل: {user_name}
"""
            try:
                await context.bot.edit_message_text(
                    chat_id=chat_id, 
                    message_id=status_msg.message_id, 
                    text=new_report,
                    parse_mode='HTML'
                )
            except Exception:
                pass
        
        await asyncio.sleep(0.4)

    elapsed_total = int(asyncio.get_running_loop().time() - start_time)
    completed_bar = "🟩" * 10
    operation_success = success_count > resume_success
    final_title = "🏁 <b>اكتملت العملية بالكامل بنجاح! 🎉</b>" if operation_success else "⚠️ <b>انتهت المحاولة بدون تنفيذ أي مساعدة.</b>"
    final_hint = "📱 تفضل بفحص حسابك باللعبة الآن!" if operation_success else "↩️ سيتم إرجاع الرصيد المخصوم تلقائياً."
    final_report = f"""
{final_title}

[{completed_bar}] 100%

⏱️ الوقت الكلي المستغرق: `{elapsed_total}` ثانية
🟢 مساعدات ناجحة كلية: `{success_count}`
🔴 لم تكتمل (بسبب ليميت مسبق): `{fail_count}` (قد تكون مدعومة مسبقاً من أصدقاء آخرين)

👤 المستلم: <b>{user_name}</b>
{final_hint}
"""
    await context.bot.send_message(chat_id=chat_id, text=final_report, parse_mode='HTML', reply_to_message_id=reply_to_message_id)
    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=status_msg.message_id)
    except Exception:
        pass
    clear_bot_progress()
    if success_count <= resume_success:
        await refund_if_needed("لم تكتمل أي مساعدة من الحسابات المتاحة")


# --- دالات ومساعد محاكاة سياق البوت لإتمام الاستئناف بسلاسة ---
class ResumedContext:
    def __init__(self, bot):
        self.bot = bot

async def resume_pending_tasks(application):
    """التحقق التلقائي واستئناف المساعدات المتوقفة عند إعادة إقلاع البوت"""
    if not BOT_PROGRESS_FILE.exists():
        return
    try:
        with open(BOT_PROGRESS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if data.get("status") == "running":
            chat_id = data["chat_id"]
            link = data.get("link")
            start_index = data.get("current_index", 0)
            success_count = data.get("success_count", 0)
            fail_count = data.get("fail_count", 0)
            start_time = data.get("start_time", None)
            user_name = data.get("user_name", "المستفيد")
            
            print(f"⏳ Found interrupted task. Resuming link {link} from index {start_index}...")
            
            try:
                await application.bot.send_message(
                    chat_id=chat_id,
                    text=f"🔄 <b>تم العثور على معاملة غير مكتملة بسبب إعادة تشغيل السيرفر!</b>\n⚙️ جاري استئناف إرسال المساعدات للرابط تلقائياً بدءاً من الحساب رقم `{start_index + 1}`",
                    parse_mode='HTML'
                )
            except Exception as e:
                print(f"Failed to send resume notification: {e}")

            context_wrapper = ResumedContext(application.bot)
            asyncio.create_task(process_bot_link_engine(
                link=link,
                chat_id=chat_id,
                context=context_wrapper,
                user_name=user_name,
                user_handle="",
                is_group=False,
                reply_to_message_id=None,
                resume_index=start_index,
                resume_success=success_count,
                resume_fail=fail_count,
                resume_start_time=start_time
            ))
    except Exception as e:
        print(f"Error resuming pending links task: {e}")


# --- منطق ومعالجات تليجرام الفاخرة ---
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    register_user_details(update.effective_user)
    if is_banned(user_id):
        await update.message.reply_text("🚫 عذراً، حسابك محظور من استخدام هذا البوت.")
        return

    # لا نعالج الكيبورد الرئيسي أو رسائل الترحيب الكبيرة في المجموعات لمراعاتها
    if update.effective_chat.type in ['group', 'supergroup']:
        return

    # معالجة نظام الدعوة من البداية
    args = context.args
    if args and args[0].startswith("ref_"):
        inviter_id = args[0].replace("ref_", "")
        balances = load_data(BALANCE_FILE, {})
        
        if str(user_id) in balances:
            # مسجل مسبقاً، تخطي
            pass
        elif str(user_id) == str(inviter_id):
            await update.message.reply_text("⚠️ لا يمكنك دعوة نفسك!")
            pass
        else:
            # توليد مسألة رياضية عشوائية للأمان ضد البوتات
            num1 = random.randint(1, 20)
            num2 = random.randint(1, 10)
            op = random.choice(['+', '-'])
            if op == '+':
                ans = num1 + num2
            else:
                if num1 < num2:
                    num1, num2 = num2, num1
                ans = num1 - num2
                
            context.user_data['pending_ref'] = inviter_id
            context.user_data['math_ans'] = ans
            
            await update.message.reply_text(
                f"👋 أهلاً بك! لمنع الدعوات الوهمية وضمان الأمان، يرجى كتابة ناتج المسألة الرياضية التالية لتسجيل دعوتك بالبوت:\n\n"
                f"<b>{num1} {op} {num2} = ?</b>",
                parse_mode='HTML'
            )
            return

    # التحقق المسبق من قيود الاشتراك والمسائل الحسابية المفتوحة
    if not await handle_user_prechecks(update, context, user_id):
        return

    if args and args[0].lower() in ["buy", "purchase", "charge"]:
        return await ask_quantity(update, context)

    # تهيئة رصيد العضو القديم أو الجديد بالملف لضمان عدم وجود مستخدمين مجهولي الأرصدة
    balances = load_data(BALANCE_FILE, {})
    if str(user_id) not in balances:
        balances[str(user_id)] = 0
        save_data(BALANCE_FILE, balances)

    keyboard = [
        ["🟢 إرسال رابط ⬇️", "💳 رصيدي 💳"],
        ["🛒 شراء رصيد 💳", "🔑 كود تفعيل 🔑"],
        ["📖 المساعدة 📖", "👥 رابط الدعوة 👥"]
    ]
    if user_id in ADMIN_IDS:
        keyboard.append(["⚙️ لوحة التحكم ⚙️"])
        
    await update.message.reply_text(
        "👋 أهلاً بك في بوت تقفيل ليميت عجلة Midasbuy\n\n"
        "📖 <b>دليل تشغيل البوت للمبتدئين:</b>\n\n"
        "1️⃣ قم بفحص الرصيد المسجل بحسابك عبر تبويب '💳 رصيدي'.\n"
        "2️⃣  لشراء الرصيد وتجربة الدوران الفوري؛ تفضل بالدخول على '🛒 شراء رصيد' وحدد باقتك ثم قم بالدفع لـ فودافون كاش وإدخل هاتفك المحول بوضوح او تواصل مع احد المشرفين @TowmasWageeh.\n"
        "3️⃣ بعد الحصول على تأكيد ورصيد، اضغط على '🟢 إرسال رابط' وأرسل رسالة المشاركة الخاصة بك من اللعبة مباشرة.\n"
        "4️⃣ سيقوم البوت بتدوير العجلة لـ 30 حساباً تلقائياً مع توضيح نسبة الإنجاز والوقت المنقضي بدقة!\n\n"
        "اختر من القائمة في الأسفل لبدء الخدمة بلمسة سحرية:",
        reply_markup=ReplyKeyboardMarkup(keyboard, resize_keyboard=True),
        parse_mode='HTML'
    )

# دالة معالجة الإجابات الرياضية
async def check_math_answer(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if is_banned(user_id): return
    
    if 'math_ans' in context.user_data:
        try:
            user_ans = int(update.message.text.strip())
            correct_ans = context.user_data['math_ans']
            
            if user_ans == correct_ans:
                inviter_id = context.user_data.get('pending_ref')
                referrals = load_data(REFERRALS_FILE, {})
                
                if str(inviter_id) not in referrals:
                    referrals[str(inviter_id)] = {"referred_users": [], "claimed_codes_count": 0}
                    
                if str(user_id) not in referrals[str(inviter_id)]["referred_users"]:
                    referrals[str(inviter_id)]["referred_users"].append(str(user_id))
                    
                    # تسجيل العضو الجديد بجداول الأرصدة فوراً لمنع التكرار
                    balances = load_data(BALANCE_FILE, {})
                    balances[str(user_id)] = balances.get(str(user_id), 0)
                    save_data(BALANCE_FILE, balances)
                    
                    await update.message.reply_text("✅ أحسنت! إجابة صحيحة بالكامل. تم التحقق من هويتك وتفعيل الحساب كلياً.")
                    
                    # مكافأة صاحب الدعوة برصيد تلقائي (لكل 5 دعوات ناجحة)
                    inviter_data = referrals[str(inviter_id)]
                    ref_count = len(inviter_data["referred_users"])
                    claimed = inviter_data.get("claimed_codes_count", 0)
                    eligible = ref_count // 5
                    
                    if eligible > claimed:
                        inviter_data["claimed_codes_count"] = claimed + 1
                        
                        # إضافة نقطة إلى رصيد الداعي مباشرة
                        inviter_balances = load_data(BALANCE_FILE, {})
                        inviter_balances[str(inviter_id)] = inviter_balances.get(str(inviter_id), 0) + 1
                        save_data(BALANCE_FILE, inviter_balances)
                        
                        try:
                            await context.bot.send_message(
                                chat_id=int(inviter_id),
                                text=f"🎉 <b>تهانينا الحارة! لقد نجحت في دعوة 5 مستخدمين جدد حقيقيين للبوت!</b>\n\n"
                                     f"🎁 تم إضافة نقطة كاملة لرصيدك تلقائياً.\n"
                                     f"💰 رصيدك الحالي الآن: <code>{inviter_balances[str(inviter_id)]}</code> نقاط.",
                                parse_mode='HTML'
                            )
                        except Exception:
                            pass
                            
                    save_data(REFERRALS_FILE, referrals)
                    
                context.user_data.pop('math_ans', None)
                context.user_data.pop('pending_ref', None)
                
                # توجيه المستخدم لحساب الصفحة الرئيسية
                await start(update, context)
                
            else:
                # توليد مسألة جديدة في حال الخطأ تفادياً للهجمات التخمينية
                num1 = random.randint(1, 10)
                num2 = random.randint(1, 10)
                op = random.choice(['+', '-'])
                if op == '+':
                    ans = num1 + num2
                else:
                    if num1 < num2:
                        num1, num2 = num2, num1
                    ans = num1 - num2
                    
                context.user_data['math_ans'] = ans
                await update.message.reply_text(
                    f"❌ <b>إجابة خاطئة! لمنع البوتات يرجى إعادة المحاولة مع هذه المسألة الجديدة:</b>\n\n"
                    f"<b>{num1} {op} {num2} = ?</b>",
                    parse_mode='HTML'
                )
        except ValueError:
            await update.message.reply_text("⚠️ يرجى إدخال أرقام صحيحة وصالحة فقط (مثال: 8):")
        return

# عرض واجهة وبيانات الدعوات للمستخدم
async def referral_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.effective_user.id)
    if not await handle_user_prechecks(update, context, int(user_id)):
        return
        
    bot_info = await context.bot.get_me()
    bot_username = bot_info.username
    ref_link = f"https://t.me/{bot_username}?start=ref_{user_id}"
    
    referrals = load_data(REFERRALS_FILE, {})
    user_ref_data = referrals.get(user_id, {"referred_users": [], "claimed_codes_count": 0})
    ref_count = len(user_ref_data["referred_users"])
    claimed = user_ref_data.get("claimed_codes_count", 0)
    
    next_goal = 5 - (ref_count % 5)
    
    msg = (
        f"<b>👥 نظام الدعوات البريميوم:</b>\n\n"
        f"قم بدعوة أصدقائك للحصول على نقاط مجانية تضاف لرصيدك تلقائياً!\n"
        f"🎁 <u>كل 5 دعوات مستخدمين حقيقيين تمنحك (1) نقطة مباشرة في رصيدك</u>.\n\n"
        f"🔗 <b>رابط الدعوة الحصري الخاص بك (اضغط للنسخ):</b>\n"
        f"<code>{ref_link}</code>\n\n"
        f"📊 <b>تفاصيل أمان الدعوات والمكافآت:</b>\n"
        f"👥 إجمالي دعوتك المقبولة: <code>{ref_count} عضو حقيقي</code>\n"
        f"🎟️ نقاط تم ربحها وإضافتها لرصيدك: <code>{claimed} نقطة</code>\n"
        f"⏳ متبقي لدعوتك التالية للحصول على النقطة القادمة: <code>{next_goal} أعضاء</code>"
    )
    await update.message.reply_text(msg, parse_mode='HTML')

async def check_balance(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.effective_user.id)
    register_user_details(update.effective_user)
    if not await handle_user_prechecks(update, context, int(user_id)):
        return
    balances = load_data(BALANCE_FILE, {})
    await update.message.reply_text(f"💳 رصيدك الحالي النشطة للخدمة: {balances.get(user_id, 0)} رابط مساعدة.")

async def ask_for_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.effective_user.id)
    if not await handle_user_prechecks(update, context, int(user_id)):
        return ConversationHandler.END
        
    settings = load_settings()
    open_mode = settings.get("open_mode", False)
    balances = load_data(BALANCE_FILE, {})
    if not open_mode and balances.get(user_id, 0) <= 0:
        await update.message.reply_text("⛔ رصيدك منتهي (0)! يرجى التوجه لشراء رصيد أولاً لتفعيل روابطك.")
        return ConversationHandler.END
        
    open_mode_note = "🔓 <b>الوضع المفتوح مفعل حالياً: التشغيل مجاني بدون خصم رصيد.</b>\n\n" if open_mode else ""
    await update.message.reply_text(
        "<b>🔗 تفضل بإرسال رابط المساعدات الترويجي الخاص بك الآن:\n\n</b>"
        f"{open_mode_note}"
        "<b>يمكنك إرسال رسالة المشاركة كاملة كما هي وسأستخلص الرابط منها ذكياً.\nاكتب /cancel للإلغاء.</b>", 
        parse_mode='HTML'
    )
    return LINK_WAITING

async def process_link_and_run(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.effective_user.id)
    register_user_details(update.effective_user)
    
    if not await handle_user_prechecks(update, context, int(user_id)):
        return ConversationHandler.END
        
    settings = load_settings()
    open_mode = settings.get("open_mode", False)
    balances = load_data(BALANCE_FILE, {})
    if not open_mode and balances.get(user_id, 0) <= 0:
        await update.message.reply_text("⛔ عذراً! رصيدك غير كافٍ. يرجى الشحن أولاً لتشغيل الخدمة.")
        return ConversationHandler.END
        
    raw_text = update.message.text
    link = extract_clean_url(raw_text)
    
    if not link:
        await update.message.reply_text(
            "<b>⚠️ خطأ في الرابط المكتوب!</b>\n"
            "يرجى إرسال رسالة المشاركة التي تحتوي على رابط Midasbuy واضح ومباشر تماشياً مع العجلة المفتوحة بالكامل باللعبة.",
            parse_mode='HTML'
        )
        return LINK_WAITING
        
    charged_user_id = None
    refund_on_failure = False
    if not open_mode:
        # خصم نقطة واحدة من رصيد العضو النشط
        balances[user_id] = balances[user_id] - 1
        save_data(BALANCE_FILE, balances)
        charged_user_id = user_id
        refund_on_failure = True
    
    user_name = update.effective_user.first_name
    user_handle = update.effective_user.username or ""
    
    # إرسال العملية إلى المحرك غير الحاصر في الخلفية
    asyncio.create_task(process_bot_link_engine(
        link=link,
        chat_id=update.effective_chat.id,
        context=context,
        user_name=user_name,
        user_handle=user_handle,
        is_group=False,
        reply_to_message_id=update.message.message_id,
        charged_user_id=charged_user_id,
        refund_on_failure=refund_on_failure
    ))
    return ConversationHandler.END

# تفعيل كود شحن يدوي
async def ask_for_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.effective_user.id)
    if not await handle_user_prechecks(update, context, int(user_id)):
        return ConversationHandler.END
    await update.message.reply_text("🔑 تفضل بإدخال كود الشحن الذي حصلت عليه لتفعيل النقاط فوراً:")
    return CODE_WAITING

async def process_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.effective_user.id)
    register_user_details(update.effective_user)
    if not await handle_user_prechecks(update, context, int(user_id)):
        return ConversationHandler.END
        
    code = update.message.text.strip().upper()
    vouchers = load_data(VOUCHERS_FILE, {})
    
    if code in vouchers and vouchers[code].get("status") == "active":
        vouchers[code]["status"] = "used"
        points = vouchers[code].get("points", 1)  # القيمة الافتراضية 1 نقطة للأكواد القديمة
        save_data(VOUCHERS_FILE, vouchers)
        
        balances = load_data(BALANCE_FILE, {})
        balances[user_id] = balances.get(user_id, 0) + points
        save_data(BALANCE_FILE, balances)
        
        await update.message.reply_text(f"✅ تم تفعيل كود الشحن بنجاح! تم إضافة `{points}` نقاط لرصيدك. رصيدك الحالي الآن: `{balances[user_id]}` روابط.", parse_mode='Markdown')
    else:
        await update.message.reply_text("❌ الكود المدخل غير صحيح، أو تم شحنه واستخدامه مسبقاً.")
        
    return ConversationHandler.END

# --- قسم الشراء والدعم كاش بنظام حماية الهاتف الصارم ---
async def ask_quantity(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.effective_user.id)
    if not await handle_user_prechecks(update, context, int(user_id)):
        return ConversationHandler.END
    settings = load_settings()
    offers = get_purchase_offers(settings)
    keyboard = []
    for i in range(0, len(offers), 2):
        keyboard.append([build_offer_button_text(offer) for offer in offers[i:i + 2]])
    keyboard.append(["✍️ ادخل عدد اللينكات يدوياً"])

    msg = "🛒 اختر عرض الشحن المناسب لك:\n\nاكتب /cancel لإلغاء عملية الشراء."
    if not offers:
        msg = "🛒 لا توجد عروض جاهزة حالياً. يمكنك إدخال عدد اللينكات يدوياً:\n\nاكتب /cancel لإلغاء عملية الشراء."

    await update.message.reply_text(
        msg,
        reply_markup=ReplyKeyboardMarkup(keyboard, resize_keyboard=True, one_time_keyboard=True)
    )
    return SELECT_QUANTITY

async def process_quantity(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        settings = load_settings()
        price = settings.get("price", 15)
        wallet = settings.get("wallet", "01036428989")
        text = update.message.text.strip()
        
        selected_offer = None
        manual_buttons = ["✍️ ادخل عدد اللينكات يدوياً", "✍️ إدخال عدد اللينكات يدوياً"]
        if text not in manual_buttons:
            for offer in get_purchase_offers(settings):
                if text == build_offer_button_text(offer):
                    selected_offer = offer
                    break
        else:
            await update.message.reply_text("✍️ اكتب عدد اللينكات المطلوب شراؤها بالأرقام فقط:")
            return SELECT_QUANTITY

        if selected_offer:
            qty = selected_offer["qty"]
            total_price = selected_offer["price"]
            package_label = selected_offer["label"]
        else:
            qty = int(text)
            if qty <= 0:
                raise ValueError("Quantity must be positive")
            total_price = qty * price
            package_label = f"{qty} لينك"
        
        context.user_data['qty'] = qty
        context.user_data['total'] = total_price
        context.user_data['package_label'] = package_label
        
        await update.message.reply_text(
            f"📥 <b>إيصال تفاصيل باقة الشراء المالي:</b>\n"
            f"📦 الباقة المطلوبة: <code>{package_label}</code>\n"
            f"📦 كمية الروابط المطلوبة: <code>{qty}</code>\n"
            f"💰 الإجمالي المستحق للدفع: ` {total_price} جنيه مصري `\n\n"
            f"📱 يرجى تحويل المبلغ بدقة لمحفظة الكاش التالية:\n"
            f"👉 <code>{wallet}</code> 👈 (اضغط للنسخ)\n\n"
            f"📸 بعد التحويل، أرسل <b>رقم الهاتف الذي حولت منه كاش</b> (مكون من 11 رقم للتحقق والقبول التلقائي):", 
            parse_mode='HTML'
        )
        return SEND_PAYMENT_INFO
    except Exception:
        await update.message.reply_text("❌ اختر عرضاً من الأزرار أو أرسل رقم دقيق فقط ككمية روابط للمتابعة.")
        return SELECT_QUANTITY

async def finish_purchase(update: Update, context: ContextTypes.DEFAULT_TYPE):
    sender_number = update.message.text.strip()
    
    if not re.match(r'^01[0125][0-9]{8}$', sender_number):
        await update.message.reply_text(
            "⚠️ <b>خطأ في رقم المرسل!</b>\n"
            "يجب أن يكون رقم الهاتف مكوناً من 11 رقم مصري ويبدأ بـ (010, 011, 012, 015)\n"
            "مثال: <code>01210587916</code>\n\n"
            "تفضل بإعادة كتابة الرقم بالشكل الصحيح الآن:",
            parse_mode='HTML'
        )
        return SEND_PAYMENT_INFO

    qty = context.user_data['qty']
    total = context.user_data['total']
    package_label = context.user_data.get('package_label', f"{qty} لينك")
    user = update.effective_user
    
    # Check for unclaimed transaction match (Scenario B: payment came first)
    unclaimed = load_data(UNCLAIMED_TX_FILE, {})
    matched_tx_id = None
    for tx_id, tx_info in unclaimed.items():
        if tx_info.get("phone") == sender_number and abs(float(tx_info.get("amount", 0)) - float(total)) < 0.01:
            matched_tx_id = tx_id
            break

    if matched_tx_id:
        confirm_msg = await auto_confirm_order(
            uid=user.id,
            qty=qty,
            total=total,
            sender_number=sender_number,
            tx_id=matched_tx_id,
            context=context
        )
        
        settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
        group_id = settings.get("group_id")
        if group_id:
            try:
                await context.bot.send_message(
                    chat_id=group_id,
                    text=confirm_msg,
                    parse_mode='HTML'
                )
            except Exception:
                pass
                
        await update.message.reply_text("✅ <b>تم التحقق وتأكيد الدفع أوتوماتيكياً بنجاح وشحن رصيدك فوراً!</b>", parse_mode='HTML')
        return ConversationHandler.END
    
    user_info = (
        f"👤 الاسم: {user.full_name}\n"
        f"🔗 المعرف لليوزر: @{user.username or 'لا يوجد'}\n"
        f"🆔 الآيدي الرقمي (ID): <code>{user.id}</code>"
    )
    
    order_text = (
        f"<b>🔔 طلب شحن رصيد جديد قيد المطابقة!</b>\n\n"
        f"{user_info}\n\n"
        f"🎁 الباقة المختارة: <code>{package_label}</code>\n"
        f"📦 الكمية المطلوبة: <code>{qty} روابط مخصصة</code>\n"
        f"💵 قيمة الإيداع: <code>{total} جنيه مصري</code>\n"
        f"📱 محوّل من رقم: <code>{sender_number}</code>"
    )
    
    keyboard = [
        [
            InlineKeyboardButton("🟢 قبول وإرسال الشحنة ✅", callback_data=f"accept_{user.id}_{qty}"),
            InlineKeyboardButton("🔴 رفض وإلغاء الطلب ❌", callback_data=f"reject_{user.id}")
        ]
    ]
    
    pending_orders = load_data(PENDING_REQ_FILE, {})
    pending_orders[str(user.id)] = {
        "user_info": user_info,
        "package_label": package_label,
        "qty": qty,
        "total": total,
        "sender_number": sender_number,
        "messages": []
    }
    
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    group_id = settings.get("group_id")
    sent_any = False
    
    if group_id:
        try:
            msg = await context.bot.send_message(
                chat_id=group_id, text=order_text, parse_mode='HTML', reply_markup=InlineKeyboardMarkup(keyboard)
            )
            pending_orders[str(user.id)]["messages"].append({"chat_id": group_id, "msg_id": msg.message_id})
            sent_any = True
        except Exception as e:
            print(f"Error sending payment request to group: {e}")
            pass
            
    if not sent_any:
        for admin_id in ADMIN_IDS:
            try:
                msg = await context.bot.send_message(
                    chat_id=admin_id, text=order_text, parse_mode='HTML', reply_markup=InlineKeyboardMarkup(keyboard)
                )
                pending_orders[str(user.id)]["messages"].append({"chat_id": admin_id, "msg_id": msg.message_id})
            except Exception:
                pass
                
    save_data(PENDING_REQ_FILE, pending_orders)
    await update.message.reply_text("✅ <b>تم إرسال طلب الشحن بنجاح! المشرفون يطابقون العمليات حالياً لشحن رصيدك فوراً.</b>", parse_mode='HTML')
    return ConversationHandler.END

# معالجة قبول أو رفض طلبات الدفع
async def admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    clicker_id = update.effective_user.id
    data = query.data.split('_')
    action = data[0]
    
    if action == "check":
        unsubscribed = await check_channel_subscription(clicker_id, context)
        if not unsubscribed:
            bonus_granted, new_balance = grant_free_join_bonus_once(clicker_id)
            if bonus_granted:
                await query.answer("✅ تم التحقق والاشتراك بنجاح! تم إضافة 1 نقطة مجانية لرصيدك 🎁", show_alert=True)
            else:
                await query.answer("✅ تم التحقق والاشتراك بنجاح! مرحباً بك.", show_alert=True)
            try:
                await query.message.delete()
            except Exception:
                pass
            
            balances = load_data(BALANCE_FILE, {})
            if str(clicker_id) not in balances:
                balances[str(clicker_id)] = 0
                save_data(BALANCE_FILE, balances)

            keyboard = [
                ["🟢 إرسال رابط ⬇️", "💳 رصيدي 💳"],
                ["🛒 شراء رصيد 💳", "🔑 كود تفعيل 🔑"],
                ["📖 المساعدة 📖", "👥 رابط الدعوة 👥"]
            ]
            if clicker_id in ADMIN_IDS:
                keyboard.append(["⚙️ لوحة التحكم ⚙️"])
            await context.bot.send_message(
                chat_id=query.message.chat_id, 
                text=(
                    f"🎁 تم إضافة 1 نقطة مجانية لرصيدك لأول اشتراك ناجح.\nرصيدك الحالي: <code>{new_balance}</code> رابط.\n\n"
                    "مرحباً بك مجدداً! كيف يمكنني مساعدتك اليوم؟"
                ) if bonus_granted else "مرحباً بك مجدداً! كيف يمكنني مساعدتك اليوم؟",
                parse_mode='HTML' if bonus_granted else None,
                reply_markup=ReplyKeyboardMarkup(keyboard, resize_keyboard=True)
            )
        else:
            await query.answer("❌ لم تشترك في جميع القنوات بعد! يرجى الاشتراك ثم الضغط على الزر مجدداً.", show_alert=True)
        return

    if clicker_id not in ADMIN_IDS:
        await query.answer("❌ عذراً! هذا الإجراء مخصص لمدراء البوت المعتمدين فقط.", show_alert=True)
        return
        
    await query.answer()
    uid = str(data[1])

    pending_orders = load_data(PENDING_REQ_FILE, {})
    if uid not in pending_orders:
        await query.message.reply_text("⚠️ هذا الطلب تمت معالجته مسبقاً أو تم حذفه من الذاكرة!")
        return
        
    order = pending_orders[uid]
    qty = order["qty"]
    user_info = order["user_info"]
    
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    delivery_method = settings.get("delivery_method", "direct")
    
    if action == "accept":
        if delivery_method == "direct":
            balances = load_data(BALANCE_FILE, {})
            balances[uid] = balances.get(uid, 0) + qty
            save_data(BALANCE_FILE, balances)
            
            new_text = (
                f"<b>✅ تم تأكيد إيداع الدفع وصدم الشحنة بنجاح!</b>\n"
                f"بواسطة المشرف المعتمد: {update.effective_user.first_name}\n"
                f"📦 تمت إضافة: <code>{qty} روابط حصرية</code> لمحفظته مباشرة.\n\n"
                f"👤 تفاصيل العضو:\n{user_info}"
            )
            try:
                await context.bot.send_message(
                    chat_id=int(uid), 
                    text=f"🎉 <b>رائع! لقد تم التحقق من معاملتك المالية وإضافة {qty} رابط (نقاط) إلى حسابك بنجاح!</b>", 
                    parse_mode='HTML'
                )
            except Exception:
                pass
        else:
            generated_codes = []
            vouchers = load_data(VOUCHERS_FILE, {})
            for _ in range(qty):
                code = "LK-BUY-" + ''.join(secrets.choice(string.ascii_uppercase + string.digits) for _ in range(12))
                vouchers[code] = {"status": "active"}
                generated_codes.append(code)
            save_data(VOUCHERS_FILE, vouchers)
            
            codes_formatted = "\n".join([f"<code>{c}</code>" for c in generated_codes])
            new_text = (
                f"<b>✅ تم تأكيد عملية الدفع وتوليد أكواد الشحن بنجاح!</b>\n"
                f"بواسطة المشرف: {update.effective_user.first_name}\n"
                f"🗝️ تم شحنه في صورة أكواد تفعيل مجمّعة.\n\n"
                f"👤 تفاصيل العضو:\n{user_info}"
            )
            try:
                await context.bot.send_message(
                    chat_id=int(uid),
                    text=f"🎉 <b>تم قبول طلب الشراء الخاص بك بنجاح!</b>\n\n"
                         f"🗝️ لقد أرسلت لك الإدارة أكواد تفعيل روابطك:\n\n"
                         f"{codes_formatted}\n\n"
                         f"قم بنسخ الأكواد واستخدامها لشحن حسابك من قسم '🔑 كود تفعيل'.",
                    parse_mode='HTML'
                )
            except Exception:
                pass
    else:
        new_text = (
            f"<b>❌ تم رفض وإبطال طلب الشحن المالي!</b>\n"
            f"بواسطة مدير البوت: {update.effective_user.first_name}\n\n"
            f"👤 تفاصيل العضو:\n{user_info}"
        )
        try:
            await context.bot.send_message(
                chat_id=int(uid), 
                text="⚠️ <b>عذراً! تم إلغاء طلبك لعدم مطابقة بيانات إيداع كاش، تواصل مع فريق المبيعات.</b>", 
                parse_mode='HTML'
            )
        except Exception:
            pass

    for msg_info in order.get("messages", []):
        try:
            await context.bot.edit_message_text(
                chat_id=msg_info["chat_id"],
                message_id=msg_info["msg_id"],
                text=new_text,
                parse_mode='HTML'
            )
        except Exception:
            pass
            
    if uid in pending_orders:
        del pending_orders[uid]
    save_data(PENDING_REQ_FILE, pending_orders)

# --- لوحة التحكم المتطورة والفاخرة للمشرفين ---
async def admin_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    kb = [
        ["📊 الإحصائيات", "🗝️ توليد كود شحن"],
        ["💰 تغيير السعر", "📱 تغيير المحفظة"],
        ["🚫 حظر مستخدم", "📋 عرض الطلبات المعلقة"],
        ["📢 بث إذاعة عامة", "🔍 قائمة الأكواد"],
        ["👥 تعيين جروب الدفع", "📢 الاشتراك الإجباري"],
        ["🔄 طريقة تسليم الرصيد", "🔍 رصيد مستخدم"],
        ["🎁 عروض الشراء"],
        ["🔓 الوضع المفتوح"],
        ["⏱️ إعلان كل ٣ ساعات", "⏰ وقت البوت الحالي"],
        ["🔙 رجوع للقائمة الرئيسية"]
    ]
    await update.message.reply_text("⚙️ مرحباً بك في كابينة التحكم والإدارة للبوت لشخصك الكريم:", reply_markup=ReplyKeyboardMarkup(kb, resize_keyboard=True))

async def show_bot_time(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    egypt_now = get_egypt_time()
    utc_now = datetime.datetime.utcnow()
    
    egypt_str = egypt_now.strftime("%Y-%m-%d %I:%M:%S %p")
    utc_str = utc_now.strftime("%Y-%m-%d %I:%M:%S %p")
    
    quota_day = get_egypt_quota_day()
    
    # تحميل الحسابات وفحص الحسابات متبقي الدخول المتاح لليوم
    accounts = load_data(ACCOUNTS_FILE, [])
    accounts_modified = False
    if check_and_reset_accounts_quota(accounts):
        accounts_modified = True
    if refresh_account_cooldowns(accounts):
        accounts_modified = True
    if accounts_modified:
        save_data(ACCOUNTS_FILE, accounts)
    
    total_accounts = len(accounts)
    sleeping_accounts = sum(1 for acc in accounts if is_account_in_cooldown(acc))
    available_accounts = len(get_available_account_indexes(accounts))
    total_capacity = total_accounts * ACCOUNT_DAILY_LIMIT
    used_today = sum(get_account_help_count(acc) for acc in accounts)
    remaining_today = sum(max(0, ACCOUNT_DAILY_LIMIT - get_account_help_count(acc)) for acc in accounts if not is_account_in_cooldown(acc))
    
    msg = (
        f"<b>⏰ وقت البوت الحالي والمنطقة الزمنية:</b>\n\n"
        f"🇪🇬 <b>توقيت القاهرة الفعلي (تلقائي/يدوي):</b>\n"
        f"<code>{egypt_str}</code>\n\n"
        f"🌐 <b>توقيت UTC العالمي:</b>\n"
        f"<code>{utc_str}</code>\n\n"
        f"📅 <b>يوم الكوتا المرجعي الحالي للبوت:</b>\n"
        f"<code>{quota_day}</code>\n\n"
        f"📊 <b>حالة حسابات السيستم بنظام راحة 24 ساعة:</b>\n"
        f"👥 إجمالي الحسابات المسجلة: <code>{total_accounts} حساب</code>\n"
        f"🟢 الحسابات المتاحة الآن: <code>{available_accounts} حساب</code>\n"
        f"⏸️ الحسابات في راحة 24 ساعة: <code>{sleeping_accounts} حساب</code>\n"
        f"⚡ المساعدات المستخدمة حالياً: <code>{used_today} من {total_capacity}</code>\n"
        f"🔑 <b>الدخول المتبقي المتاح الآن:</b> <code>{remaining_today} دخول</code>\n\n"
        f"💡 <i>الحساب الذي يصل إلى 5/5 يدخل راحة لمدة 24 ساعة كاملة، ثم يعود تلقائياً بدون ريستارت.</i>"
    )
    await update.message.reply_text(msg, parse_mode='HTML')

async def show_stats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    balances = load_data(BALANCE_FILE, {})
    total_users = len(balances)
    total_balance = sum(balances.values())
    vouchers = load_data(VOUCHERS_FILE, {})
    total_vouchers = len(vouchers)
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    wallet = settings.get("wallet", "01036428989")
    price = settings.get("price", 15)
    delivery_method = settings.get("delivery_method", "direct")
    open_mode = settings.get("open_mode", False)
    
    await update.message.reply_text(
        f"📊 <b>إحصائيات وخزانة البوت والنشاطات:</b>\n\n"
        f"👥 إجمالي الأعضاء النشطين: <code>{total_users} عضو</code>\n"
        f"💳 مجموع الروابط المفعّلة: <code>{total_balance} رابط</code>\n"
        f"🗝️ الأكواد المتوفرة بالمستودع: <code>{total_vouchers} كود شحن</code>\n"
        f"💰 سعر الباقة الحالي: <code>{price} جنيه</code>\n"
        f"🔄 طريقة التسليم: <code>{'إضافة مباشرة' if delivery_method == 'direct' else 'أكواد تفعيل'}</code>\n"
        f"🔓 الوضع المفتوح: <code>{'مفعل - مجاني' if open_mode else 'مغلق - بالرصيد'}</code>\n"
        f"📱 رقم محفظة الكاش المعتمدة: <code>{wallet}</code>", 
        parse_mode='HTML'
    )

async def toggle_delivery_method(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    current = settings.get("delivery_method", "direct")
    new_method = "codes" if current == "direct" else "direct"
    settings["delivery_method"] = new_method
    save_data(SETTINGS_FILE, settings)
    
    await update.message.reply_text(
        f"✅ <b>تم تغيير طريقة تسليم رصيد الشراء تلقائياً عند قبول الطلب لتصبح:</b>\n"
        f"👉 <code>{'أكواد تفعيل (الكود بنقطة)' if new_method == 'codes' else 'إضافة مباشرة للحساب'}</code>", 
        parse_mode='HTML'
    )

async def toggle_open_mode(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    settings = load_settings()
    settings["open_mode"] = not settings.get("open_mode", False)
    save_data(SETTINGS_FILE, settings)

    if settings["open_mode"]:
        msg = (
            "🔓 <b>تم تفعيل الوضع المفتوح.</b>\n\n"
            "البوت يعمل الآن مجاناً بدون رصيد في الخاص والجروبات."
        )
    else:
        msg = (
            "🔒 <b>تم إغلاق الوضع المفتوح.</b>\n\n"
            "تم الرجوع لنظام الرصيد والخصم الطبيعي."
        )
    await update.message.reply_text(msg, parse_mode='HTML')

async def start_generate_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    await update.message.reply_text(
        "<b>🗝️ بدء توليد كود شحن جديد:</b>\n\n"
        "يرجى إرسال قيمة الكود المطلوب (كم عدد النقاط/الروابط التي سيحصل عليها المستخدم عند تفعيله؟):\n"
        "مثال: أرسل الرقم <code>5</code> أو <code>1</code>\n\n"
        "<i>اكتب /cancel لإلغاء هذه العملية العودة.</i>",
        parse_mode='HTML'
    )
    return GIVE_CODE_POINTS

async def save_generated_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    
    text = update.message.text.strip()
    try:
        points = int(text)
        if points <= 0:
            await update.message.reply_text("❌ القيمة يجب أن تكون رقم صحيح أكبر من 0. يرجى إعادة الإرسال:")
            return GIVE_CODE_POINTS
    except ValueError:
        await update.message.reply_text("❌ يرجى إرسال رقم صحيح دقيق فقط (مثال: 5):")
        return GIVE_CODE_POINTS
        
    code = "LK-" + ''.join(secrets.choice(string.ascii_uppercase + string.digits) for _ in range(12))
    vouchers = load_data(VOUCHERS_FILE, {})
    vouchers[code] = {
        "status": "active",
        "points": points
    }
    save_data(VOUCHERS_FILE, vouchers)
    
    msg = f"""<b>🎉 تم توليد كود شحن بريميوم بنجاح!</b>

<b>🎟️ اضغط على الكود للنسخ الفوري:</b>
<code>{code}</code>

<b>📦 قيمة الكود الشاحنة: ({points}) نقطة/رابط مساعدة.</b>
<b>⏰ تاريخ الصلاحية: مفتوح للأبد ومستقر ومضمون.</b>"""
    await update.message.reply_text(msg, parse_mode='HTML')
    return ConversationHandler.END

# التوجيه لإعدادات قنوات الاشتراك الإجباري
async def force_sub_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    channels = settings.get("channels", [])
    report = "📢 <b>القنوات/المجموعات المضافة للاشتراك الإجباري:</b>\n\n"
    if not channels:
        report += "❌ لا تتوفر أي قنوات أو مجموعات مبرمجة حالياً.\n"
    else:
        for idx, ch in enumerate(channels, 1):
            report += f"{idx}. <code>{ch}</code>\n"
    report += (
        f"\n🛠️ <b>التحكم الفوري:</b>\n"
        f"⚙️ لإضافة قناة أو مجموعة: اكتب <code>/add_channel المعرف_أو_الآيدي</code>\n"
        f"⚙️ لحذف قناة أو مجموعة: اكتب <code>/del_channel المعرف_أو_الآيدي</code>\n\n"
        f"<i>💡 تأكد من إضافة البوت كمشرف في القناة أو المجموعة ليعمل الفحص بشكل سليم.</i>"
    )
    await update.message.reply_text(report, parse_mode='HTML')

async def add_channel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    if not context.args:
        await update.message.reply_text("⚠️ يرجى كتابة معرف القناة أو الآيدي الخاص بالمجموعة، مثال:\n<code>/add_channel @Username</code> أو <code>/add_channel -100xxxxxxxxxx</code>", parse_mode='HTML')
        return
    identifier = context.args[0].strip()
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    if identifier not in settings["channels"]:
        settings["channels"].append(identifier)
        save_data(SETTINGS_FILE, settings)
        await update.message.reply_text(f"✅ تم إضافة <code>{identifier}</code> إلى قائمة الاشتراك الإجباري بنجاح.", parse_mode='HTML')
    else:
        await update.message.reply_text("⚠️ هذا المعرف مضاف مسبقاً في القائمة!")

async def del_channel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    if not context.args:
        await update.message.reply_text("⚠️ يرجى كتابة المعرف أو الآيدي المراد حذفه، مثال:\n<code>/del_channel @Username</code>", parse_mode='HTML')
        return
    identifier = context.args[0].strip()
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    if identifier in settings["channels"]:
        settings["channels"].remove(identifier)
        save_data(SETTINGS_FILE, settings)
        await update.message.reply_text(f"✅ تم حذف <code>{identifier}</code> بنجاح.", parse_mode='HTML')
    else:
        await update.message.reply_text("❌ لم يتم العثور على هذا المعرف في القائمة المبرمجة.")

# التوجيه لإعدادات جروب معالجة الدفع والطلبات
async def set_payment_group_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    group_id = settings.get("group_id")
    msg = (
        f"👥 <b>إعدادات جروب معالجة المدفوعات والطلبات:</b>\n\n"
        f"الجروب الحالي مبرمج كالتالي: <code>{group_id or 'غير معين'}</code>\n\n"
        f"🔄 لتحديث وتغيير معرف الجروب، يرجى كتابة الأمر:\n"
        f"<code>/set_group معرف_الآيدي_الرقمي_هنا</code>\n"
        f"مثال للجروبات الكبيرة: <code>/set_group -100123456789</code>\n\n"
        f"<i>💡 يجب إضافة البوت كمشرف في الجروب المحدد لتلقي الطلبات وإتمام المعالجة جماعياً!</i>"
    )
    await update.message.reply_text(msg, parse_mode='HTML')

async def set_payment_group_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    if not context.args:
        await update.message.reply_text("⚠️ يرجى كتابة معرف الجروب الرقمي بعد الأمر، مثال:\n<code>/set_group -100223456789</code>", parse_mode='HTML')
        return
    try:
        group_id = int(context.args[0].strip())
        settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
        settings["group_id"] = group_id
        save_data(SETTINGS_FILE, settings)
        await update.message.reply_text(f"✅ تم برمجة وتثبيت معرف جروب الدفع بنجاح ليكون: <code>{group_id}</code>", parse_mode='HTML')
    except ValueError:
        await update.message.reply_text("❌ خطأ: آيدي الجروب يجب أن يكون قيمة رقمية صحيحة تبدأ بـ -100.")

async def ask_ban_user(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    await update.message.reply_text("🚫 تفضل بإرسال الـ ID الرقمي للعضو المراد حظره نهائياً:")
    return BAN_USER

async def execute_ban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    user_id = update.message.text.strip()
    banned = load_data(BANNED_FILE, [])
    if user_id not in banned:
        banned.append(user_id)
        save_data(BANNED_FILE, banned)
        await update.message.reply_text(f"✅ تم بنجاح تفعيل القيد وحظر المعرف الرقمي <code>{user_id}</code>.", parse_mode='HTML')
    return ConversationHandler.END

async def ask_new_price(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    await update.message.reply_text("💰 أرسل تكلفة الرابط الواحد بالجنيه المصري:")
    return CHANGE_PRICE

async def manage_purchase_offers(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    offers = get_purchase_offers()
    report = "🎁 <b>إدارة عروض زر شراء الرصيد</b>\n\n"
    if offers:
        for idx, offer in enumerate(offers, 1):
            report += f"{idx}. <code>{offer['label']}</code> = <code>{offer['qty']} لينك</code> بسعر <code>{offer['price']} ج</code>\n"
    else:
        report += "لا توجد عروض مضافة حالياً.\n"
    report += (
        "\n<b>لإضافة عرض جديد:</b>\n"
        "اكتب العرض والسعر بهذا الشكل:\n"
        "<code>6+6 50</code>\n\n"
        "<b>للحذف:</b> اكتب <code>حذف 1</code>\n"
        "<b>لمسح كل العروض:</b> اكتب <code>مسح</code>\n\n"
        "<i>اكتب /cancel للرجوع بدون تعديل.</i>"
    )
    await update.message.reply_text(report, parse_mode='HTML')
    return MANAGE_PURCHASE_OFFERS

async def save_purchase_offer(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    text = update.message.text.strip()
    settings = load_settings()
    offers = get_purchase_offers(settings)

    if text == "مسح":
        settings["purchase_offers"] = []
        save_data(SETTINGS_FILE, settings)
        await update.message.reply_text("✅ تم مسح كل عروض الشراء.")
        return ConversationHandler.END

    delete_match = re.match(r"^حذف\s+(\d+)$", text)
    if delete_match:
        index = int(delete_match.group(1)) - 1
        if 0 <= index < len(offers):
            removed = offers.pop(index)
            settings["purchase_offers"] = offers
            save_data(SETTINGS_FILE, settings)
            await update.message.reply_text(f"✅ تم حذف عرض: {removed['label']}.")
        else:
            await update.message.reply_text("❌ رقم العرض غير موجود.")
        return ConversationHandler.END

    offer = parse_purchase_offer_text(text)
    if not offer:
        await update.message.reply_text(
            "❌ صيغة العرض غير صحيحة.\n"
            "مثال صحيح: <code>6+6 50</code>\n"
            "هذا يعني 12 لينك بسعر 50 جنيه.",
            parse_mode='HTML'
        )
        return MANAGE_PURCHASE_OFFERS

    offers.append(offer)
    settings["purchase_offers"] = offers
    save_data(SETTINGS_FILE, settings)
    await update.message.reply_text(
        f"✅ تم إضافة العرض بنجاح:\n"
        f"🎁 <b>{offer['label']}</b>\n"
        f"📦 العدد: <code>{offer['qty']} لينك</code>\n"
        f"💰 السعر: <code>{offer['price']} جنيه</code>",
        parse_mode='HTML'
    )
    return ConversationHandler.END

async def save_new_price(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    try:
        new_price = int(update.message.text)
        settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
        settings["price"] = new_price
        save_data(SETTINGS_FILE, settings)
        await update.message.reply_text(f"✅ تم بنجاح تعديل سعر روابط الخدمة إلى: {new_price} جنيه مصري.")
    except Exception:
        await update.message.reply_text("❌ قيمة رقمية غير معروفة، تم إلغاء التغيير.")
    return ConversationHandler.END

async def ask_new_wallet(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    await update.message.reply_text("📱 <b>تفضل بإرسال رقم الكارت أو محفظة كاش المعتمدة الجديدة (11 رقماً):</b>", parse_mode='HTML')
    return CHANGE_WALLET

async def save_new_wallet(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    new_wallet = update.message.text.strip()
    
    if not re.match(r'^01[0125][0-9]{8}$', new_wallet):
        await update.message.reply_text(
            "⚠️ <b>تنسيق رقم هاتف خاطئ!</b>\n"
            "تأكد أن الرقم مكون من 11 رقم تماشياً مع فودافون كاش ومبيعات مصر.\n"
            "أرسل الرقم السليم الآن لإتمام الحفظ:",
            parse_mode='HTML'
        )
        return CHANGE_WALLET
        
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    settings["wallet"] = new_wallet
    save_data(SETTINGS_FILE, settings)
    await update.message.reply_text(f"✅ <b>ممتاز! تم تحديث محفظة الاستلام والتحويل بنجاح لتكون:</b>\n👉 <code>{new_wallet}</code>", parse_mode='HTML')
    return ConversationHandler.END

async def ask_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    await update.message.reply_text("📢 أرسل نص الرسالة التي تود بثها الآن لجميع المشتركين عبر الراديو:")
    return BROADCAST_MSG

async def execute_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    msg = update.message.text
    balances = load_data(BALANCE_FILE, {})
    count = 0
    for user_id in balances.keys():
        try:
            await context.bot.send_message(chat_id=int(user_id), text=msg)
            count += 1
        except Exception:
            pass
    await update.message.reply_text(f"✅ تم بث النشر بنجاح وإرسال تحديثات الراديو إلى {count} مستخدم نشط.")
    return ConversationHandler.END

async def check_vouchers_list(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    vouchers = load_data(VOUCHERS_FILE, {})
    active_codes = [code for code, data in vouchers.items() if data.get("status") == "active"]
    if not active_codes:
        await update.message.reply_text("🔍 لا تتوفر أكواد تفعيل نشطة بالمستودع.")
        return
    report = "🔍 <b>الأكواد النشطة غير المستخدمة حالياً (اضغط للنسخ مباشرة):</b>\n\n" + "\n".join([f"<code>{c}</code>" for c in active_codes])
    await update.message.reply_text(report, parse_mode='HTML')

async def show_pending_orders(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    pending_orders = load_data(PENDING_REQ_FILE, {})
    if not pending_orders:
        await update.message.reply_text("✅ لا تتوفر طلبات شحن معلقة حالياً.")
        return
    for uid, data in pending_orders.items():
        keyboard = [
            [
                InlineKeyboardButton("🟢 قبول وإرسال ✅", callback_data=f"accept_{uid}_{data.get('qty', 1)}"),
                InlineKeyboardButton("🔴 رفض وإلغاء ❌", callback_data=f"reject_{uid}")
            ]
        ]
        info = data.get('user_info', 'المشترك غير معروف')
        await update.message.reply_text(
            f"📋 <b>تفاصيل طلب معلق لمالك الحساب:</b>\n{info}\n\n📦 الكمية: {data.get('qty', 1)} رصيد", 
            parse_mode='HTML', 
            reply_markup=InlineKeyboardMarkup(keyboard)
        )

# --- قسم تتبع وعمل الإعلانات الآلية كل 3 ساعات ---
async def set_periodic_msg_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    current_msg = settings.get("periodic_message", "⚠️ لم يتم ضبط رسالة إعلانات حتى الآن.")
    msg = (
        f"⏱️ <b>إعدادات الرسالة الإعلانية التلقائية المكررة (كل ٣ ساعات):</b>\n\n"
        f"<b>الرسالة الحالية:</b>\n<code>{current_msg}</code>\n\n"
        f"⚙️ لتعديل وتغيير هذه الرسالة وبدء النشر التلقائي، أرسل رسالتك النصية الجديدة الآن:\n"
        f"(أرسل /cancel للرجوع دون تعديل)"
    )
    await update.message.reply_text(msg, parse_mode='HTML')
    return AUTO_MSG_WAITING

async def save_periodic_msg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    new_msg = update.message.text
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    settings["periodic_message"] = new_msg
    save_data(SETTINGS_FILE, settings)
    await update.message.reply_text("✅ <b>تم حفظ الرسالة الإعلانية بنجاح! سيقوم البوت بنشرها تلقائياً كل ٣ ساعات في كافة القنوات الإجبارية الرسمية المسجلة.</b>", parse_mode='HTML')
    return ConversationHandler.END

async def run_periodic_broadcaster_loop(context_bot_source):
    """لوب الإعلانات النصفية المتكررة كل ٣ ساعات"""
    while True:
        try:
            await asyncio.sleep(10800)
            settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
            periodic_msg = settings.get("periodic_message")
            channels = settings.get("channels", [])
            if periodic_msg and channels:
                for ch in channels:
                    try:
                        # استخراج البوت من المقود المباشر بأمان
                        bot = context_bot_source.bot if hasattr(context_bot_source, 'bot') else context_bot_source
                        await bot.send_message(chat_id=ch, text=periodic_msg, parse_mode='HTML')
                        await asyncio.sleep(2)
                    except Exception as e:
                        print(f"Error sending periodic msg to {ch}: {e}")
        except Exception as e:
            print(f"Periodic broad error: {e}")
            await asyncio.sleep(60)
async def run_periodic_backup_loop(application):
    """
    لوب لعمل نسخ احتياطي تلقائي كل 12 ساعة لجميع ملفات JSON المهمة بالبوت،
    وحفظها في مجلد backups وإرسال نسخة منها مباشرة إلى المشرفين (الأدمنز) على تليجرام.
    """
    # انتظار قصير عند إقلاع البوت لضمان استقرار الاتصال قبل الإرسال الأول
    await asyncio.sleep(15)
    while True:
        try:
            egypt_now = get_egypt_time()
            timestamp_str = egypt_now.strftime("%Y-%m-%d_%H-%M-%S")
            backup_filename = f"backup_{timestamp_str}.zip"
            
            # إنشاء مجلد النسخ الاحتياطية المحلي إذا لم يكن موجوداً
            BACKUPS_DIR.mkdir(parents=True, exist_ok=True)
            backup_filepath = BACKUPS_DIR / backup_filename
            
            # قائمة الملفات الهامة المراد تضمينها بالنسخة الاحتياطية
            important_files = [
                VOUCHERS_FILE,
                BALANCE_FILE,
                BANNED_FILE,
                SETTINGS_FILE,
                ACCOUNTS_FILE,
                REFERRALS_FILE,
                PENDING_REQ_FILE,
                USER_DETAILS_FILE,
                BOT_PROGRESS_FILE,
                USED_TX_FILE,
                UNCLAIMED_TX_FILE,
                FREE_JOIN_BONUS_FILE
            ]
            
            # ضغط الملفات الموجودة بالفعل داخل ملف zip واحد
            files_added_count = 0
            with zipfile.ZipFile(backup_filepath, 'w', zipfile.ZIP_DEFLATED) as zipf:
                for file_path in important_files:
                    if Path(file_path).exists():
                        zipf.write(file_path, arcname=Path(file_path).name)
                        files_added_count += 1
            
            if files_added_count > 0:
                print(f"📦 [نسخ احتياطي للسيستم]: تم إنشاء ملف {backup_filename} بنجاح ويحتوي على {files_added_count} ملفات جيثون.")
                # إرسال الملف لجميع الأدمنز للتأكيد والحفظ السحابي
                for admin_id in ADMIN_IDS:
                    try:
                        with open(backup_filepath, 'rb') as f:
                            await application.bot.send_document(
                                chat_id=admin_id,
                                document=f,
                                filename=backup_filename,
                                caption=(
                                    f"📦 <b>نسخة احتياطية تلقائية للسيستم بنجاح!</b>\n\n"
                                    f"⏰ توقيت القاهرة: <code>{egypt_now.strftime('%Y-%m-%d %I:%M:%S %p')}</code>\n"
                                    f"📂 إجمالي ملفات JSON المؤرشفة: <code>{files_added_count}</code>\n"
                                    f"🔄 التكرار: كل 12 ساعة تلقائياً."
                                ),
                                parse_mode='HTML'
                            )
                    except Exception as e:
                        print(f"Error sending backup to admin {admin_id}: {e}")
            else:
                print("⚠️ [نسخ احتياطي للسيستم]: لم يتم العثور على أي ملفات جيثون لنسخها احتياطياً.")
                
        except Exception as e:
            print(f"Error in periodic backup loop: {e}")
            
        # الانتظار لمدة 12 ساعة (تعادل 43200 ثانية)
        await asyncio.sleep(1800)
# --- قسم تتبع ومعرفة رصيد كافة المستخدمين وتعديلهم ---
async def ask_check_user_balance(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    balances = load_data(BALANCE_FILE, {})
    details = load_data(USER_DETAILS_FILE, {})
    
    if not balances:
        report = "📋 <b>لا توجد أي أرصدة مسجلة مسبقاً في قاعدة البيانات.</b>"
    else:
        report = "👥 <b>أرصدة جميع مستخدمي البوت الحاليين:</b>\n"
        report += "━━━━━━━━━━━━━━━━━━━\n"
        items = list(balances.items())
        for uid, bal in items[:100]:
            user_info = details.get(str(uid), {})
            username = user_info.get("username")
            first_name = user_info.get("first_name", "")
            if username:
                report += f"@{username} رصيده {bal}\n"
            elif first_name:
                report += f"👤 {first_name} ({uid}) رصيده {bal}\n"
            else:
                report += f"👤 آيدي: {uid} رصيده {bal}\n"
        if len(items) > 100:
            report += f"\n<i>... وتم إخفاء {len(items) - 100} مستخدم إضافي للتنسيق.</i>\n"
        report += "━━━━━━━━━━━━━━━━━━━\n"
        
    report += "\n💡 <b>لتعديل أو شحن رصيد أي مستخدم، قم بالرد (Reply) على رسالته بكلمة «رصيد» أو «رصيده» للتحكم الفوري والسريع!</b>"
    await update.message.reply_text(report, parse_mode='HTML')
    return ConversationHandler.END

async def show_user_balance_and_options(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id not in ADMIN_IDS: return ConversationHandler.END
    reply_to_user = update.message.reply_to_message
    if reply_to_user:
        target_id = str(reply_to_user.from_user.id)
    else:
        target_id = update.message.text.strip()
    balances = load_data(BALANCE_FILE, {})
    if target_id not in balances:
        balances[target_id] = 0
        save_data(BALANCE_FILE, balances)
    current_bal = balances[target_id]
    context.user_data['editing_user_id'] = target_id
    await update.message.reply_text(
        f"<b>📋 تفاصيل رصيد المستخدم المستهدف:</b>\n\n"
        f"🆔 آيدي العضو: <code>{target_id}</code>\n"
        f"💳 الرصيد الحالي النشط: <code>{current_bal} رابط مساعدة</code>",
        parse_mode='HTML'
    )
    return ConversationHandler.END

# --- تتبع ردود الإدارة المباشرة على رسائل الأعضاء لعرض الرصيد تلقائياً ---
async def handle_admin_reply_or_check_balance(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id not in ADMIN_IDS:
        return
    reply_to_user = update.message.reply_to_message
    if not reply_to_user:
        return
    message_text_stripped = update.message.text.strip()
    if message_text_stripped in ["رصيد", "رصيده"]:
        register_user_details(reply_to_user.from_user)
        target_user = reply_to_user.from_user
        target_id = str(target_user.id)
        balances = load_data(BALANCE_FILE, {})
        if target_id not in balances:
            balances[target_id] = 0
            save_data(BALANCE_FILE, balances)
        current_bal = balances[target_id]
        context.user_data['editing_user_id'] = target_id
        target_username = target_user.username
        if target_username:
            user_mention = f"@{target_username}"
        else:
            user_mention = f"👤 {target_user.first_name}"
        await update.message.reply_text(
            f"<b>{user_mention} رصيده {current_bal}</b>",
            parse_mode='HTML'
        )

# --- قسم تفعيل البوت داخل المجموعات والجروبات بمرونة متكاملة ---
async def handle_group_messages(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_type = update.effective_chat.type
    if chat_type not in ['group', 'supergroup']:
        return
    message_text = update.message.text
    if not message_text:
        return
    message_text_stripped = message_text.strip()
    user_id = str(update.effective_user.id)
    reply_to_user = update.message.reply_to_message
    
    register_user_details(update.effective_user)
    if reply_to_user and reply_to_user.from_user:
        register_user_details(reply_to_user.from_user)
        
    balances = load_data(BALANCE_FILE, {})
    if user_id not in balances:
        balances[user_id] = 0
        save_data(BALANCE_FILE, balances)
        
    # --- فحص ومطابقة عمليات الدفع والتأكيد التلقائي ---
    settings = load_data(SETTINGS_FILE, {"price": 15, "wallet": "01036428989", "channels": [], "group_id": None, "delivery_method": "direct"})
    group_id = settings.get("group_id")
    
    if group_id is None or str(update.effective_chat.id) == str(group_id):
        payment_info = parse_payment_message(message_text)
        if payment_info:
            phone = payment_info["phone"]
            amount = payment_info["amount"]
            tx_id = payment_info["tx_id"]
            
            used_tx = load_data(USED_TX_FILE, {})
            if tx_id not in used_tx:
                pending_orders = load_data(PENDING_REQ_FILE, {})
                matched_uid = None
                for uid, order in pending_orders.items():
                    order_phone = order.get("sender_number")
                    order_total = order.get("total")
                    if order_phone == phone and abs(float(order_total) - float(amount)) < 0.01:
                        matched_uid = uid
                        break
                        
                if matched_uid:
                    # الحالة أ: تم تقديم طلب الشراء مسبقاً
                    order = pending_orders[matched_uid]
                    qty = order["qty"]
                    total = order["total"]
                    
                    confirm_msg = await auto_confirm_order(
                        uid=matched_uid,
                        qty=qty,
                        total=total,
                        sender_number=phone,
                        tx_id=tx_id,
                        context=context
                    )
                    
                    user_info = order.get("user_info", f"ID: {matched_uid}")
                    new_text = (
                        f"<b>✅ تم التأكيد الأوتوماتيكي بنجاح!</b>\n"
                        f"👤 المستخدم: <code>{matched_uid}</code>\n"
                        f"📦 الكمية: <code>{qty} روابط</code>\n"
                        f"💰 المبلغ: <code>{total} جنيه</code>\n"
                        f"🔢 رقم العملية: <code>{tx_id}</code>\n\n"
                        f"👤 تفاصيل العضو:\n{user_info}"
                    )
                    
                    for msg_info in order.get("messages", []):
                        try:
                            await context.bot.edit_message_text(
                                chat_id=msg_info["chat_id"],
                                message_id=msg_info["msg_id"],
                                text=new_text,
                                parse_mode='HTML'
                            )
                        except Exception:
                            pass
                            
                    del pending_orders[matched_uid]
                    save_data(PENDING_REQ_FILE, pending_orders)
                    
                    try:
                        await update.message.reply_text(confirm_msg, parse_mode='HTML')
                    except Exception:
                        pass
                else:
                    # الحالة ب: التحويل وصل أولاً قبل تقديم طلب الشراء
                    unclaimed = load_data(UNCLAIMED_TX_FILE, {})
                    if tx_id not in unclaimed:
                        unclaimed[tx_id] = {
                            "phone": phone,
                            "amount": amount,
                            "timestamp": get_current_timestamp()
                        }
                        save_data(UNCLAIMED_TX_FILE, unclaimed)
            return
    
    # 1. إذا كتب المستخدم رصيدي بالجروب
    if message_text_stripped == "رصيدي" or message_text_stripped == "رصيد":
        bal = balances.get(user_id, 0)
        await update.message.reply_text(
            f"👤 أهلاً بك يا <b>{update.effective_user.first_name}</b>\n"
            f"💳 رصيدك الحالي والنشط للبوت: <code>{bal} رابط مساعدة</code>",
            parse_mode='HTML'
        )
        return

    # 2. إذا كتب الأدمن "رصيد" كرد (Reply)
    if message_text_stripped in ["رصيد", "رصيده"] and reply_to_user and int(user_id) in ADMIN_IDS:
        target_user = reply_to_user.from_user
        target_user_id = str(target_user.id)
        if target_user_id not in balances:
            balances[target_user_id] = 0
            save_data(BALANCE_FILE, balances)
        bal = balances.get(target_user_id, 0)
        target_username = target_user.username
        if target_username:
            user_mention = f"@{target_username}"
        else:
            user_mention = f"👤 {target_user.first_name}"
        await update.message.reply_text(
            f"<b>{user_mention} رصيده {bal}</b>",
            parse_mode='HTML'
        )
        return

    # 3. إذا كتب الأدمن "اعمل ده" كرد (Reply)
    if reply_to_user and "اعمل ده" in message_text_stripped and int(user_id) in ADMIN_IDS:
        reply_text = reply_to_user.text or ""
        link = extract_clean_url(reply_text)
        if link:
            target_user = reply_to_user.from_user
            target_user_id = str(target_user.id)
            if target_user_id not in balances:
                balances[target_user_id] = 0
                save_data(BALANCE_FILE, balances)
            await update.message.reply_text("🚨 <b>تم تفعيل صلاحية الأدمن! جاري إرسال ٣٠ مساعدة كاملة للرابط الآن...</b>", parse_mode='HTML')
            asyncio.create_task(process_bot_link_engine(
                link=link,
                chat_id=update.effective_chat.id,
                context=context,
                user_name=target_user.first_name,
                user_handle=target_user.username,
                is_group=True,
                reply_to_message_id=reply_to_user.message_id
            ))

    # 4. تفعيل كود شاحن بالجروب تلقائياً
    if message_text_stripped.upper().startswith("LK-"):
        code = message_text_stripped.upper()
        vouchers = load_data(VOUCHERS_FILE, {})
        if code in vouchers and vouchers[code]["status"] == "active":
            vouchers[code]["status"] = "used"
            points = int(vouchers[code].get("points", 1))
            save_data(VOUCHERS_FILE, vouchers)
            balances = load_data(BALANCE_FILE, {})
            balances[user_id] = balances.get(user_id, 0) + points
            save_data(BALANCE_FILE, balances)
            await update.message.reply_text(
                f"✅ <b>تم تفعيل كود الشحن بالجروب بنجاح!</b>\n"
                f"👤 العضو: {update.effective_user.first_name}\n"
                f"💳 رصيدك الحالي الآن: <code>{balances[user_id]} روابط</code>.",
                parse_mode='HTML'
            )
        return

    if message_text_stripped in ["الاسعار", "الأسعار", "السعر"]:
        settings = load_settings()
        price = settings.get("price", 15)
        await send_group_buy_prompt(
            update,
            context,
            f"💰 <b>سعر اللينك:</b> <code>{price}</code> جنيه مصري - يوجد عروض 🔥\nاضغط الزر أدناه لفتح البوت والشراء.",
            "شراء الآن 💳"
        )
        return

    # 5. إذا أرسل مستخدم رابط Midasbuy في الجروب
    link = extract_clean_url(message_text)
    if link:
        settings = load_settings()
        open_mode = settings.get("open_mode", False)
        user_bal = balances.get(user_id, 0)
        if not open_mode and user_bal <= 0:
            await send_group_buy_prompt(
                update,
                context,
                "رصيدك خلص\nاشحن علشان تكمل",
                "العروض هنا"
            )
            return
        charged_user_id = None
        refund_on_failure = False
        if not open_mode:
            balances[user_id] = user_bal - 1
            save_data(BALANCE_FILE, balances)
            charged_user_id = user_id
            refund_on_failure = True
        asyncio.create_task(process_bot_link_engine(
            link=link,
            chat_id=update.effective_chat.id,
            context=context,
            user_name=update.effective_user.first_name,
            user_handle=update.effective_user.username,
            is_group=True,
            reply_to_message_id=update.message.message_id,
            charged_user_id=charged_user_id,
            refund_on_failure=refund_on_failure
        ))

async def cancel_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("🚫 تم إلغاء العملية الجارية والعودة للقائمة.", reply_markup=ReplyKeyboardRemove())
    keyboard = [
        ["🟢 إرسال رابط ⬇️", "💳 رصيدي 💳"],
        ["🛒 شراء رصيد 💳", "🔑 كود تفعيل 🔑"],
        ["📖 المساعدة 📖", "👥 رابط الدعوة 👥"]
    ]
    if update.effective_user.id in ADMIN_IDS:
        keyboard.append(["⚙️ لوحة التحكم ⚙️"])
    await update.message.reply_text("👋 كيف يمكنني مساعدتك الآن؟", reply_markup=ReplyKeyboardMarkup(keyboard, resize_keyboard=True))
    return ConversationHandler.END

# --- المحرك ونقطة الانطلاق الرئيسية ---
async def start_background_tasks(application):
    asyncio.create_task(keep_browser_alive())
    asyncio.create_task(run_periodic_broadcaster_loop(application))
    asyncio.create_task(run_periodic_backup_loop(application))
    asyncio.create_task(resume_pending_tasks(application))

def main():
    BOT_TOKEN = "8820345956:AAGeoNiAQEh0MeWGAn9KzYz0tC2S5bgmP7c"
    application = Application.builder().token(BOT_TOKEN).post_init(start_background_tasks).build()
    
    # 1. فلتر معالجة الروابط التلقائية
    link_conv = ConversationHandler(
        entry_points=[MessageHandler(filters.Text(["إرسال رابط ⬇️", "🟢 إرسال رابط ⬇️"]), ask_for_link)],
        states={
            LINK_WAITING: [
                CommandHandler("cancel", cancel_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, process_link_and_run)
            ]
        },
        fallbacks=[CommandHandler("cancel", cancel_handler)]
    )
    
    # 2. فلتر معالجة كود تفعيل الرصيد
    code_conv = ConversationHandler(
        entry_points=[MessageHandler(filters.Text(["كود تفعيل 🔑", "🔑 كود تفعيل 🔑"]), ask_for_code)],
        states={
            CODE_WAITING: [
                CommandHandler("cancel", cancel_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, process_code)
            ]
        },
        fallbacks=[CommandHandler("cancel", cancel_handler)]
    )
    
    # 3. فلتر تتبع عمليات الشراء وطلب التحويل كاش
    purchase_conv = ConversationHandler(
        entry_points=[
            MessageHandler(filters.Regex(r"^/start(?:@\w+)?\s+(buy|purchase|charge)$"), ask_quantity),
            MessageHandler(filters.Text(["شراء رصيد 💳", "🛒 شراء رصيد 💳"]), ask_quantity)
        ],
        states={
            SELECT_QUANTITY: [MessageHandler(filters.TEXT & ~filters.COMMAND, process_quantity)],
            SEND_PAYMENT_INFO: [MessageHandler(filters.TEXT & ~filters.COMMAND, finish_purchase)],
        },
        fallbacks=[CommandHandler("cancel", cancel_handler)]
    )

    # 4. فلتر محادثة الأدمن وتعديل رصيد مستخدم مخصص
    admin_conv = ConversationHandler(
        entry_points=[
            MessageHandler(filters.Text("💰 تغيير السعر"), ask_new_price),
            MessageHandler(filters.Text("📱 تغيير المحفظة"), ask_new_wallet),
            MessageHandler(filters.Text("📢 بث إذاعة عامة"), ask_broadcast),
            MessageHandler(filters.Text("🚫 حظر مستخدم"), ask_ban_user),
            MessageHandler(filters.Text("⏱️ إعلان كل ٣ ساعات"), set_periodic_msg_panel),
            MessageHandler(filters.Text("🔍 رصيد مستخدم"), ask_check_user_balance),
            MessageHandler(filters.Text("🎁 عروض الشراء"), manage_purchase_offers),
            MessageHandler(filters.Text(["توليد كود شحن", "🗝️ توليد كود شحن"]), start_generate_code)
        ],
        states={
            CHANGE_PRICE: [MessageHandler(filters.TEXT & ~filters.COMMAND, save_new_price)],
            CHANGE_WALLET: [MessageHandler(filters.TEXT & ~filters.COMMAND, save_new_wallet)],
            BROADCAST_MSG: [MessageHandler(filters.TEXT & ~filters.COMMAND, execute_broadcast)],
            BAN_USER: [MessageHandler(filters.TEXT & ~filters.COMMAND, execute_ban)],
            AUTO_MSG_WAITING: [
                CommandHandler("cancel", cancel_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, save_periodic_msg)
            ],
            CHECK_USER_BAL_WAITING: [
                CommandHandler("cancel", cancel_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, show_user_balance_and_options)
            ],
            GIVE_CODE_POINTS: [
                CommandHandler("cancel", cancel_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, save_generated_code)
            ],
            MANAGE_PURCHASE_OFFERS: [
                CommandHandler("cancel", cancel_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, save_purchase_offer)
            ]
        },
        fallbacks=[CommandHandler("cancel", cancel_handler)]
    )

    application.add_handler(MessageHandler(filters.REPLY & filters.Text(["رصيد", "رصيده"]), handle_admin_reply_or_check_balance))
    application.add_handler(admin_conv)
    application.add_handler(MessageHandler(filters.Text(["لوحة التحكم ⚙️", "⚙️ لوحة التحكم ⚙️"]), admin_panel))
    application.add_handler(MessageHandler(filters.Text(["وقت البوت الحالي", "⏰ وقت البوت الحالي"]), show_bot_time))
    application.add_handler(MessageHandler(filters.Text("📊 الإحصائيات"), show_stats))
    application.add_handler(MessageHandler(filters.Text(["🔙 رجوع للقائمة الرئيسية", "🔙 رجوع"]), start))
    application.add_handler(MessageHandler(filters.Text(["عرض الطلبات المعلقة", "📋 عرض الطلبات المعلقة"]), show_pending_orders))
    application.add_handler(MessageHandler(filters.Text(["قائمة الأكواد", "🔍 قائمة الأكواد"]), check_vouchers_list))
    application.add_handler(MessageHandler(filters.Text("📢 الاشتراك الإجباري"), force_sub_panel))
    application.add_handler(CommandHandler("add_channel", add_channel_command))
    application.add_handler(CommandHandler("del_channel", del_channel_command))
    application.add_handler(MessageHandler(filters.Text("👥 تعيين جروب الدفع"), set_payment_group_panel))
    application.add_handler(CommandHandler("set_group", set_payment_group_command))
    application.add_handler(MessageHandler(filters.Text("🔄 طريقة تسليم الرصيد"), toggle_delivery_method))
    application.add_handler(MessageHandler(filters.Text("🔓 الوضع المفتوح"), toggle_open_mode))
    application.add_handler(MessageHandler(filters.Text(["رابط الدعوة 👥", "👥 رابط الدعوة 👥"]), referral_menu))
    application.add_handler(purchase_conv)
    application.add_handler(CallbackQueryHandler(admin_callback, pattern="^(accept|reject|check).*"))
    application.add_handler(CommandHandler("start", start))
    application.add_handler(link_conv)
    application.add_handler(code_conv)
    application.add_handler(MessageHandler(filters.Text(["رصيدي 💳", "💳 رصيدي 💳"]), check_balance))
    application.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT, handle_group_messages), group=2)
    application.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.TEXT & ~filters.COMMAND, check_math_answer), group=3)
    
    application.add_handler(MessageHandler(filters.Text(["المساعدة 📖", "📖 المساعدة 📖"]), lambda u, c: u.message.reply_text(
        "📖 <b>دليل تشغيل البوت للمبتدئين:</b>\n\n"
        "1️⃣ قم بفحص الرصيد المسجل بحسابك عبر تبويب '💳 رصيدي'.\n"
        "2️⃣ لشراء الرصيد وتجربة الدوران الفوري؛ تفضل بالدخول على '🛒 شراء رصيد' وحدد باقتك ثم قم بالدفع لـ فودافون كاش وإدخل هاتفك المحول بوضوح.\n"
        "3️⃣ بعد الحصول على تأكيد ورصيد، اضغط على '🟢 إرسال رابط' وأرسل رسالة المشاركة الخاصة بك من اللعبة مباشرة.\n"
        "4️⃣ سيقوم البوت بتدوير العجلة لـ 30 حساباً تلقائياً مع توضيح نسبة الإنجاز والوقت المنقضي بدقة !"
    , parse_mode='HTML')))
    
    print("🤖 البوت يعمل بأعلى كفاءة في الخلفية مع نظام الاستمرارية والحدود اليومية المحدثة!")
    
    # فحص كوتا الحسابات والتعديل الفوري عند التشغيل
    try:
        if ACCOUNTS_FILE.exists():
            with open(ACCOUNTS_FILE, 'r', encoding='utf-8') as f:
                accounts = json.load(f)
            accounts_modified = False
            if check_and_reset_accounts_quota(accounts):
                accounts_modified = True
            if refresh_account_cooldowns(accounts):
                accounts_modified = True
            if accounts_modified:
                save_data(ACCOUNTS_FILE, accounts)
    except Exception as e:
        print(f"Startup accounts reset check error: {e}")

    application.run_polling()

if __name__ == "__main__":
    main()
