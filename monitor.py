"""Монитор новых проектов на бирже Kwork с уведомлениями в Telegram.

Бот только читает публичную страницу биржи: без входа в аккаунт и без откликов.
Настройки фильтров меняются кнопками прямо в боте: команда /settings.

Запуск:
    python monitor.py                  — постоянная работа
    python monitor.py --dry-run        — разобрать sample_page.html и показать, что ушло бы в Telegram
    python monitor.py --test-telegram  — отправить тестовое сообщение
"""

import argparse
import html
import json
import logging
import os
import random
import shutil
import socket
import sqlite3
import sys
import time
from datetime import datetime
from logging.handlers import RotatingFileHandler

import requests
from dotenv import load_dotenv

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# Папка для того, что бот меняет сам: база, лог и рабочая копия настроек.
# Локально — папка проекта. На хостинге Bothost платформа задаёт DATA_DIR=/app/data:
# только эта папка переживает перезапуски и обновления из Git.
DATA_DIR = os.getenv("DATA_DIR", "").strip() or BASE_DIR

DB_PATH = os.path.join(DATA_DIR, "seen.db")
LOG_PATH = os.path.join(DATA_DIR, "monitor.log")
# Рабочие настройки. Если DATA_DIR — отдельная папка, при первом запуске
# туда копируется config.py из проекта, и дальше бот меняет уже копию.
CONFIG_PATH = os.path.join(DATA_DIR, "config.py")
PROJECT_CONFIG_PATH = os.path.join(BASE_DIR, "config.py")
SAMPLE_PAGE_PATH = os.path.join(BASE_DIR, "sample_page.html")

LIST_URL = "https://kwork.ru/projects"
PROJECT_URL = "https://kwork.ru/projects/{}"
TELEGRAM_API = "https://api.telegram.org/bot{}/{}"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
}

# Данные проектов лежат во встроенном JSON: <script>window.stateData={...};</script>
STATE_MARKER = "window.stateData="

# После скольких пустых проверок подряд предупреждать в Telegram.
EMPTY_CHECKS_LIMIT = 3

REQUEST_TIMEOUT = 30

# Сколько проектов максимум присылать по команде /all, чтобы не завалить чат.
ALL_COMMAND_LIMIT = 30

# Порт-«замок»: запущенный бот занимает его, и вторая копия на этом же
# компьютере не стартует. Если вдруг порт нужен другой программе — смените число.
SINGLE_INSTANCE_PORT = 47811

# Сколько секунд ждать сообщений от Telegram за один запрос (long polling).
POLL_SECONDS = 25

# Telegram не принимает сообщения длиннее 4096 символов.
TELEGRAM_MAX_LENGTH = 4000

# Команды в меню бота.
BOT_COMMANDS = [
    ("all", "Все текущие подходящие проекты"),
    ("settings", "Настройки фильтров"),
    ("help", "Как пользоваться"),
]

HELP_TEXT = """<b>Монитор новых проектов Kwork</b>

Новые подходящие проекты приходят в этот чат сами.

/all — прислать все проекты, которые сейчас висят на первых страницах ваших рубрик и подходят под фильтры, включая те, что бот уже видел.

/settings — настройки кнопками: рубрики, ключевые слова, стоп-слова, отклики, бюджет, интервал.

Слова ищутся без учёта регистра, как часть слова, в названии и описании проекта."""

# Названия списков слов для экранов настроек. Ключ — короткий код в кнопках.
WORD_LISTS = {
    "k": ("keywords", "🔑 Ключевые слова"),
    "s": ("stop_words", "⛔ Стоп-слова"),
}

# Числовые настройки: код -> (поле, название, минимум, пример).
NUMBERS = {
    "o": ("max_offers", "Макс. откликов", 0, "30"),
    "b": ("min_budget", "Мин. бюджет, ₽", 0, "2000"),
    "i": ("interval_min", "Интервал проверки, мин", 1, "7"),
}

log = logging.getLogger("kwork")


# ---------- Настройка ----------

def setup_logging():
    os.makedirs(DATA_DIR, exist_ok=True)
    log.setLevel(logging.INFO)
    formatter = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")

    # Лог-файл ограничен 3 файлами по 2 МБ, чтобы не разрастался на VPS.
    file_handler = RotatingFileHandler(LOG_PATH, maxBytes=2_000_000, backupCount=3, encoding="utf-8")
    file_handler.setFormatter(formatter)
    log.addHandler(file_handler)

    console_handler = logging.StreamHandler()
    console_handler.setFormatter(formatter)
    log.addHandler(console_handler)


def read_env():
    """Читает токен, chat_id и начальный интервал из .env."""
    load_dotenv(os.path.join(BASE_DIR, ".env"))
    # Bothost кладёт токен из поля «Bot Token» в BOT_TOKEN.
    token = (os.getenv("TELEGRAM_TOKEN") or os.getenv("BOT_TOKEN") or "").strip()
    chat_id = os.getenv("TELEGRAM_CHAT_ID", "").strip()

    interval_text = os.getenv("CHECK_INTERVAL_MIN", "7").strip()
    try:
        interval = float(interval_text)
    except ValueError:
        interval = 7
    if interval <= 0:
        interval = 7
    if interval == int(interval):
        interval = int(interval)

    return token, chat_id, interval


def lock_single_instance():
    """Не даёт запустить вторую копию бота на этом компьютере.

    Две копии делят между собой нажатия кнопок и затирают настройки друг друга.
    Бот занимает локальный порт: пока он работает, второй запуск получит ошибку.
    Порт освобождается сам, когда бот остановлен любым способом.
    Возвращает сокет (его надо держать до конца работы) или None, если копия уже есть."""
    lock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        lock.bind(("127.0.0.1", SINGLE_INSTANCE_PORT))
    except OSError:
        lock.close()
        return None
    return lock


# ---------- Настройки фильтров (config.py) ----------
#
# Все настройки живут в config.py. Кнопки в боте переписывают этот файл,
# а если вы поправили его вручную — бот перечитает его сам (см. reload_if_changed).

# Время изменения config.py, когда бот последний раз его читал или писал.
config_mtime = None


def read_config(env_interval):
    """Читает config.py и возвращает словарь настроек. При ошибке — ValueError."""
    namespace = {}
    try:
        with open(CONFIG_PATH, encoding="utf-8") as config_file:
            source = config_file.read()
        exec(compile(source, CONFIG_PATH, "exec"), namespace)
    except OSError as error:
        raise ValueError("не удалось открыть config.py: {}".format(error))
    except Exception as error:
        raise ValueError("ошибка в config.py: {}".format(error))

    try:
        categories = {}
        for category_id, name in namespace["CATEGORIES"].items():
            categories[str(int(category_id))] = str(name)

        interval = namespace.get("CHECK_INTERVAL_MIN", env_interval)
        if interval <= 0:
            interval = env_interval
        if interval == int(interval):
            interval = int(interval)

        return {
            "categories": categories,
            "keywords": clean_words(namespace["KEYWORDS"]),
            "stop_words": clean_words(namespace["STOP_WORDS"]),
            "max_offers": int(namespace["MAX_OFFERS"]),
            "min_budget": int(namespace["MIN_BUDGET"]),
            "interval_min": interval,
            "description_length": int(namespace.get("DESCRIPTION_LENGTH", 300)),
        }
    except (KeyError, TypeError, ValueError, AttributeError) as error:
        raise ValueError("в config.py не хватает настройки или она неверного вида: {}".format(error))


def load_settings(env_interval):
    """Читает config.py при запуске. Если файл испорчен — бот не стартует."""
    global config_mtime
    if not os.path.exists(CONFIG_PATH):
        # Первый запуск на хостинге: в папке данных ещё нет настроек — берём из проекта.
        os.makedirs(DATA_DIR, exist_ok=True)
        shutil.copyfile(PROJECT_CONFIG_PATH, CONFIG_PATH)
        log.info("Настройки скопированы из проекта в %s", CONFIG_PATH)
    settings = read_config(env_interval)
    config_mtime = os.path.getmtime(CONFIG_PATH)
    return settings


def reload_if_changed(settings, env_interval):
    """Если config.py поправили вручную — перечитывает его в settings."""
    global config_mtime
    try:
        mtime = os.path.getmtime(CONFIG_PATH)
    except OSError:
        return
    if mtime == config_mtime:
        return

    try:
        fresh = read_config(env_interval)
    except ValueError as error:
        # Не перечитываем испорченный файл, работаем со старыми настройками.
        log.error("config.py изменён, но прочитать его не удалось: %s", error)
        config_mtime = mtime
        return

    settings.clear()
    settings.update(fresh)
    config_mtime = mtime
    log.info("config.py изменён вручную — настройки перечитаны")


def python_text(value):
    """Строка в кавычках для записи в config.py: "лендинг"."""
    return json.dumps(value, ensure_ascii=False)


def save_settings(settings):
    """Записывает настройки в config.py."""
    global config_mtime

    lines = [
        "# Настройки монитора Kwork.",
        "#",
        "# Этот файл переписывает бот, когда вы меняете настройки кнопками (/settings).",
        "# Его можно править и вручную — бот сам заметит изменения при следующем",
        "# нажатии кнопки или следующей проверке биржи, перезапуск не нужен.",
        "# Свои комментарии сюда лучше не писать: бот их не сохранит.",
        "",
        "# Рубрики биржи (id: название). Каждая рубрика загружается отдельным запросом,",
        "# потому что без входа в аккаунт Kwork не умеет показывать несколько рубрик сразу.",
        "CATEGORIES = {",
    ]
    for category_id, name in settings["categories"].items():
        lines.append("    {}: {},".format(category_id, python_text(name)))
    lines.append("}")
    lines.append("")
    lines.append("# Хотя бы одно из слов должно быть в названии или описании проекта.")
    lines.append("# Ищутся как часть слова, без учёта регистра. Буквы «е» и «ё» разные.")
    lines.append("# Пустой список — присылаются все проекты, прошедшие остальные фильтры.")
    lines.append("KEYWORDS = [")
    for word in settings["keywords"]:
        lines.append("    {},".format(python_text(word)))
    lines.append("]")
    lines.append("")
    lines.append("# Если в названии или описании есть любое из этих слов — проект пропускается.")
    lines.append("STOP_WORDS = [")
    for word in settings["stop_words"]:
        lines.append("    {},".format(python_text(word)))
    lines.append("]")
    lines.append("")
    lines.append("# Не присылать проекты, на которые уже больше стольких откликов.")
    lines.append("MAX_OFFERS = {}".format(settings["max_offers"]))
    lines.append("")
    lines.append("# Минимальный бюджет в рублях. Сравнивается с допустимым бюджетом проекта")
    lines.append("# (сколько заказчик готов заплатить максимум).")
    lines.append("MIN_BUDGET = {}".format(settings["min_budget"]))
    lines.append("")
    lines.append("# Как часто проверять биржу, в минутах (плюс случайно 0–60 сек).")
    lines.append("CHECK_INTERVAL_MIN = {}".format(format_number(settings["interval_min"])))
    lines.append("")
    lines.append("# Сколько символов описания показывать в сообщении.")
    lines.append("DESCRIPTION_LENGTH = {}".format(settings["description_length"]))
    lines.append("")

    # Пишем во временный файл и подменяем, чтобы при сбое не остался обрезанный файл.
    temp_path = CONFIG_PATH + ".tmp"
    with open(temp_path, "w", encoding="utf-8") as config_file:
        config_file.write("\n".join(lines))
    os.replace(temp_path, CONFIG_PATH)
    config_mtime = os.path.getmtime(CONFIG_PATH)


def clean_words(words):
    """Приводит слова к нижнему регистру, убирает пустые и повторы."""
    result = []
    for word in words:
        word = word.strip().lower()
        if word and word not in result:
            result.append(word)
    return result


# ---------- Загрузка и разбор страницы ----------

def fetch_page(category_id=None):
    """Загружает первую страницу проектов (одной рубрики или всей биржи)."""
    params = {"view": 0}
    if category_id is not None:
        params["c"] = category_id
    response = requests.get(LIST_URL, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT)
    response.raise_for_status()
    return response.text


def parse_state(page_html):
    """Достаёт встроенный JSON window.stateData. Если разметка поменялась — ValueError."""
    start = page_html.find(STATE_MARKER)
    if start == -1:
        raise ValueError("на странице нет window.stateData — возможно, сменилась разметка")

    decoder = json.JSONDecoder()
    try:
        state, _ = decoder.raw_decode(page_html, start + len(STATE_MARKER))
    except json.JSONDecodeError as error:
        raise ValueError("не удалось разобрать JSON stateData: {}".format(error))
    return state


def extract_projects(page_html):
    """Список проектов со страницы."""
    state = parse_state(page_html)

    raw_projects = None
    wants_list = state.get("wantsListData")
    if isinstance(wants_list, dict):
        pagination = wants_list.get("pagination")
        if isinstance(pagination, dict):
            raw_projects = pagination.get("data")
    if raw_projects is None:
        raw_projects = state.get("wants")
    if not isinstance(raw_projects, list):
        raise ValueError("в stateData нет списка проектов — возможно, сменилась разметка")

    projects = []
    for raw in raw_projects:
        try:
            projects.append(parse_project(raw))
        except (KeyError, TypeError, ValueError) as error:
            log.warning("Не удалось разобрать проект: %s", error)
    return projects


def extract_rubrics(page_html):
    """Дерево рубрик: список (id, название, [(id, название), ...])."""
    state = parse_state(page_html)
    categories = state.get("categories")
    if not isinstance(categories, dict):
        raise ValueError("в stateData нет списка рубрик")

    rubrics = []
    for parent in categories.values():
        children = []
        for child in parent.get("cats") or []:
            children.append((str(child.get("CATID")), child.get("name", "")))
        rubrics.append((str(parent.get("CATID")), parent.get("name", ""), children))
    return rubrics


def find_rubric_name(rubrics, category_id):
    for parent_id, parent_name, children in rubrics:
        if parent_id == category_id:
            return parent_name
        for child_id, child_name in children:
            if child_id == category_id:
                return child_name
    return None


def to_number(value):
    """Превращает '7000.00', 7000 или None в число."""
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return 0


def parse_project(raw):
    """Оставляет из сырых данных Kwork только нужные поля."""
    project_id = int(raw["id"])

    hired_percent = None
    user = raw.get("user")
    if isinstance(user, dict) and isinstance(user.get("data"), dict):
        hired_percent = user["data"].get("wants_hired_percent")

    description = html.unescape(raw.get("description") or "")
    description = description.replace("\r\n", "\n").replace("\r", "\n").strip()

    return {
        "id": project_id,
        "name": html.unescape(raw.get("name") or "").strip(),
        "description": description,
        "price": to_number(raw.get("priceLimit")),
        "max_price": to_number(raw.get("possiblePriceLimit")),
        "offers": to_number(raw.get("kwork_count")),
        "hired_percent": hired_percent,
        "time_left": raw.get("timeLeft") or "",
        "date_active": raw.get("date_active") or "",
        "url": PROJECT_URL.format(project_id),
    }


# ---------- Фильтры ----------

def find_word(text, words):
    """Возвращает первое слово из списка, которое встречается в тексте, или None."""
    for word in words:
        if word.lower() in text:
            return word
    return None


def check_filters(project, settings):
    """Возвращает None, если проект подходит, иначе — причину отказа."""
    text = (project["name"] + " " + project["description"]).lower()

    stop_word = find_word(text, settings["stop_words"])
    if stop_word:
        return "стоп-слово «{}»".format(stop_word)

    if project["offers"] > settings["max_offers"]:
        return "откликов {} > {}".format(project["offers"], settings["max_offers"])

    budget = max(project["price"], project["max_price"])
    if budget < settings["min_budget"]:
        return "бюджет {} < {}".format(budget, settings["min_budget"])

    if settings["keywords"] and not find_word(text, settings["keywords"]):
        return "нет ключевых слов"

    return None


# ---------- Сообщения о проектах ----------

def format_money(amount):
    return "{:,}".format(int(amount)).replace(",", " ")


def format_message(project, settings):
    """Текст уведомления о проекте (HTML-разметка)."""
    price = project["price"]
    max_price = project["max_price"]
    if max_price > price:
        budget = "{} – {} ₽".format(format_money(price), format_money(max_price))
    else:
        budget = "{} ₽".format(format_money(price))

    if project["hired_percent"] is None or project["hired_percent"] == "":
        hired = "нет данных"
    else:
        hired = "{}%".format(project["hired_percent"])

    description = project["description"]
    limit = settings["description_length"]
    if len(description) > limit:
        description = description[:limit].rstrip() + "…"

    lines = [
        "<b>{}</b>".format(html.escape(project["name"])),
        "",
        "💰 Бюджет: {}".format(budget),
        "📨 Откликов: {}".format(project["offers"]),
        "🤝 Найм у заказчика: {}".format(hired),
        "⏳ Осталось: {}".format(html.escape(project["time_left"])),
        "",
        html.escape(description),
        "",
        project["url"],
    ]
    return "\n".join(lines)


def format_word_list(words):
    if not words:
        return "пусто"
    escaped = []
    for word in words:
        escaped.append(html.escape(word))
    return ", ".join(escaped)


def format_number(value):
    """7.0 -> '7', 7.5 -> '7.5'"""
    if value == int(value):
        return str(int(value))
    return str(value)


# ---------- Telegram ----------

def telegram_call(token, method, data, timeout=REQUEST_TIMEOUT):
    """Вызывает метод Telegram API. Возвращает поле result или None при ошибке."""
    try:
        response = requests.post(TELEGRAM_API.format(token, method), data=data, timeout=timeout)
    except requests.RequestException as error:
        log.error("Telegram недоступен (%s): %s", method, error)
        return None

    if response.status_code != 200:
        # Нажали кнопку, а на экране ничего не поменялось — это не ошибка.
        if "message is not modified" in response.text:
            return {}
        if response.status_code == 409:
            # Telegram отдаёт сообщения только одному запущенному боту.
            log.error("Бот запущен дважды (например, в PyCharm и в консоли или ещё и на сервере). "
                      "Остановите лишний — иначе кнопки будут срабатывать через раз.")
            return None
        log.error("Telegram ответил ошибкой %s (%s): %s", response.status_code, method, response.text[:300])
        return None

    try:
        return response.json().get("result")
    except ValueError:
        log.error("Telegram прислал не JSON (%s)", method)
        return None


def send_telegram(token, chat_id, text, keyboard=None):
    """Отправляет сообщение. Возвращает True при успехе, ошибки только логирует."""
    data = {
        "chat_id": chat_id,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
        # Обычное уведомление со звуком/вибрацией (не «тихое»).
        # Будет ли телефон вибрировать, решают настройки Telegram на телефоне.
        "disable_notification": False,
    }
    if keyboard is not None:
        data["reply_markup"] = json.dumps({"inline_keyboard": keyboard}, ensure_ascii=False)
    return telegram_call(token, "sendMessage", data) is not None


def edit_message(token, chat_id, message_id, text, keyboard):
    """Меняет текст и кнопки уже отправленного сообщения (экран меню)."""
    data = {
        "chat_id": chat_id,
        "message_id": message_id,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
        "reply_markup": json.dumps({"inline_keyboard": keyboard}, ensure_ascii=False),
    }
    telegram_call(token, "editMessageText", data)


def delete_message(token, chat_id, message_id):
    telegram_call(token, "deleteMessage", {"chat_id": chat_id, "message_id": message_id})


def answer_callback(token, callback_id, text=""):
    """Убирает «часики» с нажатой кнопки. text — всплывающая подсказка."""
    data = {"callback_query_id": callback_id}
    if text:
        data["text"] = text[:200]
    telegram_call(token, "answerCallbackQuery", data)


def set_bot_commands(token):
    """Показывает команды в меню бота в Telegram."""
    commands = []
    for name, description in BOT_COMMANDS:
        commands.append({"command": name, "description": description})
    telegram_call(token, "setMyCommands", {"commands": json.dumps(commands, ensure_ascii=False)})


def get_updates(token, offset, wait_seconds):
    """Новые сообщения и нажатия кнопок. Ждёт до wait_seconds секунд, если их нет."""
    data = {"timeout": wait_seconds, "allowed_updates": json.dumps(["message", "callback_query"])}
    if offset is not None:
        data["offset"] = offset
    result = telegram_call(token, "getUpdates", data, timeout=wait_seconds + 15)
    if result is None:
        # Сеть или Telegram недоступны — не долбим запросами, подождём.
        time.sleep(5)
        return []
    return result


def button(text, data):
    return {"text": text, "callback_data": data}


# ---------- Экраны меню настроек ----------
#
# Каждый экран — функция, которая возвращает (текст, кнопки).
# В кнопках зашит короткий код (callback_data, не больше 64 байт):
#   menu           — главный экран
#   w:k / w:s      — список ключевых / стоп-слов (нажатие на слово удаляет его)
#   we:k / we:s    — тот же список в режиме «изменить»
#   wd:k:3         — удалить слово №3;  wi:k:3 — изменить слово №3
#   wa:k           — добавить слова;    wc:k   — очистить список
#   num            — числа;             n:o    — ввести новое значение
#   rub            — группы рубрик;     rg:11  — рубрики группы 11
#   rt:79:11       — включить/выключить рубрику 79 (из группы 11)
#   cancel / close

def screen_main(settings):
    lines = ["<b>⚙️ Настройки монитора Kwork</b>", "", "<b>Рубрики:</b>"]
    if settings["categories"]:
        for category_id, name in settings["categories"].items():
            lines.append("• {} <i>({})</i>".format(html.escape(name), category_id))
    else:
        lines.append("нет — бот ничего не проверяет")

    keywords_text = format_word_list(settings["keywords"])
    if not settings["keywords"]:
        keywords_text = "пусто — присылаю всё, что прошло остальные фильтры"

    lines.append("")
    lines.append("<b>Ключевые слова ({}):</b> {}".format(len(settings["keywords"]), keywords_text))
    lines.append("<b>Стоп-слова ({}):</b> {}".format(len(settings["stop_words"]), format_word_list(settings["stop_words"])))
    lines.append("")
    lines.append("<b>Макс. откликов:</b> {}".format(settings["max_offers"]))
    lines.append("<b>Мин. бюджет:</b> {} ₽".format(format_money(settings["min_budget"])))
    lines.append("<b>Интервал:</b> {} мин (+ 0–60 сек)".format(format_number(settings["interval_min"])))

    keyboard = [
        [button("📂 Рубрики", "rub"), button("🔢 Числа", "num")],
        [button("🔑 Ключевые слова", "w:k"), button("⛔ Стоп-слова", "w:s")],
        [button("✖️ Закрыть", "close")],
    ]
    return "\n".join(lines), keyboard


def screen_words(settings, code, edit_mode):
    key, title = WORD_LISTS[code]
    words = settings[key]

    lines = ["<b>{}</b> ({})".format(title, len(words)), ""]
    if not words:
        if code == "k":
            lines.append("Список пуст — присылаю всё, что прошло остальные фильтры.")
        else:
            lines.append("Список пуст.")
    elif edit_mode:
        lines.append("Нажмите на слово, которое хотите <b>изменить</b>.")
    else:
        lines.append("Нажмите на слово, чтобы <b>удалить</b> его.")

    # Слова — кнопками по два в ряд.
    keyboard = []
    row = []
    for index, word in enumerate(words):
        if edit_mode:
            row.append(button("✏️ " + word, "wi:{}:{}".format(code, index)))
        else:
            row.append(button("❌ " + word, "wd:{}:{}".format(code, index)))
        if len(row) == 2:
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)

    if edit_mode:
        keyboard.append([button("← Режим удаления", "w:" + code)])
    else:
        actions = [button("➕ Добавить", "wa:" + code)]
        if words:
            actions.append(button("✏️ Изменить", "we:" + code))
        keyboard.append(actions)
        if words:
            keyboard.append([button("🧹 Очистить весь список", "wc:" + code)])
    keyboard.append([button("« Назад", "menu")])
    return "\n".join(lines), keyboard


def screen_numbers(settings):
    lines = ["<b>🔢 Числа</b>", "", "Нажмите на значение, чтобы его изменить."]
    keyboard = []
    for code, (key, title, _, _) in NUMBERS.items():
        value = settings[key]
        if key == "min_budget":
            shown = "{} ₽".format(format_money(value))
        elif key == "interval_min":
            shown = "{} мин".format(format_number(value))
        else:
            shown = format_number(value)
        keyboard.append([button("{}: {}".format(title.split(",")[0], shown), "n:" + code)])
    keyboard.append([button("« Назад", "menu")])
    return "\n".join(lines), keyboard


def screen_rubric_groups(settings, rubrics):
    lines = ["<b>📂 Рубрики</b>", "", "Выберите раздел. Цифра в скобках — сколько рубрик в нём отслеживается."]
    keyboard = []
    for parent_id, parent_name, children in rubrics:
        selected = 0
        if parent_id in settings["categories"]:
            selected += 1
        for child_id, _ in children:
            if child_id in settings["categories"]:
                selected += 1
        label = parent_name
        if selected:
            label = "{} ({})".format(parent_name, selected)
        keyboard.append([button(label, "rg:" + parent_id)])
    keyboard.append([button("« Назад", "menu")])
    return "\n".join(lines), keyboard


def screen_rubric_children(settings, rubrics, group_id):
    for parent_id, parent_name, children in rubrics:
        if parent_id != group_id:
            continue

        lines = [
            "<b>📂 {}</b>".format(html.escape(parent_name)),
            "",
            "✅ — отслеживается. Нажмите, чтобы включить или выключить.",
        ]
        keyboard = []
        mark = "✅" if parent_id in settings["categories"] else "▫️"
        keyboard.append([button("{} Весь раздел целиком".format(mark), "rt:{}:{}".format(parent_id, parent_id))])
        for child_id, child_name in children:
            mark = "✅" if child_id in settings["categories"] else "▫️"
            keyboard.append([button("{} {}".format(mark, child_name), "rt:{}:{}".format(child_id, parent_id))])
        keyboard.append([button("« К разделам", "rub"), button("« В меню", "menu")])
        return "\n".join(lines), keyboard

    return "Раздел не найден.", [[button("« К разделам", "rub")]]


def screen_prompt(text):
    """Экран «напишите ответ сообщением» с кнопкой отмены."""
    return text, [[button("Отмена", "cancel")]]


def screen_error(text):
    return text, [[button("« В меню", "menu")]]


# ---------- Действия с настройками ----------

def add_rubric(settings, category_id, conn):
    """Включает рубрику: проверяет её на Kwork и запоминает уже висящие там проекты,
    чтобы не прислать их все разом. Возвращает короткий текст для подсказки."""
    try:
        page_html = fetch_page(int(category_id))
        name = find_rubric_name(extract_rubrics(page_html), category_id)
        projects = extract_projects(page_html)
    except requests.RequestException:
        return "Не удалось загрузить Kwork, попробуйте позже"
    except ValueError as error:
        return "Не удалось разобрать страницу Kwork: {}".format(error)

    if name is None:
        return "Такой рубрики на Kwork нет"

    for project in projects:
        mark_seen(conn, project["id"])

    settings["categories"][category_id] = name
    save_settings(settings)
    return "Включил «{}». Текущих проектов: {} — пришлю только новые".format(name, len(projects))


def toggle_rubric(settings, category_id, conn):
    if category_id in settings["categories"]:
        name = settings["categories"].pop(category_id)
        save_settings(settings)
        return "Выключил «{}»".format(name)
    return add_rubric(settings, category_id, conn)


def get_rubrics(menu):
    """Дерево рубрик Kwork. Загружается один раз и запоминается."""
    if menu.get("rubrics") is None:
        try:
            menu["rubrics"] = extract_rubrics(fetch_page())
        except (requests.RequestException, ValueError) as error:
            log.error("Не удалось загрузить список рубрик: %s", error)
            return None
    return menu["rubrics"]


def word_at(settings, code, index_text):
    """Слово по номеру из кнопки. None, если список успел измениться."""
    key = WORD_LISTS[code][0]
    if not index_text.isdigit():
        return None
    index = int(index_text)
    if index >= len(settings[key]):
        return None
    return settings[key][index]


def handle_callback(data, settings, conn, menu):
    """Обрабатывает нажатие кнопки. Возвращает (текст, кнопки, подсказка);
    текст None — значит, сообщение меню нужно удалить."""
    parts = data.split(":")
    action = parts[0]

    # Любое нажатие кнопки отменяет ожидание ввода.
    menu["pending"] = None

    if action == "menu" or action == "cancel":
        text, keyboard = screen_main(settings)
        return text, keyboard, ""

    if action == "close":
        return None, None, ""

    if action == "w" and parts[1] in WORD_LISTS:
        text, keyboard = screen_words(settings, parts[1], False)
        return text, keyboard, ""

    if action == "we" and parts[1] in WORD_LISTS:
        text, keyboard = screen_words(settings, parts[1], True)
        return text, keyboard, ""

    if action == "wd" and parts[1] in WORD_LISTS:
        code = parts[1]
        word = word_at(settings, code, parts[2])
        toast = "Список изменился, попробуйте ещё раз"
        if word is not None:
            settings[WORD_LISTS[code][0]].remove(word)
            save_settings(settings)
            toast = "Удалил «{}»".format(word)
        text, keyboard = screen_words(settings, code, False)
        return text, keyboard, toast

    if action == "wi" and parts[1] in WORD_LISTS:
        code = parts[1]
        word = word_at(settings, code, parts[2])
        if word is None:
            text, keyboard = screen_words(settings, code, True)
            return text, keyboard, "Список изменился, попробуйте ещё раз"
        menu["pending"] = {"action": "edit_word", "code": code, "word": word}
        text, keyboard = screen_prompt(
            "✏️ Напишите сообщением, на что заменить «<b>{}</b>».".format(html.escape(word)))
        return text, keyboard, ""

    if action == "wa" and parts[1] in WORD_LISTS:
        code = parts[1]
        menu["pending"] = {"action": "add_words", "code": code}
        text, keyboard = screen_prompt(
            "➕ Напишите сообщением слова для списка «{}».\n"
            "Можно несколько через запятую: <i>лендинг, сайт под ключ</i>".format(WORD_LISTS[code][1]))
        return text, keyboard, ""

    if action == "wc" and parts[1] in WORD_LISTS:
        code = parts[1]
        settings[WORD_LISTS[code][0]] = []
        save_settings(settings)
        text, keyboard = screen_words(settings, code, False)
        return text, keyboard, "Список очищен"

    if action == "num":
        text, keyboard = screen_numbers(settings)
        return text, keyboard, ""

    if action == "n" and parts[1] in NUMBERS:
        code = parts[1]
        key, title, minimum, example = NUMBERS[code]
        menu["pending"] = {"action": "set_number", "code": code}
        text, keyboard = screen_prompt(
            "🔢 <b>{}</b>\nСейчас: {}\n\nНапишите новое значение числом, например <i>{}</i>."
            .format(title, format_number(settings[key]), example))
        return text, keyboard, ""

    if action == "rub" or action == "rg" or action == "rt":
        rubrics = get_rubrics(menu)
        if rubrics is None:
            text, keyboard = screen_error("Не удалось загрузить список рубрик с Kwork. Попробуйте позже.")
            return text, keyboard, ""

        if action == "rub":
            text, keyboard = screen_rubric_groups(settings, rubrics)
            return text, keyboard, ""
        if action == "rg":
            text, keyboard = screen_rubric_children(settings, rubrics, parts[1])
            return text, keyboard, ""

        toast = toggle_rubric(settings, parts[1], conn)
        text, keyboard = screen_rubric_children(settings, rubrics, parts[2])
        return text, keyboard, toast

    text, keyboard = screen_main(settings)
    return text, keyboard, "Кнопка устарела"


def handle_text_input(text, settings, menu):
    """Обрабатывает текст, который бот попросил написать (новые слова, число).
    Возвращает (текст, кнопки) — новый экран меню."""
    pending = menu.get("pending")
    if not pending:
        return ("Чтобы поменять настройки, нажмите /settings", None)

    if pending["action"] == "add_words":
        code = pending["code"]
        key = WORD_LISTS[code][0]
        added = []
        for word in clean_words(text.split(",")):
            if word not in settings[key]:
                settings[key].append(word)
                added.append(word)
        save_settings(settings)
        menu["pending"] = None

        screen_text, keyboard = screen_words(settings, code, False)
        if added:
            note = "✅ Добавил: {}".format(format_word_list(added))
        else:
            note = "Эти слова уже есть в списке."
        return note + "\n\n" + screen_text, keyboard

    if pending["action"] == "edit_word":
        code = pending["code"]
        key = WORD_LISTS[code][0]
        old_word = pending["word"]
        new_word = text.strip().lower()
        if not new_word:
            return screen_prompt("Пустое слово не подойдёт. Напишите замену или нажмите «Отмена».")

        menu["pending"] = None
        if old_word in settings[key]:
            position = settings[key].index(old_word)
            if new_word in settings[key]:
                settings[key].remove(old_word)
            else:
                settings[key][position] = new_word
            save_settings(settings)
            note = "✅ Заменил: {} → {}".format(html.escape(old_word), html.escape(new_word))
        else:
            note = "Слова «{}» уже нет в списке.".format(html.escape(old_word))
        screen_text, keyboard = screen_words(settings, code, False)
        return note + "\n\n" + screen_text, keyboard

    if pending["action"] == "set_number":
        key, title, minimum, example = NUMBERS[pending["code"]]
        try:
            value = float(text.replace(",", ".").replace(" ", ""))
        except ValueError:
            return screen_prompt("Нужно число, например <i>{}</i>. Попробуйте ещё раз или нажмите «Отмена».".format(example))
        if value < minimum:
            return screen_prompt("Значение должно быть не меньше {}. Попробуйте ещё раз.".format(minimum))

        # Для интервала дробные минуты допустимы, остальное — целые числа.
        if key != "interval_min" or value == int(value):
            value = int(value)
        settings[key] = value
        save_settings(settings)
        menu["pending"] = None

        note = "✅ {}: {}".format(title, format_number(value))
        if key == "interval_min":
            note += "\nНовый интервал начнёт действовать после ближайшей проверки."
        screen_text, keyboard = screen_numbers(settings)
        return note + "\n\n" + screen_text, keyboard

    menu["pending"] = None
    return ("Чтобы поменять настройки, нажмите /settings", None)


def process_updates(token, chat_id, settings, conn, menu, env_interval, wait_seconds):
    """Забирает сообщения и нажатия кнопок и отвечает на них.
    Номер последнего обработанного сообщения хранится в menu["offset"]."""
    updates = get_updates(token, menu["offset"], wait_seconds)
    if updates:
        # Вдруг config.py поправили вручную — показываем и меняем актуальные настройки.
        reload_if_changed(settings, env_interval)

    for update in updates:
        menu["offset"] = update["update_id"] + 1
        try:
            if "callback_query" in update:
                process_callback(token, chat_id, settings, conn, menu, update["callback_query"])
            elif "message" in update:
                process_message(token, chat_id, settings, menu, update["message"])
        except Exception:
            log.exception("Ошибка при обработке сообщения от Telegram")
            send_telegram(token, chat_id, "Ошибка при выполнении, подробности в monitor.log")


def is_my_chat(chat, chat_id):
    """Настройки меняются только из вашего чата — чужих не слушаем."""
    sender_chat = str((chat or {}).get("id"))
    if sender_chat != str(chat_id):
        log.warning("Сообщение из чужого чата %s проигнорировано", sender_chat)
        return False
    return True


def process_callback(token, chat_id, settings, conn, menu, callback):
    message = callback.get("message") or {}
    if not is_my_chat(message.get("chat"), chat_id):
        answer_callback(token, callback["id"])
        return

    data = callback.get("data") or ""
    log.info("Кнопка: %s", data)
    text, keyboard, toast = handle_callback(data, settings, conn, menu)
    answer_callback(token, callback["id"], toast)

    if text is None:
        delete_message(token, chat_id, message.get("message_id"))
    else:
        edit_message(token, chat_id, message.get("message_id"), text, keyboard)


def project_date(project):
    """Ключ сортировки: дата публикации проекта ("2026-10-30 10:57:04")."""
    return project["date_active"]


def send_all_projects(token, chat_id, settings):
    """Команда /all: все проекты с первых страниц рубрик, которые подходят под фильтры,
    в том числе уже увиденные. Новые — сверху."""
    category_items = list(settings["categories"].items())
    if not category_items:
        send_telegram(token, chat_id, "Рубрик нет — нечего показывать. Добавьте их в /settings → Рубрики.")
        return

    send_telegram(token, chat_id, "⏳ Собираю проекты из рубрик: {}…".format(len(category_items)))

    projects = []
    seen_ids = []
    errors = []
    for index, (category_id, category_name) in enumerate(category_items):
        if index > 0:
            time.sleep(random.uniform(1, 2))
        try:
            page_projects = extract_projects(fetch_page(int(category_id)))
        except (requests.RequestException, ValueError) as error:
            log.error("/all: рубрика «%s»: %s", category_name, error)
            errors.append(category_name)
            continue
        # Один проект может оказаться сразу в двух рубриках — не дублируем.
        for project in page_projects:
            if project["id"] not in seen_ids:
                seen_ids.append(project["id"])
                projects.append(project)

    matching = []
    for project in projects:
        if check_filters(project, settings) is None:
            matching.append(project)
    matching.sort(key=project_date, reverse=True)

    shown = matching[:ALL_COMMAND_LIMIT]
    for project in shown:
        send_telegram(token, chat_id, format_message(project, settings))

    lines = []
    if not projects and errors and len(errors) == len(category_items):
        lines.append("⚠️ Не удалось загрузить ни одной рубрики — Kwork недоступен. Попробуйте позже.")
    elif not projects:
        lines.append("📭 В ваших рубриках сейчас нет ни одного активного проекта.")
    elif not matching:
        lines.append("📭 Подходящих проектов нет: все {} на первых страницах рубрик "
                     "отсеяны фильтрами. Ослабить их можно в /settings.".format(len(projects)))
    else:
        lines.append("✅ Подходят под фильтры: {} из {} проектов на первых страницах рубрик.".format(
            len(matching), len(projects)))
        if len(matching) > len(shown):
            lines.append("Показал первые {} — самые свежие.".format(len(shown)))
    if errors and len(errors) < len(category_items):
        lines.append("Не удалось загрузить: {}.".format(html.escape(", ".join(errors))))
    send_telegram(token, chat_id, "\n".join(lines))
    log.info("/all: показано %d из %d подходящих (всего %d)", len(shown), len(matching), len(projects))


def process_message(token, chat_id, settings, menu, message):
    if not is_my_chat(message.get("chat"), chat_id):
        return

    text = (message.get("text") or "").strip()
    if not text:
        return

    if text.startswith("/"):
        menu["pending"] = None
        command = text.split()[0].split("@")[0].lower()
        log.info("Команда: %s", command)
        if command == "/settings":
            screen_text, keyboard = screen_main(settings)
            send_telegram(token, chat_id, screen_text, keyboard)
        elif command == "/all":
            send_all_projects(token, chat_id, settings)
        else:
            send_telegram(token, chat_id, HELP_TEXT)
        return

    log.info("Ввод: %s", text[:100])
    screen_text, keyboard = handle_text_input(text, settings, menu)
    send_telegram(token, chat_id, screen_text, keyboard)


# ---------- База увиденных проектов ----------

def open_db():
    conn = sqlite3.connect(DB_PATH)
    conn.execute("CREATE TABLE IF NOT EXISTS seen (id INTEGER PRIMARY KEY, first_seen TEXT)")
    conn.commit()
    return conn


def db_is_empty(conn):
    row = conn.execute("SELECT COUNT(*) FROM seen").fetchone()
    return row[0] == 0


def is_seen(conn, project_id):
    row = conn.execute("SELECT 1 FROM seen WHERE id = ?", (project_id,)).fetchone()
    return row is not None


def mark_seen(conn, project_id):
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    conn.execute("INSERT OR IGNORE INTO seen (id, first_seen) VALUES (?, ?)", (project_id, now))
    conn.commit()


# ---------- Основная логика ----------

def check_once(conn, token, chat_id, settings, pause):
    """Одна проверка всех рубрик. Возвращает, сколько всего проектов нашлось на страницах.
    pause(секунды) — чем заполнить паузу между рубриками (в боте — ответами на кнопки)."""
    first_run = db_is_empty(conn)
    if first_run:
        log.info("Первый запуск: запоминаю текущие проекты, уведомления не отправляю")

    total_found = 0
    sent_count = 0
    # Копия списка: рубрики могут поменяться кнопками, пока идёт проверка.
    category_items = list(settings["categories"].items())

    for index, (category_id, category_name) in enumerate(category_items):
        # Небольшая пауза между рубриками, чтобы не бомбить сайт запросами.
        if index > 0:
            pause(random.uniform(3, 8))

        try:
            page_html = fetch_page(int(category_id))
            projects = extract_projects(page_html)
        except requests.RequestException as error:
            log.error("Рубрика «%s»: ошибка сети: %s", category_name, error)
            continue
        except ValueError as error:
            log.error("Рубрика «%s»: %s", category_name, error)
            continue

        total_found += len(projects)

        new_projects = []
        for project in projects:
            if not is_seen(conn, project["id"]):
                new_projects.append(project)

        log.info("Рубрика «%s»: на странице %d, новых %d", category_name, len(projects), len(new_projects))

        if not first_run and projects and len(new_projects) == len(projects):
            log.warning(
                "Рубрика «%s»: все %d проектов на первой странице новые — "
                "часть могла уйти на вторую страницу, интервал проверки великоват",
                category_name, len(projects),
            )

        for project in new_projects:
            if first_run:
                mark_seen(conn, project["id"])
                continue

            reason = check_filters(project, settings)
            if reason:
                log.info("  пропуск %s «%s»: %s", project["id"], project["name"][:60], reason)
                mark_seen(conn, project["id"])
                continue

            if send_telegram(token, chat_id, format_message(project, settings)):
                log.info("  отправлен %s «%s»", project["id"], project["name"][:60])
                mark_seen(conn, project["id"])
                sent_count += 1
            else:
                # Не помечаем как увиденный — попробуем отправить при следующей проверке.
                log.warning("  не удалось отправить %s, повторю позже", project["id"])

    log.info("Проверка завершена: найдено %d, отправлено %d", total_found, sent_count)
    return total_found


def run_forever(token, chat_id, env_interval):
    conn = open_db()
    settings = load_settings(env_interval)
    set_bot_commands(token)
    log.info("Монитор запущен. Рубрик: %d, интервал: %s мин. Настройки и база: %s",
             len(settings["categories"]), format_number(settings["interval_min"]), DATA_DIR)

    # Состояние меню: чего бот ждёт от вас сообщением, кэш списка рубрик
    # и номер последнего обработанного сообщения Telegram.
    menu = {"pending": None, "rubrics": None, "offset": None}

    def listen(seconds):
        """Ждёт столько секунд и всё это время отвечает на кнопки и сообщения."""
        deadline = time.time() + seconds
        while True:
            left = deadline - time.time()
            if left <= 0:
                return
            if left < 1:
                time.sleep(left)
                return
            try:
                process_updates(token, chat_id, settings, conn, menu, env_interval, int(min(POLL_SECONDS, left)))
            except Exception:
                log.exception("Неожиданная ошибка при обработке Telegram")
                time.sleep(min(5, left))

    empty_checks = 0
    while True:
        reload_if_changed(settings, env_interval)
        try:
            found = check_once(conn, token, chat_id, settings, listen)
        except Exception:
            # Любая неожиданная ошибка не должна ронять бота.
            log.exception("Неожиданная ошибка при проверке")
            found = 0

        if not settings["categories"]:
            log.warning("Рубрик нет — проверять нечего")
        elif found == 0:
            empty_checks += 1
            log.warning("Проектов не найдено (%d раз подряд)", empty_checks)
            if empty_checks == EMPTY_CHECKS_LIMIT:
                send_telegram(
                    token, chat_id,
                    "⚠️ Монитор Kwork: {} проверки подряд не нашли ни одного проекта. "
                    "Возможно, сайт недоступен или сменилась разметка. "
                    "Посмотрите monitor.log.".format(EMPTY_CHECKS_LIMIT),
                )
        else:
            if empty_checks >= EMPTY_CHECKS_LIMIT:
                send_telegram(token, chat_id, "✅ Монитор Kwork снова находит проекты.")
            empty_checks = 0

        delay = settings["interval_min"] * 60 + random.uniform(0, 60)
        log.info("Следующая проверка через %d сек", delay)
        listen(delay)


def dry_run(page_path):
    """Разбирает сохранённую страницу и печатает, что было бы отправлено."""
    if not os.path.exists(page_path):
        print("Файл не найден: {}".format(page_path))
        return

    with open(page_path, encoding="utf-8") as page_file:
        page_html = page_file.read()

    try:
        projects = extract_projects(page_html)
    except ValueError as error:
        print("Ошибка разбора: {}".format(error))
        return

    _, _, env_interval = read_env()
    try:
        settings = load_settings(env_interval)
    except ValueError as error:
        print("Ошибка: {}".format(error))
        return

    print("Проектов на странице: {}\n".format(len(projects)))
    passed = 0
    for project in projects:
        reason = check_filters(project, settings)
        if reason:
            print("✗ ПРОПУСК {} «{}»: {}".format(project["id"], project["name"], reason))
            continue
        passed += 1
        print("✓ ОТПРАВИЛ БЫ:")
        print("-" * 60)
        print(format_message(project, settings))
        print("-" * 60)
    print("\nПодходит под фильтры: {} из {}".format(passed, len(projects)))


def main():
    # Чтобы русский текст и эмодзи нормально печатались в консоли Windows.
    try:
        sys.stdout.reconfigure(encoding="utf-8")
        sys.stderr.reconfigure(encoding="utf-8")
    except AttributeError:
        pass

    parser = argparse.ArgumentParser(description="Монитор новых проектов Kwork")
    parser.add_argument("--dry-run", nargs="?", const=SAMPLE_PAGE_PATH, metavar="HTML",
                        help="разобрать сохранённую страницу (по умолчанию sample_page.html)")
    parser.add_argument("--test-telegram", action="store_true",
                        help="отправить тестовое сообщение в Telegram")
    args = parser.parse_args()

    if args.dry_run:
        dry_run(args.dry_run)
        return

    setup_logging()
    token, chat_id, env_interval = read_env()
    if not token or not chat_id:
        log.error("Не заданы токен бота и chat_id. Локально — впишите TELEGRAM_TOKEN и TELEGRAM_CHAT_ID в .env. "
                  "На хостинге — заполните поле Bot Token и добавьте переменную окружения TELEGRAM_CHAT_ID.")
        sys.exit(1)

    if args.test_telegram:
        if send_telegram(token, chat_id, "✅ Тестовое сообщение от монитора Kwork. Токен работает."):
            log.info("Тестовое сообщение отправлено")
        else:
            sys.exit(1)
        return

    instance_lock = lock_single_instance()
    if instance_lock is None:
        log.error("Бот уже запущен на этом компьютере (в PyCharm или в консоли). "
                  "Вторая копия не запускается. Остановите прежнюю (в PyCharm — кнопка Stop) "
                  "и запустите снова.")
        sys.exit(1)

    try:
        run_forever(token, chat_id, env_interval)
    except KeyboardInterrupt:
        log.info("Остановлено пользователем")
    except ValueError as error:
        # config.py испорчен при запуске — без настроек работать нельзя.
        log.error("Бот не запущен: %s", error)
        sys.exit(1)


if __name__ == "__main__":
    main()
