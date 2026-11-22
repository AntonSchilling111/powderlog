#!/usr/bin/env python3
"""
Powderlog Update-Agent
----------------------
Aktualisiert data.json:
  geo     -> Lifte und Pisten aus OpenStreetMap (Overpass API, ODbL: Quelle "OpenStreetMap-Mitwirkende" nennen)
  weather -> Wetter, Wind, Nullgradgrenze, Neuschnee (Modell) und Windfenster via Open-Meteo
  snow    -> gemessene Schneehöhe (Tal/Berg) von Tourismus-/Skigebiets-Seiten (Textextraktion, siehe SNOW_SOURCES);
             Sölden zusätzlich Stationswerte (Schneehöhe/Temperatur je Livecam-Standort, siehe SNOW_STATION_SOURCES)
  avalanche -> Lawinenlagebericht (EAWS/CAAMLv5-XML) für Salzburg (AT-05), Tirol (AT-07), Vorarlberg (AT-08)

Nutzung:
  python update_agent.py --file data.json --only weather
  python update_agent.py --file data.json --only geo
  python update_agent.py --file data.json --only snow
  python update_agent.py --file data.json --only avalanche
  python update_agent.py --file data.json --only lifts     # Liftstatus (offen/geschlossen), derzeit nur Arlberg
  python update_agent.py --file data.json --only webcams   # prüft nur, ob die Webcam-Seiten erreichbar sind
  python update_agent.py --probe AT-05               # Regions-IDs + Stufen des heutigen Berichts anzeigen
  python update_agent.py --file data.json            # alles
  python update_agent.py --file data.json --dry-run  # nichts schreiben

Empfohlener Takt (cron):
  0 * * * *   python update_agent.py --file /pfad/data.json --only weather
  0 4 * * 1   python update_agent.py --file /pfad/data.json --only geo
  */15 8-17 * * *  python update_agent.py --file /pfad/data.json --only lifts   # Liftstatus tagsüber
  15 */3 * * *   python update_agent.py --file /pfad/data.json --only snow   # höchstens alle 3 h abrufen
  30 17,18 * * * python update_agent.py --file /pfad/data.json --only avalanche   # Berichte kommen abends
  30 6,7 * * *   python update_agent.py --file /pfad/data.json --only avalanche   # Vorarlberg/Updates morgens

Hinweise:
  * Nur Python-Standardbibliothek, Python 3.9+.
  * Open-Meteo-Schnee ist ein MODELLWERT, kein Messwert vom Skigebiet. Er landet in snow.model,
    die Felder base_cm/summit_cm (Messwerte vom Skigebiet) bleiben unberührt.
  * Unbekanntes bleibt null. Es werden keine Werte erfunden.
  * Bitte USER_AGENT mit echter Kontaktadresse versehen (Höflichkeit gegenüber Overpass/Open-Meteo).
"""
import argparse
import html
import json
import math
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import urllib.robotparser
import unicodedata
from html.parser import HTMLParser
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta

USER_AGENT = "Powderlog-Agent/1.0 (kontakt: %s)" % os.environ.get("POWDERLOG_CONTACT", "deine@mail.example")
try:
    from zoneinfo import ZoneInfo
    TZ = ZoneInfo("Europe/Vienna")
except Exception:  # z. B. Windows ohne Paket "tzdata": einfache MEZ/MESZ-Regel als Ersatz
    from datetime import tzinfo

    class _Vienna(tzinfo):
        @staticmethod
        def _last_sunday(year, month):
            d = datetime(year, month, 31)
            return d - timedelta(days=(d.weekday() + 1) % 7)

        def _dst_local(self, dt):
            n = dt.replace(tzinfo=None)
            return self._last_sunday(n.year, 3).replace(hour=2) <= n < self._last_sunday(n.year, 10).replace(hour=3)

        def utcoffset(self, dt):
            return timedelta(hours=2 if self._dst_local(dt) else 1)

        def dst(self, dt):
            return timedelta(hours=1 if self._dst_local(dt) else 0)

        def tzname(self, dt):
            return "CEST" if self._dst_local(dt) else "CET"

        def fromutc(self, dt):
            n = dt.replace(tzinfo=None)
            on = self._last_sunday(n.year, 3).replace(hour=1) <= n < self._last_sunday(n.year, 10).replace(hour=1)
            return (n + timedelta(hours=2 if on else 1)).replace(tzinfo=self)

    TZ = _Vienna()
OVERPASS_URL = "https://overpass-api.de/api/interpreter"
OPEN_METEO_URL = "https://api.open-meteo.com/v1/forecast"

# Suchrechtecke (süd, west, nord, ost). Bei Bedarf anpassen.
BBOX = {
    "obertauern": (47.20, 13.48, 47.30, 13.65),
    "arlberg": (47.08, 10.05, 47.28, 10.35),
    "soelden": (46.90, 10.90, 47.03, 11.12),
    "zillertal": (47.05, 11.60, 47.36, 12.15),
}

LIFT_TYPES = {
    "gondola": "gondola",
    "cable_car": "cable_car",
    "chair_lift": "chairlift",
    "mixed_lift": "chairlift",
    "drag_lift": "drag",
    "t-bar": "drag",
    "j-bar": "drag",
    "platter": "drag",
    "magic_carpet": "drag",
}
PISTE_DIFFICULTY = {
    "novice": "blue",
    "easy": "blue",
    "intermediate": "red",
    "advanced": "black",
    "expert": "black",
    "freeride": "skiroute",
}

GUST_LIMIT_KMH = 40   # Windfenster: Böen unter diesem Wert
WINDOW_HOURS = 4      # Mindestlänge des Fensters
DAY_START, DAY_END = 8, 16


# ---------- HTTP ----------

def http(url, data=None, retries=3, timeout=120):
    req = urllib.request.Request(url, data=data, headers={"User-Agent": USER_AGENT})
    last = None
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode("utf-8"))
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as e:
            last = e
            time.sleep(2 ** attempt)
    raise RuntimeError(f"Abruf fehlgeschlagen: {url[:80]} ({last})")


def http_bytes(url, timeout=60):
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def fetch_overpass(bbox):
    s, w, n, e = bbox
    types = "|".join(LIFT_TYPES)
    q = f"""[out:json][timeout:90];
(
  way["aerialway"~"^({types})$"]({s},{w},{n},{e});
  way["piste:type"="downhill"]({s},{w},{n},{e});
);
out tags geom;"""
    return http(OVERPASS_URL, data=urllib.parse.urlencode({"data": q}).encode())


def fetch_open_meteo(lat, lon, elevation):
    params = {
        "latitude": lat,
        "longitude": lon,
        "elevation": elevation,
        "hourly": "temperature_2m,wind_speed_10m,wind_gusts_10m,freezing_level_height,snowfall,snow_depth",
        "wind_speed_unit": "kmh",
        "past_days": 3,
        "forecast_days": 3,
        "timezone": "Europe/Vienna",
    }
    return http(OPEN_METEO_URL + "?" + urllib.parse.urlencode(params))


# ---------- Geo (Lifte, Pisten) ----------

def haversine_km(a, b):
    r = 6371.0
    p1, p2 = math.radians(a[0]), math.radians(b[0])
    dp = p2 - p1
    dl = math.radians(b[1] - a[1])
    h = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(h))


def line_length_km(points):
    return sum(haversine_km(points[i], points[i + 1]) for i in range(len(points) - 1))


def parse_ele(tags):
    try:
        return float(str(tags.get("ele", "")).replace(",", ".").split()[0])
    except (ValueError, IndexError):
        return None


def convert_osm(elements):
    lifts, pistes = [], []
    for el in elements:
        tags = el.get("tags", {})
        geom = [[g["lat"], g["lon"]] for g in el.get("geometry", [])]
        if len(geom) < 2:
            continue
        osm_id = el["id"]
        name = tags.get("name") or tags.get("ref") or None
        if "aerialway" in tags and tags["aerialway"] in LIFT_TYPES:
            lifts.append({
                "id": f"osm-{osm_id}",
                "name": name,
                "type": LIFT_TYPES[tags["aerialway"]],
                "bottom": {"lat": geom[0][0], "lon": geom[0][1], "elevation": None},
                "top": {"lat": geom[-1][0], "lon": geom[-1][1], "elevation": None},
                "geometry": geom,
                "osm_id": osm_id,
            })
        elif tags.get("piste:type") == "downhill":
            pistes.append({
                "id": f"osm-{osm_id}",
                "name": name,
                "difficulty": PISTE_DIFFICULTY.get(tags.get("piste:difficulty"), None),
                "geometry": geom,
                "length_km": round(line_length_km(geom), 2),
                "osm_id": osm_id,
            })
    return lifts, pistes


def merge_by_id(existing, fresh):
    """Neue OSM-Daten übernehmen, Live-Felder (status, groomed_at, updated_at) bestehender Einträge behalten."""
    old = {e["id"]: e for e in existing}
    out = []
    for f in fresh:
        o = old.get(f["id"], {})
        merged = {**o, **f}
        merged.setdefault("status", "unknown")
        merged.setdefault("updated_at", None)
        if "groomed_at" in o:
            merged["groomed_at"] = o["groomed_at"]
        out.append(merged)
    return out


def update_geo(resort):
    bbox = BBOX.get(resort["id"])
    if not bbox:
        raise RuntimeError("Keine BBOX definiert")
    lifts, pistes = convert_osm(fetch_overpass(bbox).get("elements", []))
    resort["lifts"] = merge_by_id(resort.get("lifts", []), lifts)
    resort["pistes"] = merge_by_id(resort.get("pistes", []), pistes)
    return f"{len(lifts)} Lifte, {len(pistes)} Pisten"


# ---------- Wetter ----------

def now_index(times, now):
    """Index der letzten vollen Stunde <= jetzt."""
    cur = now.replace(minute=0, second=0, microsecond=0).strftime("%Y-%m-%dT%H:%M")
    idx = None
    for i, t in enumerate(times):
        if t <= cur:
            idx = i
        else:
            break
    return idx


def sum_window(values, end_idx, hours):
    vals = values[max(0, end_idx - hours + 1): end_idx + 1]
    vals = [v for v in vals if v is not None]
    return round(sum(vals), 1) if vals else None


def find_window(times, gusts, start_idx):
    """Erster Zeitraum >= WINDOW_HOURS zwischen DAY_START und DAY_END mit Böen < GUST_LIMIT in den nächsten 48 h."""
    run = []
    for i in range(start_idx, min(len(times), start_idx + 48)):
        hour = int(times[i][11:13])
        g = gusts[i]
        ok = g is not None and g < GUST_LIMIT_KMH and DAY_START <= hour <= DAY_END
        same_day = not run or times[i][:10] == times[run[-1]][:10]
        if ok and same_day:
            run.append(i)
        else:
            if len(run) >= WINDOW_HOURS:
                break
            run = [i] if ok else []
    if len(run) >= WINDOW_HOURS:
        return {"from": times[run[0]], "to": times[run[-1]], "max_gust": max(gusts[i] for i in run)}
    return None


def at(values, idx):
    return values[idx] if idx is not None and idx < len(values) else None


def _weather_open_meteo(resort, now=None):
    now = now or datetime.now(TZ)
    elev = resort["elevation"]
    c = resort["center"]
    base = fetch_open_meteo(c["lat"], c["lon"], elev["min"])["hourly"]
    summit = fetch_open_meteo(c["lat"], c["lon"], elev["max"])["hourly"]

    ib = now_index(base["time"], now)
    isu = now_index(summit["time"], now)
    if ib is None or isu is None:
        raise RuntimeError("Keine passende Stunde in der Antwort")

    resort["weather"] = {
        "temp_base": at(base["temperature_2m"], ib),
        "temp_summit": at(summit["temperature_2m"], isu),
        "wind_summit": at(summit["wind_speed_10m"], isu),
        "gusts": at(summit["wind_gusts_10m"], isu),
        "freezing_level": at(summit["freezing_level_height"], isu),
        "forecast_window": find_window(summit["time"], summit["wind_gusts_10m"], isu),
        "updated_at": now.isoformat(timespec="minutes"),
    }

    def depth_cm(h, i):
        d = at(h["snow_depth"], i)
        return None if d is None else round(d * 100)

    resort.setdefault("snow", {})["model"] = {
        "source": "Open-Meteo Modell (kein Messwert vom Skigebiet)",
        "base_cm": depth_cm(base, ib),
        "summit_cm": depth_cm(summit, isu),
        "new_24h_cm": sum_window(summit["snowfall"], isu, 24),
        "new_72h_cm": sum_window(summit["snowfall"], isu, 72),
        "updated_at": now.isoformat(timespec="minutes"),
    }
    w = resort["weather"]
    return f"Gipfel {w['temp_summit']} °C, Böen {w['gusts']} km/h, Fenster: {w['forecast_window']}"


def fetch_open_meteo_daily(lat, lon, elevation):
    params = {
        "latitude": lat, "longitude": lon, "elevation": elevation,
        "daily": "snowfall_sum,precipitation_probability_max,temperature_2m_max,temperature_2m_min",
        "forecast_days": 7, "timezone": "Europe/Vienna",
    }
    return http(OPEN_METEO_URL + "?" + urllib.parse.urlencode(params))


def update_forecast(resort, now=None):
    """7-Tage-Vorhersage mit erwarteter Neuschneemenge in cm (Tal = Talstation, Berg = Gipfelbereich)."""
    now = now or datetime.now(TZ)
    c, e = resort["center"], resort["elevation"]
    b = fetch_open_meteo_daily(c["lat"], c["lon"], e["min"])["daily"]
    sm = fetch_open_meteo_daily(c["lat"], c["lon"], e["max"])["daily"]
    wd = ["Mo", "Di", "Mi", "Do", "Fr", "Sa", "So"]
    probs = b.get("precipitation_probability_max") or [None] * len(b["time"])
    days = []
    for i in range(min(len(b["time"]), len(sm["time"]))):
        dt = datetime.strptime(b["time"][i], "%Y-%m-%d")
        sb, ss = b["snowfall_sum"][i], sm["snowfall_sum"][i]
        days.append({"date": b["time"][i], "d": f"{wd[dt.weekday()]} {dt.day:02d}.{dt.month:02d}.",
                     "hi": b["temperature_2m_max"][i], "lo": b["temperature_2m_min"][i], "p": probs[i],
                     "t": "snow" if (sb or 0) > 0 or (ss or 0) > 0 else "precip",
                     "snow_base_cm": sb, "snow_summit_cm": ss})
    resort["forecast"] = {
        "place": resort["name"], "source": "Open-Meteo", "asof": now.strftime("%d.%m.%Y"), "current": None,
        "note": "Neuschnee in cm Höhe (Tal = Talstation, Berg = Gipfelbereich). Faustregel: 1 cm Neuschnee ≈ 1 l/m² Wasser (Pulver weniger).",
        "daily": days, "updated_at": now.isoformat(timespec="minutes")}
    resort.pop("forecast_error", None)
    tot = sum((d["snow_summit_cm"] or 0) for d in days)
    return f"{len(days)} Tage, Neuschnee Berg gesamt {tot:g} cm"


MET_URL = "https://api.met.no/weatherapi/locationforecast/2.0/complete"


def fetch_met(lat, lon, altitude):
    """MET Norway Locationforecast (Ersatzquelle). Verlangt einen identifizierenden User-Agent (POWDERLOG_CONTACT setzen)."""
    q = urllib.parse.urlencode({"lat": round(lat, 4), "lon": round(lon, 4), "altitude": int(altitude)})
    return http(MET_URL + "?" + q)


def _weather_met(resort, now=None):
    now = now or datetime.now(TZ)
    c, elev = resort["center"], resort["elevation"]

    def rows(data):
        out = []
        for e in data["properties"]["timeseries"]:
            d = e["data"]["instant"]["details"]
            t = datetime.fromisoformat(e["time"].replace("Z", "+00:00")).astimezone(TZ)
            ws, g = d.get("wind_speed"), d.get("wind_speed_of_gust")
            out.append((t, d.get("air_temperature"), None if ws is None else round(ws * 3.6, 1), None if g is None else round(g * 3.6, 1)))
        return out

    rb, rs = rows(fetch_met(c["lat"], c["lon"], elev["min"])), rows(fetch_met(c["lat"], c["lon"], elev["max"]))

    def current(rws):
        past = [r for r in rws if r[0] <= now]
        if not past:
            raise RuntimeError("MET Norway: keine passende Stunde in der Antwort")
        return past[-1]

    b, su = current(rb), current(rs)
    start = now.replace(minute=0, second=0, microsecond=0)
    nxt = [r for r in rs if start <= r[0] <= now + timedelta(hours=48)]
    resort["weather"] = {
        "temp_base": b[1], "temp_summit": su[1], "wind_summit": su[2], "gusts": su[3],
        "freezing_level": None,   # liefert MET Norway nicht
        "forecast_window": find_window([r[0].strftime("%Y-%m-%dT%H:%M") for r in nxt], [r[3] for r in nxt], 0),
        "updated_at": now.isoformat(timespec="minutes"),
    }
    w = resort["weather"]
    return f"Gipfel {w['temp_summit']} °C, Böen {w['gusts']} km/h, Fenster: {w['forecast_window']}"


def update_weather(resort, now=None):
    """Open-Meteo zuerst, bei Fehler MET Norway als Ersatz. Die verwendete Quelle steht in weather.source."""
    now = now or datetime.now(TZ)
    errors = []
    for name, fn in (("Open-Meteo", _weather_open_meteo), ("MET Norway", _weather_met)):
        try:
            msg = fn(resort, now)
        except Exception as e:
            errors.append(f"{name}: {e}")
            continue
        resort["weather"]["source"] = name
        resort["weather"]["source_note"] = ("Ersatzquelle, weil " + " | ".join(errors)) if errors else None
        try:   # Vorhersage mit Neuschnee-Mengen: eigener Abruf, darf das Wetter nicht scheitern lassen
            fmsg = update_forecast(resort, now)
        except Exception as e:
            resort["forecast_error"] = str(e)
            fmsg = f"Vorhersage FEHLER: {e}"
        return msg + f" [Quelle: {name}" + (", Ersatz" if errors else "") + f"] | {fmsg}"
    raise RuntimeError("Alle Wetterquellen fehlgeschlagen: " + " | ".join(errors))


# ---------- Hooks (noch offen) ----------

def update_webcams(resort, now=None):
    """Prüft, ob die hinterlegten Webcam-Seiten erreichbar sind (ok=true/false, null = robots.txt verbietet Abruf)."""
    now = now or datetime.now(TZ)
    cams = resort.get("webcams", [])
    if not cams:
        raise RuntimeError("keine Webcams hinterlegt")
    status = {}
    for url in sorted({c["page_url"] for c in cams if c.get("page_url")}):
        try:
            if not robots_allows(url):
                status[url] = None
            else:
                http_bytes(url, timeout=30)
                status[url] = True
        except Exception:
            status[url] = False
        time.sleep(1)
    for c in cams:
        c["ok"] = status.get(c.get("page_url"))
        c["last_checked"] = now.isoformat(timespec="minutes")
    bad = [u for u, v in status.items() if v is False]
    msg = f"{len(cams)} Webcams, {len(status)} Seiten geprüft"
    if bad:
        raise RuntimeError(msg + f", nicht erreichbar: {bad}")
    return msg


# ---------- Gemessene Schneehöhe ----------
# Es gibt keine offene Schnittstelle für Skigebiets-Messwerte. Der Agent liest deshalb die Texte öffentlicher
# Schneebericht-Seiten (Label "Schneehöhe Tal/Berg" + Zahl + cm). Das ist anfällig für Seitenänderungen:
#  - Ohne passende Zahl wird NICHTS erfunden (Wert bleibt null / alter Wert wird als stale markiert).
#  - robots.txt wird beachtet, Abruf höchstens alle paar Stunden (cron).
#  - Vor dem Produktiveinsatz Nutzungsbedingungen der Seiten prüfen bzw. Betreiber um eine Datenschnittstelle bitten.
# Quellen sind pro Skigebiet in data.json unter snow.sources überschreibbar.

SNOW_SOURCES = {
    "obertauern": [{"name": "Tourismusverband Obertauern", "url": "https://www.obertauern.com/en/snow-report.html",
                    "note": "Durchschnittswerte für das gesamte Skigebiet laut Betreiber"}],
    "arlberg": [
        {"area": "St. Anton (Tirol)", "name": "Tirol Werbung (St. Anton)",
         "url": "https://www.tirol.at/reiseservice/schneehoehen/schneehoehen-st-anton", "note": None},
        {"area": "Lech Zürs (Vorarlberg)", "name": "Lech Zürs Tourismus",
         "url": "https://www.lechzuers.com/en/snow-report", "note": "Werte für das Skigebiet Lech Zürs"},
    ],
    "zillertal": [
        {"area": "Mayrhofen (Penken/Ahorn)", "name": "Tirol Werbung (Mayrhofen)",
         "url": "https://www.tirol.at/orte/a-mayrhofen/schneehoehen", "note": None},
        {"area": "Zell-Gerlos (Zillertal Arena)", "name": "Tirol Werbung (Zell am Ziller)",
         "url": "https://www.tirol.at/reiseservice/schneehoehen/schneehoehen-zell-am-ziller", "note": None},
    ],
    "soelden": [{"name": "Tirol Werbung (Sölden)", "url": "https://www.tirol.at/reiseservice/schneehoehen/schneehoehen-soelden",
                 "note": None}],
}

_NUM = r"(\d{1,3}(?:[.,]\d)?)\s*cm"
RE_BERG = re.compile(r"Schneeh[öo]he\s+(?:am\s+|auf\s+dem\s+)?Berg\s*:?\s*" + _NUM, re.I)
RE_TAL = re.compile(r"Schneeh[öo]he\s+(?:im\s+)?Tal\s*:?\s*" + _NUM, re.I)
RE_NEU = re.compile(r"Neuschnee\s+(?:am\s+)?Berg\s*:?\s*" + _NUM, re.I)
_NUM_OPT = r"(\d{1,3}(?:[.,]\d)?)(?:\s*cm)?\b"
RE_BERG_EN = re.compile(r"Height\s+in\s+the\s+ski\s+area\s*:?\s*" + _NUM_OPT, re.I)
RE_TAL_EN = re.compile(r"Height\s+in\s+the\s+valley\s*:?\s*" + _NUM_OPT, re.I)
RE_NEU_EN = re.compile(r"New\s+snow\s+in\s+the\s+ski\s+area\s*:?\s*" + _NUM_OPT, re.I)
RE_KA = re.compile(r"(?:Schneeh[öo]he[^\d]{0,30}?k\.?\s?A\."
                   r"|Height\s+in\s+the\s+(?:valley|ski\s+area)\s*:?\s*-(?!\s*\d))", re.I)
RE_STAND = re.compile(r"(?:Stand|aktualisiert(?:\s+am)?|Letzte\s+Aktualisierung)\D{0,6}(\d{2})\.(\d{2})\.(\d{4})(?:\D{0,4}(\d{2}):(\d{2}))?", re.I)
MAX_PLAUSIBLE_CM = 1000

_robots_cache = {}


def html_to_text(raw):
    t = raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else raw
    t = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", t, flags=re.S | re.I)
    t = re.sub(r"<[^>]+>", " ", t)
    t = html.unescape(t).replace("\xa0", " ")
    return re.sub(r"\s+", " ", t).strip()


def robots_allows(url):
    parts = urllib.parse.urlsplit(url)
    host = f"{parts.scheme}://{parts.netloc}"
    rp = _robots_cache.get(host)
    if rp is None:
        rp = urllib.robotparser.RobotFileParser()
        try:
            rp.parse(http_bytes(host + "/robots.txt", timeout=20).decode("utf-8", errors="replace").splitlines())
        except urllib.error.HTTPError as e:
            if 400 <= e.code < 500:
                rp.parse([])            # keine robots.txt -> erlaubt
            else:
                rp.parse(["User-agent: *", "Disallow: /"])
        except Exception:
            rp.parse(["User-agent: *", "Disallow: /"])   # im Zweifel nicht abrufen
        _robots_cache[host] = rp
    return rp.can_fetch(USER_AGENT, url)


def _to_cm(m):
    if not m:
        return None
    v = float(m.group(1).replace(",", "."))
    return round(v) if 0 <= v <= MAX_PLAUSIBLE_CM else None


def parse_snow_text(text, tz=TZ):
    """Extrahiert Tal/Berg/Neuschnee. Liefert None, wenn die Seite k.A. meldet; wirft, wenn nichts gefunden wird."""
    def first(*patterns):
        for pat in patterns:
            v = _to_cm(pat.search(text))
            if v is not None:
                return v
        return None

    tal, berg, neu = first(RE_TAL, RE_TAL_EN), first(RE_BERG, RE_BERG_EN), first(RE_NEU, RE_NEU_EN)
    if tal is None and berg is None:
        if RE_KA.search(text):
            return None
        raise RuntimeError("keine Schneehöhen im Seitentext gefunden (Seite geändert, per JavaScript geladen oder keine Meldung)")
    measured_at = None
    m = RE_STAND.search(text)
    if m:
        d, mo, y, hh, mm = m.groups()
        try:
            measured_at = datetime(int(y), int(mo), int(d), int(hh or 0), int(mm or 0), tzinfo=tz).isoformat(timespec="minutes")
        except ValueError:
            measured_at = None
    return {"base_cm": tal, "summit_cm": berg, "new_reported_cm": neu, "measured_at": measured_at}


def _fetch_snow(src):
    url = src["url"]
    if not robots_allows(url):
        raise RuntimeError(f"{url}: laut robots.txt nicht erlaubt")
    return parse_snow_text(html_to_text(http_bytes(url)))


def _update_snow_areas(resort, snow, sources, now):
    """Skigebiete mit mehreren getrennten Teilgebieten (z. B. Arlberg): Werte pro Teilgebiet in snow.areas.
    Top-Level base_cm/summit_cm bleiben null, weil ein Mittelwert über Teilgebiete irreführend wäre."""
    old = {a.get("area"): a for a in snow.get("areas", [])}
    entries, errors = [], []
    for src in sources:
        area = src.get("area") or src["name"]
        entry = {"area": area, "name": src.get("name"), "url": src["url"], "note": src.get("note"),
                 "base_cm": None, "summit_cm": None, "new_reported_cm": None, "measured_at": None,
                 "fetched_at": now.isoformat(timespec="minutes"), "stale": False, "error": None}
        try:
            res = _fetch_snow(src)
            if res:
                entry.update(res)
                if res["measured_at"]:
                    age_h = (now - datetime.fromisoformat(res["measured_at"])).total_seconds() / 3600
                    entry["stale"] = age_h > 48
        except Exception as e:
            errors.append(f"{area}: {e}")
            prev = old.get(area, {})
            entry.update({k: prev.get(k) for k in ("base_cm", "summit_cm", "new_reported_cm", "measured_at")})
            entry.update({"stale": True, "error": str(e)})
        entries.append(entry)
    snow["sources"] = sources
    snow["areas"] = entries
    snow.update({"base_cm": None, "summit_cm": None, "source_name": None, "source_url": None,
                 "fetched_at": now.isoformat(timespec="minutes"), "error": " | ".join(errors) or None})
    summary = "; ".join(f"{e['area']}: Tal {e['base_cm']} / Berg {e['summit_cm']}" for e in entries)
    if errors:
        raise RuntimeError(f"{summary} | FEHLER: {' | '.join(errors)}")
    return summary


def update_measured_snow(resort, now=None):
    now = now or datetime.now(TZ)
    snow = resort.setdefault("snow", {})
    sources = snow.get("sources") or SNOW_SOURCES.get(resort["id"], [])
    if not sources:
        raise RuntimeError("keine Schnee-Quelle konfiguriert")
    if len([x for x in sources if x.get("area")]) >= 2:
        return _update_snow_areas(resort, snow, sources, now)
    errors = []
    for src in sources:
        url = src["url"]
        try:
            if not robots_allows(url):
                errors.append(f"{url}: laut robots.txt nicht erlaubt")
                continue
            res = parse_snow_text(html_to_text(http_bytes(url)))
        except Exception as e:
            errors.append(f"{url}: {e}")
            continue
        snow["sources"] = sources
        snow["source_name"], snow["source_url"], snow["source_note"] = src.get("name"), url, src.get("note")
        snow["fetched_at"] = now.isoformat(timespec="minutes")
        snow["error"] = None
        if res is None:
            snow.update({"base_cm": None, "summit_cm": None, "new_reported_cm": None, "measured_at": None, "stale": False})
            return f"{src.get('name')}: meldet keine Schneehöhen (k.A.)"
        snow.update(res)
        age_h = None
        if res["measured_at"]:
            age_h = (now - datetime.fromisoformat(res["measured_at"])).total_seconds() / 3600
        snow["stale"] = bool(age_h is not None and age_h > 48)
        return f"{src.get('name')}: Tal {res['base_cm']} cm, Berg {res['summit_cm']} cm"
    # Alle Quellen fehlgeschlagen: alte Werte behalten, aber als veraltet markieren
    snow["stale"] = True
    snow["error"] = " | ".join(errors)
    raise RuntimeError(snow["error"])


# ---------- Schneehöhe je Station (Sölden) ----------
# Die Livecam-Seite der Bergbahnen Sölden nennt je Standort Zeit, Temperatur und (nicht überall) Schneehöhe.
# Gespeichert wird je Station; die Top-Level-Werte base_cm/summit_cm bleiben unberührt.

SNOW_STATION_SOURCES = {
    "soelden": {
        "name": "Bergbahnen Sölden (Livecams)",
        "url": "https://www.soelden.com/en/live-information/livecams",
        "areas": ["Sölden", "Gaislachkogl", "Giggijoch", "Glacier"],
        "names": ["Village view", "Gaislachkogl Mid Station", "Gaislachkogl", "Hochsölden", "Giggijoch", "Schwarzkogl Valley",
                  "Seekogl", "Rettenbach Glacier", "Schwarze Schneidbahn Middle Station", "Schwarze Schneidbahn Mid Station",
                  "Tiefenbach Glacier Valley", "Tiefenbach Glacier Mountain"],
    },
}


def parse_station_snow(text, cfg, now):
    areas = "|".join(re.escape(a) for a in cfg["areas"])
    header = rf"(?:{areas}),\s*\d{{3,4}}\s*m"
    card = re.compile(
        rf"(?P<area>{areas}),\s*(?P<elev>\d{{3,4}})\s*m\s+View details"
        rf"(?:(?!{header}).)*?"                      # nie über den Beginn der nächsten Station hinweglesen
        r"(?P<time>\d{1,2}:\d{2})\s+Updated\s+(?P<temp>-?\d+(?:\.\d+)?)\s*°C\s+Temperature"
        r"(?:\s+(?P<snow>\d+(?:\.\d+)?)\s*cm\s+Snow depth)?", re.S)
    out, seen = [], set()
    for m in card.finditer(text):
        key = (m.group("area"), m.group("elev"), m.group("time"))
        if key in seen:
            continue
        seen.add(key)
        before = text[:m.start()].rstrip()
        name = next((n for n in sorted(cfg.get("names", []), key=len, reverse=True) if before.endswith(n)), None)
        hh, mm = (int(x) for x in m.group("time").split(":"))
        ts = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
        if ts > now + timedelta(hours=1):
            ts -= timedelta(days=1)
        snow = float(m.group("snow")) if m.group("snow") else None
        out.append({"name": name, "area": m.group("area"), "elevation": int(m.group("elev")),
                    "temp_c": float(m.group("temp")),
                    "snow_cm": snow if snow is not None and 0 <= snow <= MAX_PLAUSIBLE_CM else None,
                    "measured_at": ts.isoformat(timespec="minutes")})
    return out


def update_snow_stations(resort, now=None):
    now = now or datetime.now(TZ)
    cfg = SNOW_STATION_SOURCES.get(resort["id"])
    if not cfg:
        return "keine Stationsquelle konfiguriert (übersprungen)"
    snow = resort.setdefault("snow", {})
    try:
        if not robots_allows(cfg["url"]):
            raise RuntimeError(f"{cfg['url']}: laut robots.txt nicht erlaubt")
        stations = parse_station_snow(html_to_text(http_bytes(cfg["url"])), cfg, now)
        if not stations:
            raise RuntimeError("keine Stationswerte im Seitentext gefunden (Seite geändert oder per JavaScript geladen)")
    except Exception as e:
        snow["stations_stale"], snow["stations_error"] = True, str(e)
        raise RuntimeError(f"Stationen: {e}")
    snow.update({"stations": stations, "stations_source": cfg["url"], "stations_source_name": cfg["name"],
                 "stations_fetched_at": now.isoformat(timespec="minutes"), "stations_stale": False, "stations_error": None})
    with_snow = [f"{x['elevation']} m: {x['snow_cm']:g} cm" for x in stations if x["snow_cm"] is not None]
    return f"{len(stations)} Stationen, Schneehöhe an {len(with_snow)} ({', '.join(with_snow) or 'keine Meldung'})"


def update_snow(resort, now=None):
    """Gebietswerte (update_measured_snow) und Stationswerte (update_snow_stations); beide laufen auch bei Teilfehlern."""
    msgs, errs = [], []
    for fn in (update_measured_snow, update_snow_stations):
        try:
            msgs.append(fn(resort, now))
        except Exception as e:
            errs.append(str(e))
    if errs:
        raise RuntimeError(" | ".join(msgs + ["FEHLER: " + e for e in errs]))
    return " | ".join(msgs)


# ---------- Liftstatus ----------
# Quelle: offizielle Live-Info-Seiten von Ski Arlberg (Tabelle: Lift | Status | Typ | Betriebszeiten).
# Für Obertauern und Sölden ist noch keine Quelle konfiguriert (wird übersprungen).
# Sicherheitsregel: Ist die Liste unvollständig (partial=true), darf die App fehlende Lifte NICHT als "geschlossen" anzeigen.

LIFT_SOURCES = {
    "arlberg": {
        "expected_total": 85,
        "sources": [
            {"area": "St. Anton – St. Christoph – Stuben", "url": "https://www.skiarlberg.at/en/st-anton/live-info/cable-cars-lifts"},
            {"area": "Lech – Oberlech – Zürs", "url": "https://www.skiarlberg.at/en/lech-zuers/live-info/cable-cars-lifts"},
            {"area": "Warth-Schröcken", "url": "https://www.skiarlberg.at/en/warth-schroecken/live-info/cable-cars-lifts"},
        ],
    },
    "obertauern": {
        "parser": "icon_table",
        "expected_total": 26,
        # Status steckt im Symbol (Bild-ID). 594/599/600/601 stehen in der Legende der Seite;
        # 591 ist NICHT in der Legende: Annahme "nicht in Betrieb", abgeleitet aus dem Vergleich vom 21.11.2026
        # (nur die 4 Lifte mit Symbol 594 liefen, genau wie im Infotext der Seite genannt).
        "icon_status": {"594": "open", "599": "hold", "600": "closed", "601": "closed", "591": "closed"},
        "note": "Status aus Symbolen der Seite; unbekannte Symbole werden als 'unknown' gespeichert.",
        "sources": [{"area": "Obertauern", "url": "https://www.ski-obertauern.at/en/lifts-pists/open-lifts"}],
    },
    "soelden": {
        "parser": "open_list",
        "expected_total": 31,
        "note": "Quelle nennt nur OFFENE Lifte aus den Skigebietsnews (Gletscher-/Winterskigebiet). "
                "Nicht gelistete Lifte sind unbekannt, nicht geschlossen.",
        "sources": [{"area": "Sölden", "url": "https://www.soelden.com/en/live-information/ski-resort-news"}],
    },
}
LIFT_STATUS_WORDS = {"open": "open", "closed": "closed", "on hold": "hold", "interrupted": "hold",
                     "standby": "hold", "stand by": "hold", "temporarily closed": "closed"}
LIFT_SKIP = {"type", "operating hours", "show map", "show more", "status", "interactive map", "lift facility", "lift"}
RE_HOURS = re.compile(r"^\d{1,2}:\d{2}\s*[-–]\s*\d{1,2}:\d{2}$")


class _RowParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.rows, self._row, self._skip = [], None, 0

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self._skip += 1
        elif tag == "tr":
            self._row = []

    def handle_endtag(self, tag):
        if tag in ("script", "style"):
            self._skip = max(0, self._skip - 1)
        elif tag == "tr" and self._row is not None:
            self.rows.append(self._row)
            self._row = None

    def handle_data(self, data):
        if self._skip or self._row is None:
            return
        t = re.sub(r"\s+", " ", data).strip()
        if t:
            self._row.append(t)


def norm_name(name):
    t = unicodedata.normalize("NFKD", name or "").encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z0-9]", "", t)


def parse_lift_rows(raw):
    p = _RowParser()
    p.feed(raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else raw)
    out, seen = [], set()
    for row in p.rows:
        st_i = next((i for i, t in enumerate(row) if t.lower() in LIFT_STATUS_WORDS), None)
        if st_i is None or row[0].lower() in LIFT_SKIP or row[0].lower() in LIFT_STATUS_WORDS:
            continue
        hours = next((t for t in row if RE_HOURS.match(t)), None)
        ltype = next((t for t in row[st_i + 1:] if t.lower() not in LIFT_SKIP and not RE_HOURS.match(t)
                      and t.lower() not in LIFT_STATUS_WORDS), None)
        key = norm_name(row[0])
        if key in seen:
            continue
        seen.add(key)
        out.append({"name": row[0], "status": LIFT_STATUS_WORDS[row[st_i].lower()], "type": ltype, "hours": hours})
    return out


class _IconRowParser(HTMLParser):
    """Tabellenzeilen mit Text und Bild-IDs (Status als Symbol, z. B. ...?eID=dumpFile&f=594&token=...)."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.rows, self._row, self._skip = [], None, 0

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self._skip += 1
        elif tag == "tr":
            self._row = {"texts": [], "icons": []}
        elif tag == "img" and self._row is not None:
            m = re.search(r"[?&]f=(\d+)", dict(attrs).get("src") or "")
            if m:
                self._row["icons"].append(m.group(1))

    def handle_endtag(self, tag):
        if tag in ("script", "style"):
            self._skip = max(0, self._skip - 1)
        elif tag == "tr" and self._row is not None:
            self.rows.append(self._row)
            self._row = None

    def handle_data(self, data):
        if not self._skip and self._row is not None:
            t = re.sub(r"\s+", " ", data).strip()
            if t:
                self._row["texts"].append(t)


def parse_lift_icon_rows(raw, icon_status):
    """Nummerierte Liftzeilen (01, 02, ...) der ERSTEN Tabelle; spätere Abschnitte (Fußgänger, Nachtski, ...) starten
    wieder bei 01 und werden ignoriert. Status = erstes Symbol der Zeile; unbekannte Symbole -> 'unknown'."""
    p = _IconRowParser()
    p.feed(raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else raw)
    out, nxt = [], 1
    for row in p.rows:
        t = row["texts"]
        idx = next((i for i, x in enumerate(t) if re.fullmatch(r"\d{2}", x)), None)
        if idx is None or int(t[idx]) != nxt or idx + 1 >= len(t):
            continue
        nxt += 1
        out.append({"name": t[idx + 1], "type": t[idx + 2] if idx + 2 < len(t) else None, "hours": None,
                    "status": icon_status.get(row["icons"][0], "unknown") if row["icons"] else "unknown"})
    return out


class _OpenListParser(HTMLParser):
    """Liest 'Lifts'-Listen unter Gebiets- (h3) und Datumsüberschriften der Skigebietsnews."""
    HEAD = ("h1", "h2", "h3", "h4", "h5", "h6")

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.items, self._skip = [], 0
        self.area = self.date = self.section = None
        self._head, self._buf, self._li = None, [], None

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self._skip += 1
        elif tag in self.HEAD:
            self._head, self._buf = tag, []
        elif tag == "li":
            self._li = []

    def handle_endtag(self, tag):
        if tag in ("script", "style"):
            self._skip = max(0, self._skip - 1)
        elif tag == self._head:
            text = re.sub(r"\s+", " ", "".join(self._buf)).strip()
            low = text.lower()
            if low in ("lifts", "lifte"):
                self.section = "lifts"
            elif low in ("slopes", "restaurants", "information", "pisten", "restaurants"):
                self.section = None
            elif re.search(r"\b\d{1,2},\s*\d{4}$", text):
                self.date = text
            elif tag == "h3":
                self.area, self.date, self.section = text, None, None
            self._head = None
        elif tag == "li" and self._li is not None:
            text = re.sub(r"\s+", " ", "".join(self._li)).strip()
            if text and self.section == "lifts":
                self.items.append({"area": self.area, "date": self.date, "text": text})
            self._li = None

    def handle_data(self, data):
        if self._skip:
            return
        if self._head:
            self._buf.append(data)
        if self._li is not None:
            self._li.append(data)


def parse_open_list(raw, now):
    p = _OpenListParser()
    p.feed(raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else raw)
    out = []
    for it in p.items:
        list_date = None
        m = re.search(r"([A-Za-z]+)\s+(\d{1,2}),\s*(\d{4})", it["date"] or "")
        if m:
            try:
                list_date = datetime.strptime(f"{m.group(1)} {m.group(2)} {m.group(3)}", "%B %d %Y").date()
            except ValueError:
                list_date = None
        m2 = re.match(r"^(\d+[A-Z]{2,4})\s+(.*)$", it["text"])
        out.append({"name": (m2.group(2) if m2 else it["text"]), "type": m2.group(1) if m2 else None,
                    "hours": None, "status": "open", "listed_for": list_date.isoformat() if list_date else None,
                    "stale": list_date is None or list_date < now.date()})
    return out


def parse_lifts_for(cfg, raw, now):
    mode = cfg.get("parser", "table")
    if mode == "icon_table":
        return parse_lift_icon_rows(raw, cfg["icon_status"])
    if mode == "open_list":
        return parse_open_list(raw, now)
    return parse_lift_rows(raw)


def update_lifts(resort, now=None):
    now = now or datetime.now(TZ)
    cfg = resort.get("lift_sources") or LIFT_SOURCES.get(resort["id"])
    if not cfg:
        return "keine Liftstatus-Quelle konfiguriert (übersprungen)"
    ls = resort.setdefault("lift_status", {})
    fresh, failed_areas, errors = {}, [], []
    for src in cfg["sources"]:
        area, url = src.get("area"), src["url"]
        try:
            if not robots_allows(url):
                raise RuntimeError("laut robots.txt nicht erlaubt")
            rows = parse_lifts_for(cfg, http_bytes(url), now)
            if not rows:
                raise RuntimeError("keine Liftzeilen gefunden (Seite geändert oder per JavaScript geladen)")
        except Exception as e:
            failed_areas.append(area)
            errors.append(f"{area or url}: {e}")
            continue
        for r in rows:
            r["area"] = area
            r.setdefault("stale", False)
            fresh.setdefault(norm_name(r["name"]), r)
    if not fresh:
        ls["stale"], ls["error"] = True, " | ".join(errors)
        raise RuntimeError(ls["error"])
    # Teilgebiete, die ausgefallen sind: alte Einträge behalten, als veraltet markieren
    for old in ls.get("items", []):
        if old.get("area") in failed_areas and norm_name(old["name"]) not in fresh:
            old["stale"] = True
            fresh[norm_name(old["name"])] = old
    items = sorted(fresh.values(), key=lambda x: ((x.get("area") or ""), x["name"]))
    expected = cfg.get("expected_total")
    ls.update({
        "items": items,
        "listed": len(items),
        "open": sum(1 for i in items if i["status"] == "open" and not i["stale"]),
        "expected_total": expected,
        "partial": bool(errors) or cfg.get("parser") == "open_list" or (expected is not None and len(items) < expected),
        "sources": [x["url"] for x in cfg["sources"]],
        "fetched_at": now.isoformat(timespec="minutes"),
        "stale": bool(failed_areas) or all(i["stale"] for i in items),
        "error": " | ".join(errors) or None,
        "mode": cfg.get("parser", "table"),
        "note": cfg.get("note"),
    })
    by_name = {norm_name(l.get("name")): l for l in resort.get("lifts", []) if l.get("name")}
    matched = 0
    for it in items:
        lift = by_name.get(norm_name(it["name"]))
        if lift and not it["stale"]:
            lift.update({"status": it["status"], "hours": it["hours"], "updated_at": ls["fetched_at"]})
            matched += 1
    summary = f"{ls['open']} offen von {len(items)} gelisteten Liften (erwartet {expected}), {matched} mit OSM-Lift verknüpft"
    if errors:
        raise RuntimeError(summary + " | FEHLER: " + " | ".join(errors))
    return summary


# ---------- Lawinenlagebericht ----------
# Format: CAAMLv5 (EAWS). Pro Bundesland eine Datei: <Datum>_AT-xx_en.xml
# Quellen-URLs für AT-05 sind geprüft; für AT-07 und AT-08 werden mehrere Hosts nacheinander versucht.

AVALANCHE_URLS = {
    "AT-05": ["https://static.lawinen-warnung.eu/bulletins/{d}/{d}_AT-05_en.xml"],
    "AT-07": ["https://avalanche.report/bulletins/{d}/{d}_AT-07_en.xml",
              "https://static.lawinen-warnung.eu/bulletins/{d}/{d}_AT-07_en.xml"],
    "AT-08": ["https://static.lawinen-warnung.eu/bulletins/{d}/{d}_AT-08_en.xml",
              "https://static-albina.avalanche-warnings.eu/bulletins/{d}/{d}_AT-08_en.xml"],
}
AVALANCHE_PAGES = {
    "AT-05": "https://lawine.salzburg.at",
    "AT-07": "https://lawinen.report",
    "AT-08": "https://warnung.vorarlberg.at",
}
ASPECT_ORDER = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"]
DANGER_WORDS = {"low": 1, "moderate": 2, "considerable": 3, "high": 4, "very_high": 5, "very high": 5}


def ln(tag):
    return tag.rsplit("}", 1)[-1]


def href_of(el):
    for k, v in el.attrib.items():
        if k.endswith("href"):
            return v
    return None


def parse_danger(text):
    t = (text or "").strip().lower()
    if t.isdigit():
        v = int(t)
        return v if 1 <= v <= 5 else None
    return DANGER_WORDS.get(t)


def parse_elevation(el):
    """validElevation -> {"above": m} / {"below": m} (m kann auch 'treeline' sein) oder None."""
    h = href_of(el)
    if h:
        m = re.search(r"ElevationRange_(.+?)(Hi|Lw)$", h)
        if m:
            val = int(m.group(1)) if m.group(1).isdigit() else m.group(1).lower()
            return {"above": val} if m.group(2) == "Hi" else {"below": val}
        return {"raw": h}
    out = {}
    for sub in el.iter():
        txt = (sub.text or "").strip()
        if ln(sub.tag) == "beginPosition" and txt.isdigit():
            out["above"] = int(txt)
        elif ln(sub.tag) == "endPosition" and txt.isdigit():
            out["below"] = int(txt)
    return out or None


def parse_bulletins(xml_bytes):
    root = ET.fromstring(xml_bytes)
    result = []
    for b in root.iter():
        if ln(b.tag) != "Bulletin":
            continue
        regions = [href_of(c) for c in b if ln(c.tag) == "locRef" and href_of(c)]
        valid_from = valid_to = None
        for vt in b:
            if ln(vt.tag) == "validTime":
                for sub in vt.iter():
                    if ln(sub.tag) == "beginPosition":
                        valid_from = (sub.text or "").strip() or None
                    elif ln(sub.tag) == "endPosition":
                        valid_to = (sub.text or "").strip() or None
        ratings, problems = [], []
        for el in b.iter():
            name = ln(el.tag)
            if name == "DangerRating":
                val, elev = None, None
                for c in el:
                    if ln(c.tag) == "mainValue":
                        val = parse_danger(c.text)
                    elif ln(c.tag) == "validElevation":
                        elev = parse_elevation(c)
                if val:
                    ratings.append({"level": val, "elevation": elev})
            elif name == "AvProblem":
                ptype, aspects, elev = None, [], None
                for c in el:
                    if ln(c.tag) == "type":
                        ptype = (c.text or "").strip() or None
                    elif ln(c.tag) == "validAspect":
                        h = href_of(c) or ""
                        a = h.rsplit("_", 1)[-1].upper()
                        if a in ASPECT_ORDER:
                            aspects.append(a)
                    elif ln(c.tag) == "validElevation":
                        elev = parse_elevation(c)
                problems.append({"type": ptype, "aspects": sorted(set(aspects), key=ASPECT_ORDER.index), "elevation": elev})
        result.append({"regions": regions, "valid_from": valid_from, "valid_to": valid_to,
                       "ratings": ratings, "problems": problems})
    return result


def summarize_avalanche(bulletins, region_ids):
    wanted = set(region_ids)
    hits = [b for b in bulletins if wanted & set(b["regions"])]
    if not hits:
        return None
    ratings = [r for b in hits for r in b["ratings"]]
    if not ratings:
        return None
    seen, by_elev = set(), []
    for r in sorted(ratings, key=lambda r: -r["level"]):
        key = (r["level"], json.dumps(r["elevation"], sort_keys=True))
        if key not in seen:
            seen.add(key)
            by_elev.append(r)
    problems, pseen = [], set()
    for b in hits:
        for p in b["problems"]:
            key = json.dumps(p, sort_keys=True)
            if key not in pseen:
                pseen.add(key)
                problems.append(p)
    aspects = sorted({a for p in problems for a in p["aspects"]}, key=ASPECT_ORDER.index)
    ends = [b["valid_to"] for b in hits if b["valid_to"]]
    return {
        "level": max(r["level"] for r in ratings),
        "levels_by_elevation": by_elev,
        "aspects": aspects,
        "problems": problems,
        "valid_until": max(ends) if ends else None,
        "matched_regions": sorted(wanted & {r for b in hits for r in b["regions"]}),
    }


def date_candidates(now):
    days = []
    if now.hour >= 17:
        days.append(now + timedelta(days=1))
    days += [now, now - timedelta(days=1)]
    return [d.strftime("%Y-%m-%d") for d in days]


def fetch_bulletin(state, now):
    if state not in AVALANCHE_URLS:
        raise RuntimeError(f"Unbekanntes Bundesland {state}")
    last = None
    for d in date_candidates(now):
        for tmpl in AVALANCHE_URLS[state]:
            url = tmpl.format(d=d)
            try:
                return url, parse_bulletins(http_bytes(url))
            except (urllib.error.URLError, TimeoutError, ET.ParseError) as e:
                last = f"{url}: {e}"
    raise RuntimeError(f"Kein Lagebericht für {state} abrufbar (zuletzt: {last})")


def is_expired(valid_until, now):
    if not valid_until:
        return None
    try:
        return datetime.fromisoformat(valid_until.replace("Z", "+00:00")) < now
    except ValueError:
        return None


def update_avalanche(resort, now=None):
    now = now or datetime.now(TZ)
    av = resort.setdefault("avalanche", {})
    ids = av.get("region_ids") or []
    if not ids:
        av["level"] = None
        av["note"] = "region_ids fehlen: IDs mit --probe ermitteln und unter avalanche.region_ids eintragen"
        return "keine region_ids konfiguriert (Lawinenstufe bleibt null)"

    states = sorted({"-".join(i.split("-")[:2]) for i in ids})
    bulletins, sources = [], []
    try:
        for st in states:
            url, bl = fetch_bulletin(st, now)
            bulletins += bl
            sources.append(url)
        summary = summarize_avalanche(bulletins, ids)
        if summary is None:
            raise RuntimeError(f"region_ids {ids} in keinem Bericht gefunden")
    except Exception as e:
        # Alte Werte behalten, aber klar als veraltet markieren. Nie "gering" annehmen.
        av["stale"] = True
        av["error"] = str(e)
        raise

    av.update(summary)
    av["bulletin_url"] = AVALANCHE_PAGES[states[0]]
    av["bulletin_urls"] = [AVALANCHE_PAGES[s] for s in states]
    av["source_files"] = sources
    av["updated_at"] = now.isoformat(timespec="minutes")
    av["stale"] = bool(is_expired(summary["valid_until"], now))
    av["error"] = None
    av.pop("note", None)
    return f"Stufe {summary['level']}, gültig bis {summary['valid_until']}, Regionen {summary['matched_regions']}"


def probe_avalanche(state, now=None):
    """Zeigt alle Bulletins eines Bundeslands mit Regions-IDs und Stufen, um region_ids für data.json zu wählen."""
    now = now or datetime.now(TZ)
    url, bulletins = fetch_bulletin(state, now)
    print(f"Quelle: {url}")
    for b in bulletins:
        mx = max((r["level"] for r in b["ratings"]), default=None)
        print(f"- Stufe max {mx} | gültig bis {b['valid_to']} | Regionen: {', '.join(b['regions'])}")
    print("Namen zu den IDs: https://lawinen.report/education/handbook")


# ---------- Main ----------

def save_atomic(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def main():
    ap = argparse.ArgumentParser(description="Powderlog Update-Agent")
    ap.add_argument("--file", default="data.json")
    ap.add_argument("--only", choices=["geo", "weather", "snow", "avalanche", "webcams", "lifts", "all"], default="all")
    ap.add_argument("--probe", metavar="STATE", help="Regions-IDs eines Bundeslands anzeigen (AT-05, AT-07, AT-08)")
    ap.add_argument("--resort", help="nur dieses Skigebiet (id)")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if args.probe:
        probe_avalanche(args.probe)
        return

    with open(args.file, encoding="utf-8") as f:
        data = json.load(f)

    errors = 0
    for resort in data["resorts"]:
        if args.resort and resort["id"] != args.resort:
            continue
        steps = []
        if args.only in ("weather", "all"):
            steps.append(("weather", update_weather))
        if args.only in ("snow", "all"):
            steps.append(("snow", update_snow))
        if args.only in ("avalanche", "all"):
            steps.append(("avalanche", update_avalanche))
        if args.only in ("geo", "all"):
            steps.append(("geo", update_geo))
        if args.only in ("lifts", "all"):
            steps.append(("lifts", update_lifts))
        if args.only in ("webcams", "all"):
            steps.append(("webcams", update_webcams))
        for name, fn in steps:
            try:
                print(f"[{resort['id']}] {name}: {fn(resort)}")
            except Exception as e:
                errors += 1
                print(f"[{resort['id']}] {name} FEHLER: {e}", file=sys.stderr)
            time.sleep(1)

    data["meta"]["updated_at"] = datetime.now(TZ).isoformat(timespec="minutes")
    data["meta"]["updated_by"] = "update_agent.py"
    if args.dry_run:
        print("Dry-Run: nichts geschrieben.")
    else:
        save_atomic(args.file, data)
        print(f"Gespeichert: {args.file}")
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
