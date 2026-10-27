#!/usr/bin/env python3
"""Watch the network path to destinations you choose, and alarm when it changes.

Add each destination and its label in the browser. The watch traces them
from this machine once a second and remembers the list in destinations.json.

    python3 route_watch.py

A hop that starts answering during the first minute is added to the picture
quietly, because the far end of a path often answers on only some probes.
A router that replaces one already on the path raises an alarm after it
answers twice in a row. Silence raises an alarm only for a hop that answered
on every learning probe, and only after eight silent probes in a row.
"""

from __future__ import annotations

import argparse
import json
import queue
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import uuid
import webbrowser
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

LEARN_SAMPLES = 8
CONFIRM_PROBES = 2
MISS_PROBES = 8
DISCOVER_SECONDS = 60
DEEP_EVERY = 30
INDEX = Path(__file__).with_name("index.html")
STORE = Path(__file__).with_name("destinations.json")

HOP_LINE = re.compile(
    r"^\s*(\d+)\s+(?:\*|(\d{1,3}(?:\.\d{1,3}){3}))"
    r"(?:\s+([\d.]+)\s+ms)?(?:\s+!\S+)?\s*$"
)
HOST_RE = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9.-]{0,251}[A-Za-z0-9])?")


def clean_label(value: object) -> str:
    text = " ".join(str(value or "").split())
    if not text:
        raise ValueError("Add a label")
    if len(text) > 80:
        raise ValueError("Use a shorter label")
    if any(ord(ch) < 32 for ch in text):
        raise ValueError("That label cannot be shown")
    return text


def clean_host(value: object) -> str:
    host = str(value or "").strip()
    if not host:
        raise ValueError("Add an address")
    if not HOST_RE.fullmatch(host) or ".." in host:
        raise ValueError("Use a hostname or an IPv4 address")
    if re.fullmatch(r"(?:\d{1,3}\.){3}\d{1,3}", host):
        if any(int(part) > 255 for part in host.split(".")):
            raise ValueError("That IP address is not usable")
    return host


def is_private(ip: str) -> bool:
    try:
        parts = [int(p) for p in ip.split(".")]
    except ValueError:
        return False
    if len(parts) != 4 or any(p < 0 or p > 255 for p in parts):
        return False
    if parts[0] == 10 or parts[0] == 127:
        return True
    if parts[0] == 192 and parts[1] == 168:
        return True
    if parts[0] == 172 and 16 <= parts[1] <= 31:
        return True
    if parts[0] == 100 and 64 <= parts[1] <= 127:
        return True
    return False


def parse_hop(stdout: str, ttl: int) -> tuple[str | None, float | None]:
    for line in stdout.splitlines():
        match = HOP_LINE.match(line)
        if not match or int(match.group(1)) != ttl:
            continue
        ip = match.group(2)
        rtt = float(match.group(3)) if match.group(3) else None
        return ip, rtt
    return None, None


def traceroute_bin() -> str:
    found = shutil.which("traceroute")
    if found:
        return found
    if Path("/usr/sbin/traceroute").exists():
        return "/usr/sbin/traceroute"
    raise FileNotFoundError("traceroute is not installed")


def probe_ttl(host: str, ttl: int) -> tuple[str | None, float | None]:
    proc = subprocess.run(
        [
            traceroute_bin(),
            "-n",
            "-q",
            "1",
            "-w",
            "1",
            "-f",
            str(ttl),
            "-m",
            str(ttl),
            host,
        ],
        capture_output=True,
        text=True,
        timeout=4,
    )
    if proc.returncode != 0 and not proc.stdout.strip():
        detail = proc.stderr.strip() or f"traceroute exited {proc.returncode}"
        raise RuntimeError(detail.splitlines()[-1])
    return parse_hop(proc.stdout, ttl)


def probe(host: str, depth: int) -> tuple[list[dict], str | None]:
    hops: list[dict] = []
    errors: list[str] = []
    with ThreadPoolExecutor(max_workers=depth) as pool:
        futures = {ttl: pool.submit(probe_ttl, host, ttl) for ttl in range(1, depth + 1)}
        for ttl in range(1, depth + 1):
            try:
                ip, rtt = futures[ttl].result()
            except Exception as exc:  # noqa: BLE001 - surface any probe failure on the page
                errors.append(str(exc))
                ip, rtt = None, None
            hops.append({"ttl": ttl, "ip": ip, "rtt_ms": rtt})
    if errors and not any(hop["ip"] for hop in hops):
        return [], errors[0]
    return hops, None


def describe_diffs(diffs: list[dict]) -> str:
    parts: list[str] = []
    for diff in diffs:
        before = ", ".join(diff["before"]) if diff["before"] else "no reply"
        if diff["kind"] == "missing":
            parts.append(f"Hop {diff['ttl']} stopped answering ({before})")
        else:
            parts.append(f"Hop {diff['ttl']} changed from {before} to {diff['after']}")
    return ". ".join(parts)


class PathMemory:
    """Baseline path for one gateway, and the alarms raised against it."""

    def __init__(self) -> None:
        self.samples = 0
        self.started = time.monotonic()
        self.locked_at: float | None = None
        self.stable_since: float | None = None
        self.baseline: dict[int, set[str]] = {}
        self.hits: dict[int, int] = {}
        self.always: set[int] = set()
        self.misses: dict[int, int] = {}
        self.pending: dict[int, tuple[str, int]] = {}
        self.alerted: dict[int, str] = {}
        self.missing_alerted: set[int] = set()
        self.last_accepted: dict[int, str] = {}
        self.alert: dict | None = None

    @property
    def learning(self) -> bool:
        return self.samples < LEARN_SAMPLES

    def note(self, hops: list[dict], now: float) -> list[dict]:
        self.samples += 1
        if self.samples <= LEARN_SAMPLES:
            for hop in hops:
                if not hop["ip"]:
                    continue
                self.hits[hop["ttl"]] = self.hits.get(hop["ttl"], 0) + 1
                self.baseline.setdefault(hop["ttl"], set()).add(hop["ip"])
                self.last_accepted[hop["ttl"]] = hop["ip"]
            if self.samples < LEARN_SAMPLES:
                return []
            self.locked_at = now
            self.stable_since = time.time()
            self.always = {
                ttl for ttl, count in self.hits.items() if count == LEARN_SAMPLES
            }

        events: list[dict] = []
        diffs: list[dict] = []
        discovering = (now - self.started) < DISCOVER_SECONDS
        for hop in hops:
            diff = self._judge(hop, discovering)
            if diff:
                diffs.append(diff)
        if diffs:
            if self.alert:
                fresh = {diff["ttl"] for diff in diffs}
                for old in self.alert["diffs"]:
                    if old["ttl"] in fresh:
                        continue
                    if old["kind"] == "changed" and self.alerted.get(old["ttl"]) == old["after"]:
                        diffs.append(old)
                    elif old["kind"] == "missing" and old["ttl"] in self.missing_alerted:
                        diffs.append(old)
            diffs.sort(key=lambda item: item["ttl"])
            summary = describe_diffs(diffs)
            self.alert = {
                "id": str(time.time_ns()),
                "at": time.time(),
                "summary": summary,
                "diffs": diffs,
            }
            events.append({"kind": "alert", "summary": summary, "id": self.alert["id"]})
        return events

    def _judge(self, hop: dict, discovering: bool) -> dict | None:
        ttl = hop["ttl"]
        ip = hop["ip"]
        known = self.baseline.get(ttl, set())

        if ip is None:
            self.pending.pop(ttl, None)
            if ttl not in self.always:
                return None
            self.misses[ttl] = self.misses.get(ttl, 0) + 1
            if self.misses[ttl] < MISS_PROBES or ttl in self.missing_alerted:
                return None
            self.missing_alerted.add(ttl)
            return {"ttl": ttl, "kind": "missing", "before": sorted(known), "after": None}

        was_missing = ttl in self.missing_alerted
        self.misses[ttl] = 0
        if was_missing:
            self.missing_alerted.discard(ttl)
            if self.alert:
                self.alert["diffs"] = [
                    diff
                    for diff in self.alert["diffs"]
                    if not (diff["ttl"] == ttl and diff["kind"] == "missing")
                ]
                if not self.alert["diffs"]:
                    self.alert = None
                    self.stable_since = time.time()
                else:
                    self.alert["summary"] = describe_diffs(self.alert["diffs"])

        if ip in known or ip == self.alerted.get(ttl):
            self.pending.pop(ttl, None)
            self.last_accepted[ttl] = ip
            return None

        previous, count = self.pending.get(ttl, ("", 0))
        count = count + 1 if previous == ip else 1
        self.pending[ttl] = (ip, count)
        if count < CONFIRM_PROBES:
            return None

        self.pending.pop(ttl, None)
        if not known and discovering:
            self.baseline.setdefault(ttl, set()).add(ip)
            self.last_accepted[ttl] = ip
            return None

        self.alerted[ttl] = ip
        self.last_accepted[ttl] = ip
        return {"ttl": ttl, "kind": "changed", "before": sorted(known), "after": ip}

    def mark(self, ttl: int, ip: str | None) -> str:
        if self.alert:
            for diff in self.alert["diffs"]:
                if diff["ttl"] == ttl:
                    return "changed" if diff["kind"] == "changed" else "missing"
        if ip is None:
            if ttl in self.last_accepted:
                return "same"
            return "silent"
        known = self.baseline.get(ttl, set())
        pending = self.pending.get(ttl)
        if pending and pending[0] == ip and ip not in known and ip != self.alerted.get(ttl):
            if known or (time.monotonic() - self.started) >= DISCOVER_SECONDS:
                return "watching"
        return "same"

    def was(self, ttl: int) -> list[str]:
        if not self.alert:
            return []
        for diff in self.alert["diffs"]:
            if diff["ttl"] == ttl:
                return list(diff["before"])
        return []

    def ack(self) -> None:
        if self.alert:
            for diff in self.alert["diffs"]:
                if diff["kind"] == "changed" and diff["after"]:
                    self.baseline[diff["ttl"]] = {diff["after"]}
                    self.last_accepted[diff["ttl"]] = diff["after"]
                elif diff["kind"] == "missing":
                    self.always.discard(diff["ttl"])
        self.alert = None
        self.alerted.clear()
        self.missing_alerted.clear()
        self.pending.clear()
        self.misses.clear()
        self.stable_since = time.time()


class Destination:
    def __init__(self, dest_id: str, label: str, host: str) -> None:
        self.id = dest_id
        self.name = label
        self.host = host
        self.removed = False
        self.hops: list[dict] = []
        self.error: str | None = None
        self.probed_at: float | None = None
        self.probe_ms: float | None = None
        self.last_ttl: int | None = None
        self.cycle = 0
        self.memory = PathMemory()
        self.address_alert: dict | None = None

    def set_host(self, host: str) -> str | None:
        if self.host == host:
            return None
        previous = self.host
        self.host = host
        self.memory = PathMemory()
        self.hops = []
        self.last_ttl = None
        self.error = None
        summary = f"Address changed from {previous} to {host}"
        self.address_alert = {
            "id": str(time.time_ns()),
            "at": time.time(),
            "summary": summary,
            "diffs": [],
        }
        return summary

    def depth(self) -> int:
        self.cycle += 1
        if self.cycle % DEEP_EVERY == 0:
            return 24
        if self.last_ttl is None:
            return 16
        return min(24, max(self.last_ttl + 3, 12))

    def apply_probe(self, hops: list[dict], error: str | None, probe_ms: float) -> list[dict]:
        self.probed_at = time.time()
        self.probe_ms = probe_ms
        self.error = error
        if error:
            return []
        self.hops = hops
        responding = [hop["ttl"] for hop in hops if hop["ip"]]
        reached = [hop["ttl"] for hop in hops if hop["ip"] == self.host]
        known = [ttl for ttl, ips in self.memory.baseline.items() if ips]
        if reached:
            self.last_ttl = min(reached)
        elif responding or known:
            self.last_ttl = max(responding + known)
        return self.memory.note(hops, time.monotonic())

    def ack(self) -> None:
        if self.address_alert:
            self.address_alert = None
            self.memory.stable_since = time.time()
            return
        self.memory.ack()

    def status(self) -> str:
        if self.address_alert or self.memory.alert:
            return "changed"
        if self.memory.samples == 0:
            return "starting"
        if self.memory.learning:
            return "learning"
        if not any(hop["ip"] for hop in self.hops):
            return "silent"
        return "stable"

    def visible_hops(self, names: dict[str, str | None]) -> list[dict]:
        limit = 0
        for hop in self.hops:
            if hop["ip"]:
                limit = max(limit, hop["ttl"])
        for ttl, ips in self.memory.baseline.items():
            if ips:
                limit = max(limit, ttl)
        for hop in self.hops:
            if hop["ip"] == self.host:
                limit = hop["ttl"]
                break
        visible = []
        for hop in self.hops:
            if hop["ttl"] > limit:
                continue
            ip = hop["ip"]
            hold = self.memory.last_accepted.get(hop["ttl"])
            mark = self.memory.mark(hop["ttl"], ip)
            shown = ip or hold
            known = self.memory.baseline.get(hop["ttl"], set())
            also = [] if mark in ("changed", "missing") else sorted(
                other for other in known if other and other != shown
            )
            visible.append(
                {
                    "ttl": hop["ttl"],
                    "ip": ip,
                    "hold": hold,
                    "also": also,
                    "rtt_ms": hop["rtt_ms"],
                    "name": names.get(shown) if shown else None,
                    "local": bool(shown and is_private(shown)),
                    "mark": mark,
                    "was": self.memory.was(hop["ttl"]),
                }
            )
        return visible

    def to_json(self, names: dict[str, str | None]) -> dict:
        banner = self.address_alert or self.memory.alert
        return {
            "id": self.id,
            "name": self.name,
            "label": self.name,
            "host": self.host,
            "status": self.status(),
            "samples": self.memory.samples,
            "learn_samples": LEARN_SAMPLES,
            "stable_since": self.memory.stable_since if self.status() == "stable" else None,
            "probed_at": self.probed_at,
            "error": self.error,
            "hops": self.visible_hops(names),
            "reached": bool(self.host and any(hop["ip"] == self.host for hop in self.hops)),
            "banner": banner,
        }


class Resolver(threading.Thread):
    def __init__(self, on_update) -> None:
        super().__init__(daemon=True)
        self.on_update = on_update
        self.cache: dict[str, str | None] = {}
        self.pending: set[str] = set()
        self.jobs: queue.Queue[str] = queue.Queue()
        self.lock = threading.Lock()

    def copy(self) -> dict[str, str | None]:
        with self.lock:
            return dict(self.cache)

    def want(self, ip: str | None) -> None:
        if not ip:
            return
        with self.lock:
            if ip in self.cache or ip in self.pending:
                return
            self.pending.add(ip)
        self.jobs.put(ip)

    def run(self) -> None:
        while True:
            ip = self.jobs.get()
            name = self._resolve(ip)
            with self.lock:
                self.cache[ip] = name
                self.pending.discard(ip)
            self.on_update()

    @staticmethod
    def _resolve(ip: str) -> str | None:
        if is_private(ip):
            return None
        try:
            socket.setdefaulttimeout(0.6)
            host, _aliases, _ips = socket.gethostbyaddr(ip)
        except OSError:
            return None
        finally:
            socket.setdefaulttimeout(None)
        if host == ip:
            return None
        return host.rstrip(".")


class Hub:
    def __init__(self) -> None:
        self.cond = threading.Condition()
        self.generation = 0
        self.payload = "{}"

    def publish(self, payload: str) -> None:
        with self.cond:
            self.generation += 1
            self.payload = payload
            self.cond.notify_all()

    def wait_next(self, generation: int, timeout: float = 15) -> tuple[int, str, bool]:
        with self.cond:
            if self.generation == generation:
                self.cond.wait(timeout)
            changed = self.generation != generation
            return self.generation, self.payload, changed


class App:
    def __init__(self, interval: float, store: Path) -> None:
        self.interval = interval
        self.store = store
        self.source = socket.gethostname()
        self.lock = threading.Lock()
        self.destinations: list[Destination] = []
        self.log: list[dict] = []
        self.hub = Hub()
        self.stop = threading.Event()
        self.resolver = Resolver(self.publish)
        self.names: dict[str, str | None] = {}

    def destination(self, dest_id: str) -> Destination | None:
        for dest in self.destinations:
            if dest.id == dest_id:
                return dest
        return None

    def record(self, dest: Destination, summary: str) -> None:
        stamp = time.strftime("%H:%M:%S")
        print(f"{stamp}  {dest.name}  {summary}", flush=True)
        self.log.append({"at": time.time(), "label": dest.name, "summary": summary})
        if len(self.log) > 40:
            del self.log[:-40]

    def snapshot(self) -> dict:
        names = self.resolver.copy()
        with self.lock:
            self.names = names
            return {
                "source": self.source,
                "interval_s": self.interval,
                "targets": [dest.to_json(self.names) for dest in self.destinations],
                "log": list(reversed(self.log)),
            }

    def publish(self) -> None:
        self.hub.publish(json.dumps(self.snapshot(), separators=(",", ":")))

    def save(self) -> None:
        payload = [
            {"id": dest.id, "label": dest.name, "host": dest.host}
            for dest in self.destinations
        ]
        temporary = self.store.with_suffix(".tmp")
        temporary.write_text(json.dumps(payload, indent=2) + "\n")
        temporary.replace(self.store)

    def load(self) -> None:
        if not self.store.exists():
            return
        try:
            payload = json.loads(self.store.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            print(f"Could not read {self.store}: {exc}", flush=True)
            return
        if not isinstance(payload, list):
            return
        for item in payload:
            if not isinstance(item, dict):
                continue
            try:
                label = clean_label(item.get("label"))
                host = clean_host(item.get("host"))
            except ValueError:
                continue
            dest_id = str(item.get("id") or uuid.uuid4().hex[:8])
            if self.destination(dest_id):
                continue
            self.destinations.append(Destination(dest_id, label, host))

    def start_probe(self, dest: Destination) -> None:
        threading.Thread(target=self.probe_loop, args=(dest,), daemon=True).start()

    def add_destination(self, label: object, host: object) -> str:
        cleaned_label = clean_label(label)
        cleaned_host = clean_host(host)
        with self.lock:
            dest = Destination(uuid.uuid4().hex[:8], cleaned_label, cleaned_host)
            self.destinations.append(dest)
            self.save()
        self.start_probe(dest)
        self.publish()
        return dest.id

    def update_destination(self, dest_id: str, label: object, host: object) -> None:
        cleaned_label = clean_label(label)
        cleaned_host = clean_host(host)
        with self.lock:
            dest = self.destination(dest_id)
            if dest is None:
                raise KeyError(dest_id)
            dest.name = cleaned_label
            summary = dest.set_host(cleaned_host)
            if summary:
                self.record(dest, summary)
            self.save()
        self.publish()

    def remove_destination(self, dest_id: str) -> bool:
        with self.lock:
            dest = self.destination(dest_id)
            if dest is None:
                return False
            dest.removed = True
            self.destinations.remove(dest)
            self.save()
        self.publish()
        return True

    def probe_loop(self, dest: Destination) -> None:
        while not self.stop.is_set() and not dest.removed:
            started = time.monotonic()
            with self.lock:
                if dest.removed or dest not in self.destinations:
                    return
                host = dest.host
                depth = dest.depth()
            try:
                hops, error = probe(host, depth)
            except Exception as exc:  # noqa: BLE001
                hops, error = [], str(exc)
            elapsed = time.monotonic() - started
            with self.lock:
                if dest.removed or dest.host != host:
                    continue
                events = dest.apply_probe(hops, error, elapsed * 1000)
                for event in events:
                    self.record(dest, event["summary"])
            for hop in hops:
                self.resolver.want(hop.get("ip"))
            self.publish()
            remaining = self.interval - (time.monotonic() - started)
            if remaining > 0 and not dest.removed:
                self.stop.wait(remaining)

    def ack(self, dest_id: str) -> bool:
        with self.lock:
            dest = self.destination(dest_id)
            if dest is None:
                return False
            dest.ack()
        self.publish()
        return True


def make_handler(app: App):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt: str, *args) -> None:
            return

        def do_GET(self) -> None:  # noqa: N802
            path = self.path.split("?", 1)[0]
            if path in ("/", "/index.html"):
                self._send(200, "text/html; charset=utf-8", INDEX.read_bytes())
                return
            if path == "/api/state":
                body = json.dumps(app.snapshot(), separators=(",", ":")).encode()
                self._send(200, "application/json", body)
                return
            if path == "/api/events":
                self._stream()
                return
            self._send(404, "text/plain; charset=utf-8", b"Not found\n")

        def do_POST(self) -> None:  # noqa: N802
            path = self.path.split("?", 1)[0]
            length = int(self.headers.get("Content-Length", "0") or 0)
            if length > 8192:
                self._json(400, {"ok": False, "error": "That request is too large"})
                return
            raw = self.rfile.read(length) if length else b"{}"
            try:
                payload = json.loads(raw.decode() or "{}")
            except json.JSONDecodeError:
                self._json(400, {"ok": False, "error": "The request was not valid"})
                return
            if not isinstance(payload, dict):
                self._json(400, {"ok": False, "error": "The request was not valid"})
                return
            try:
                if path == "/api/ack":
                    ok = app.ack(str(payload.get("id", "")))
                    self._json(200 if ok else 404, {"ok": ok})
                    return
                if path == "/api/destinations":
                    dest_id = app.add_destination(payload.get("label"), payload.get("host"))
                    self._json(200, {"ok": True, "id": dest_id})
                    return
                if path == "/api/destinations/update":
                    app.update_destination(str(payload.get("id", "")), payload.get("label"), payload.get("host"))
                    self._json(200, {"ok": True})
                    return
                if path == "/api/destinations/remove":
                    ok = app.remove_destination(str(payload.get("id", "")))
                    self._json(200 if ok else 404, {"ok": ok})
                    return
            except ValueError as exc:
                self._json(400, {"ok": False, "error": str(exc)})
                return
            except KeyError:
                self._json(404, {"ok": False, "error": "That destination is gone"})
                return
            self._json(404, {"ok": False, "error": "Not found"})

        def _json(self, status: int, payload: dict) -> None:
            self._send(status, "application/json", json.dumps(payload).encode())

        def _send(self, status: int, content_type: str, body: bytes) -> None:
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _stream(self) -> None:
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-cache")
            self.send_header("Connection", "keep-alive")
            self.end_headers()
            generation = -1
            try:
                while not app.stop.is_set():
                    generation, payload, changed = app.hub.wait_next(generation)
                    if changed:
                        self.wfile.write(b"data: " + payload.encode() + b"\n\n")
                    else:
                        self.wfile.write(b": ping\n\n")
                    self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError, TimeoutError):
                return

    return Handler


def sample_hops(mapping: dict[int, str | None]) -> list[dict]:
    return [
        {"ttl": ttl, "ip": ip, "rtt_ms": 1.0 if ip else None}
        for ttl, ip in sorted(mapping.items())
    ]


def self_test() -> None:
    stdout = (
        "traceroute to 203.0.113.10 (203.0.113.10), 7 hops max, 40 byte packets\n"
        " 7  198.51.100.41  2.034 ms\n"
    )
    assert parse_hop(stdout, 7) == ("198.51.100.41", 2.034)
    assert parse_hop(" 8  *\n", 8) == (None, None)
    assert parse_hop(" 4  10.1.2.3  1.250 ms !X\n", 4) == ("10.1.2.3", 1.25)
    assert parse_hop("not a hop\n", 1) == (None, None)

    memory = PathMemory()
    steady = sample_hops({1: "10.0.0.1", 2: "1.2.3.4"})
    for _ in range(LEARN_SAMPLES):
        assert memory.note(steady, time.monotonic()) == []
    assert memory.note(sample_hops({1: "10.0.0.1", 2: "9.9.9.9"}), time.monotonic()) == []
    changed = memory.note(sample_hops({1: "10.0.0.1", 2: "9.9.9.9"}), time.monotonic())
    assert changed and changed[0]["kind"] == "alert"
    assert "9.9.9.9" in changed[0]["summary"]
    assert memory.mark(2, "9.9.9.9") == "changed"
    memory.ack()
    assert memory.alert is None
    assert memory.baseline[2] == {"9.9.9.9"}
    assert memory.note(sample_hops({1: "10.0.0.1", 2: "9.9.9.9"}), time.monotonic()) == []
    assert memory.note(sample_hops({1: "10.0.0.1", 2: "1.2.3.4"}), time.monotonic()) == []
    reverted = memory.note(sample_hops({1: "10.0.0.1", 2: "1.2.3.4"}), time.monotonic())
    assert reverted and "1.2.3.4" in reverted[0]["summary"]

    fill = PathMemory()
    for _ in range(LEARN_SAMPLES):
        assert fill.note(sample_hops({1: "10.0.0.1"}), time.monotonic()) == []
    assert fill.note(sample_hops({1: "10.0.0.1", 2: "5.5.5.5"}), time.monotonic()) == []
    assert fill.note(sample_hops({1: "10.0.0.1", 2: "5.5.5.5"}), time.monotonic()) == []
    assert "5.5.5.5" in fill.baseline.get(2, set())
    fill.started = time.monotonic() - (DISCOVER_SECONDS + 5)
    assert fill.note(sample_hops({1: "10.0.0.1", 2: "5.5.5.5", 3: "6.6.6.6"}), time.monotonic()) == []
    late = fill.note(sample_hops({1: "10.0.0.1", 2: "5.5.5.5", 3: "6.6.6.6"}), time.monotonic())
    assert late and late[0]["kind"] == "alert"

    gaps = PathMemory()
    for _ in range(LEARN_SAMPLES):
        gaps.note(sample_hops({1: "10.0.0.1", 4: "8.8.8.8"}), time.monotonic())
    assert 1 in gaps.always
    for _ in range(MISS_PROBES - 1):
        assert gaps.note(sample_hops({1: None, 4: "8.8.8.8"}), time.monotonic()) == []
    missing = gaps.note(sample_hops({1: None, 4: "8.8.8.8"}), time.monotonic())
    assert missing and "stopped answering" in missing[0]["summary"]
    recovered = gaps.note(sample_hops({1: "10.0.0.1", 4: "8.8.8.8"}), time.monotonic())
    assert recovered == []
    assert gaps.alert is None

    both = PathMemory()
    for _ in range(LEARN_SAMPLES):
        both.note(sample_hops({1: "10.0.0.1", 2: "1.2.3.4"}), time.monotonic())
    assert both.note(sample_hops({1: "10.0.0.1", 2: "9.9.9.9"}), time.monotonic()) == []
    assert both.note(sample_hops({1: "10.0.0.1", 2: "9.9.9.9"}), time.monotonic())
    for _ in range(MISS_PROBES - 1):
        assert both.note(sample_hops({1: None, 2: "9.9.9.9"}), time.monotonic()) == []
    combined = both.note(sample_hops({1: None, 2: "9.9.9.9"}), time.monotonic())
    assert combined and "stopped answering" in combined[0]["summary"]
    assert "9.9.9.9" in combined[0]["summary"]
    assert both.mark(1, None) == "missing"
    assert both.mark(2, "9.9.9.9") == "changed"

    flaky = PathMemory()
    for i in range(LEARN_SAMPLES):
        ip = "4.4.4.4" if i < 4 else None
        flaky.note(sample_hops({1: "10.0.0.1", 3: ip}), time.monotonic())
    assert 3 not in flaky.always
    assert flaky.note(sample_hops({1: "10.0.0.1", 3: None}), time.monotonic()) == []

    assert clean_label("  Sydney gateway  ") == "Sydney gateway"
    assert clean_host("203.0.113.10") == "203.0.113.10"
    assert clean_host("gw1.example") == "gw1.example"
    for bad in ("", "1.2.3.999", "not a host", "10.0.0.1;id"):
        try:
            clean_host(bad)
        except ValueError:
            continue
        raise AssertionError(bad)

    dest = Destination("lab", "Example", "203.0.113.10")
    assert dest.set_host("203.0.113.10") is None
    moved = dest.set_host("203.0.113.20")
    assert moved and "203.0.113.20" in moved
    assert dest.address_alert is not None
    dest.ack()
    assert dest.address_alert is None
    dest.name = "Example path"
    assert dest.to_json({})["label"] == "Example path"

    print("self-test ok")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--interval", type=float, default=1.0)
    parser.add_argument("--no-open", action="store_true", help="Do not open a browser")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return

    if not INDEX.exists():
        sys.exit(f"Missing {INDEX}")
    if args.interval <= 0:
        sys.exit("--interval must be greater than 0")

    app = App(args.interval, STORE)
    with app.lock:
        app.load()
    for dest in app.destinations:
        print(f"{dest.name}  {dest.host}", flush=True)
        app.start_probe(dest)

    app.resolver.start()

    handler = make_handler(app)

    class QuietServer(ThreadingHTTPServer):
        def handle_error(self, request, client_address) -> None:
            exc = sys.exc_info()[1]
            if isinstance(exc, (ConnectionResetError, BrokenPipeError, TimeoutError)):
                return
            super().handle_error(request, client_address)

    try:
        server = QuietServer(("127.0.0.1", args.port), handler)
    except OSError as exc:
        sys.exit(f"Could not listen on 127.0.0.1:{args.port}: {exc}")

    url = f"http://127.0.0.1:{args.port}/"
    print(f"Route watch  {url}", flush=True)
    print(f"Checking every {args.interval:g}s. Stop with Ctrl-C.", flush=True)
    if not args.no_open:
        threading.Timer(0.4, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.", flush=True)
    finally:
        app.stop.set()
        server.server_close()


if __name__ == "__main__":
    main()
