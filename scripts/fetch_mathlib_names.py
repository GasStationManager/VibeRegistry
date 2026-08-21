#!/usr/bin/env python3
"""Build the Mathlib declaration-name list used by check_mathlib_conflicts.py.

Source: Mathlib's own doc-gen4 declaration data, which lists every declaration
in Mathlib and its dependencies with its kind. Using it means the collision
check needs no Lean toolchain and no Mathlib build.

    data/mathlib-names.tsv.gz    name<TAB>kind, sorted (gitignored: ~3 MB, derived)
    data/mathlib-names.meta.json provenance: source, date, count, digest (committed)

Caveat worth knowing: the published docs track current Mathlib, not the Mathlib
revision an entry pins. Declarations are added far more often than removed, so a
name found here is real; a name missing here may still exist in an older pinned
revision. The check is therefore a good detector of collisions and not a proof
of their absence — meta.json records exactly which snapshot was used.

Usage:
    fetch_mathlib_names.py [--url URL] [--out data/mathlib-names.tsv.gz]
"""

from __future__ import annotations

import argparse
import datetime as dt
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import sys
import urllib.request

PROJECT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_URL = "https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp"
DEFAULT_OUT = os.path.join(PROJECT_DIR, "data", "mathlib-names.tsv.gz")


USER_AGENT = "VibeRegistry/1.0 (+https://github.com/GasStationManager/VibeRegistry)"


def download(url: str, attempts: int = 3) -> bytes:
    """Fetch a large file, preferring curl.

    The document is ~70 MB and some proxies cut urllib's read short partway
    through, so retry and fall back rather than half-reading a truncated JSON.
    """
    if shutil.which("curl"):
        print(f"Fetching {url} (curl)")
        proc = subprocess.run(
            ["curl", "-sSL", "--fail", "--retry", "3", "-A", USER_AGENT, url],
            capture_output=True,
        )
        if proc.returncode == 0 and proc.stdout:
            return proc.stdout
        print(f"  curl failed ({proc.returncode}): {proc.stderr.decode()[:200]}", file=sys.stderr)

    last = None
    for attempt in range(1, attempts + 1):
        print(f"Fetching {url} (urllib, attempt {attempt}/{attempts})")
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(req, timeout=300) as resp:
                chunks = []
                while True:
                    chunk = resp.read(1 << 20)
                    if not chunk:
                        break
                    chunks.append(chunk)
                return b"".join(chunks)
        except Exception as exc:  # noqa: BLE001 - retry any transport failure
            last = exc
            print(f"  {type(exc).__name__}: {exc}", file=sys.stderr)
    raise SystemExit(f"ERROR: could not download {url}: {last}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--url", default=DEFAULT_URL)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--file", help="use an already-downloaded declaration-data file")
    args = ap.parse_args()

    if args.file:
        print(f"Reading {args.file}")
        with open(args.file, "rb") as f:
            raw = f.read()
    else:
        raw = download(args.url)
    print(f"  {len(raw) / 1e6:.1f} MB")

    data = json.loads(raw)
    declarations = data.get("declarations", {})
    if not declarations:
        print("ERROR: no declarations in the fetched document", file=sys.stderr)
        return 1

    rows = sorted((name, info.get("kind", "")) for name, info in declarations.items())

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    payload = "".join(f"{name}\t{kind}\n" for name, kind in rows).encode()
    with gzip.open(args.out, "wb") as f:
        f.write(payload)

    meta = {
        "source": args.url,
        "fetched_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "declarations": len(rows),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "file": os.path.relpath(args.out, PROJECT_DIR),
        "note": "Snapshot of current Mathlib docs; entries pin older Mathlib revisions.",
    }
    meta_path = os.path.join(os.path.dirname(args.out), "mathlib-names.meta.json")
    with open(meta_path, "w") as f:
        json.dump(meta, f, indent=2)
        f.write("\n")

    print(f"Wrote {os.path.relpath(args.out, PROJECT_DIR)} "
          f"({os.path.getsize(args.out) / 1e6:.1f} MB, {len(rows)} declarations)")
    print(f"Wrote {os.path.relpath(meta_path, PROJECT_DIR)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
