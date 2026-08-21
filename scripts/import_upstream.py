#!/usr/bin/env python3
"""Import entries from upstream Lean registries, so VibeRegistry can overlay them.

Palomar and LeanPool both publish machine-checked Lean formalizations, and
neither has a human sign-off step: Palomar's statement-fidelity judgment is made
by a language model, LeanPool's fit-and-significance review likewise. VibeRegistry
does have one. So rather than re-verify what they already verified, we mirror
their records and add the layer they are missing — the same relation an overlay
journal has to arXiv.

Sources:
  palomar   https://data.palomar-registry.org/recent.json  (JSON feed, schema 2)
  leanpool  LeanPool/projects.yml from Vilin97/lean-pool   (YAML project index)

Output:
  overlay/<source>/<upstream-id>.json   one normalized record per upstream entry
  overlay/index.json                    merged view, with our sign-offs attached

Our sign-offs live in overlay/signoffs.toml and are never written by this script,
so re-importing cannot clobber human review. A sign-off records the hash of the
statement text it reviewed; when upstream publishes a new version of that entry,
the hash stops matching and the sign-off is reported as stale.

Usage:
    import_upstream.py --source palomar [--limit N] [--dry-run]
    import_upstream.py --source leanpool [--limit N]
    import_upstream.py --all
    import_upstream.py --reindex          # rebuild overlay/index.json only
"""

from __future__ import annotations

import argparse
import datetime as dt
import glob
import hashlib
import json
import os
import sys
import urllib.request

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config  # noqa: E402

OVERLAY_DIR = os.path.join(PROJECT_DIR, "overlay")
SIGNOFFS_PATH = os.path.join(OVERLAY_DIR, "signoffs.toml")

SOURCES = {
    "palomar": {
        "url": "https://data.palomar-registry.org/recent.json",
        "home": "https://palomar-registry.org/",
        "human_signoff": False,
        "note": "Comparator + Lean and NanoDa kernels; statement fidelity judged by an LLM.",
    },
    "leanpool": {
        "url": "https://raw.githubusercontent.com/Vilin97/lean-pool/main/LeanPool/projects.yml",
        "home": "https://github.com/Vilin97/lean-pool",
        "human_signoff": False,
        "note": "Mathlib linters + repo quality gates + LLM review of fit and significance.",
    },
}

USER_AGENT = "VibeRegistry-overlay/1.0 (+https://github.com/GasStationManager/VibeRegistry)"


def fetch(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return resp.read()


def statement_hash(record) -> str:
    """Hash the parts a reviewer actually reads, so upstream edits invalidate a sign-off."""
    payload = json.dumps(
        {
            "declarations": sorted(record.get("declarations", [])),
            "informal": record.get("informal", {}),
            "commit": record.get("commit", ""),
        },
        sort_keys=True,
        ensure_ascii=False,
    )
    return "sha256:" + hashlib.sha256(payload.encode()).hexdigest()


def normalize_palomar(entry):
    source = entry.get("source", {}) or {}
    formalization = entry.get("formalization", {}) or {}
    classification = entry.get("classification", {}) or {}
    repo = source.get("repository", "")
    upstream_id = entry.get("id", "")
    version = entry.get("version", 1)
    record = {
        "source": "palomar",
        "upstream_id": upstream_id,
        "upstream_url": f"https://palomar-registry.org/{upstream_id}",
        "version": version,
        "title": entry.get("title", repo),
        "abstract": entry.get("abstract", ""),
        "authors": [a.get("name", "") for a in entry.get("authors", []) if isinstance(a, dict)],
        "repository": f"https://github.com/{repo}" if repo and "://" not in repo else repo,
        "commit": source.get("commit", ""),
        "project_path": source.get("project_path"),
        "declarations": list(formalization.get("theorem_names", []) or []),
        # Palomar's feed carries an abstract per entry, not per declaration.
        "informal": {},
        "classification": {
            "arxiv": classification.get("arxiv", []),
            "msc2020": classification.get("msc2020", []),
        },
        "license": entry.get("license", ""),
        "published_at": entry.get("published_at", ""),
        "status": entry.get("status", ""),
        "upstream_checks": {
            "comparator": True,
            "kernels": ["lean", "nanoda"],
            "human_signoff": False,
            "llm_review": True,
        },
        "preservation": entry.get("preservation", {}),
    }
    record["statement_hash"] = statement_hash(record)
    return record


def normalize_leanpool(project):
    source = project.get("source", {}) or {}
    slug = project.get("slug", "")
    github_repo = source.get("github_repo", "")
    informal = {}
    for result in project.get("main_results", []) or []:
        if not isinstance(result, dict):
            continue
        decl = str(result.get("declaration", "")).strip()
        text = str(result.get("informal", "")).strip()
        if decl and text:
            informal[decl] = text
    declarations = [str(d).strip() for d in (project.get("main_declarations") or [])]
    for decl in informal:
        if decl not in declarations:
            declarations.append(decl)
    record = {
        "source": "leanpool",
        "upstream_id": slug,
        "upstream_url": f"https://github.com/Vilin97/lean-pool/tree/main/"
                        f"{str(project.get('entry_module', '')).replace('.', '/')}",
        "version": 1,
        "title": project.get("title", slug),
        "abstract": str(project.get("summary", "")).strip(),
        "authors": [str(a) for a in (project.get("authors") or [])],
        "repository": f"https://github.com/{github_repo}" if github_repo else "",
        "commit": "",  # LeanPool vendors projects; it pins Mathlib, not upstream commits
        "entry_module": project.get("entry_module", ""),
        "declarations": declarations,
        "informal": informal,
        "classification": {
            "msc2020": [str(m) for m in (project.get("msc") or [])],
            "tags": [str(t) for t in (project.get("tags") or [])],
            "branch": project.get("branch", ""),
        },
        "license": project.get("license", ""),
        "published_at": "",
        "status": project.get("status", ""),
        "provenance": project.get("provenance", ""),
        "upstream_checks": {
            "comparator": False,
            "kernels": ["lean"],
            "human_signoff": False,
            "llm_review": True,
            "sorry_free": True,
        },
    }
    record["statement_hash"] = statement_hash(record)
    return record


def import_palomar(limit=None):
    data = json.loads(fetch(SOURCES["palomar"]["url"]))
    entries = data.get("entries", [])
    if limit:
        entries = entries[:limit]
    return [normalize_palomar(e) for e in entries]


def import_leanpool(limit=None):
    try:
        import yaml
    except ImportError:
        print("ERROR: PyYAML required for the leanpool source (pip install pyyaml)",
              file=sys.stderr)
        return []
    doc = yaml.safe_load(fetch(SOURCES["leanpool"]["url"]).decode("utf-8"))
    projects = doc.get("projects", []) if isinstance(doc, dict) else []
    if limit:
        projects = projects[:limit]
    return [normalize_leanpool(p) for p in projects]


IMPORTERS = {"palomar": import_palomar, "leanpool": import_leanpool}


def safe_filename(upstream_id: str) -> str:
    return "".join(c if c.isalnum() or c in "-._" else "-" for c in upstream_id) or "entry"


def write_records(source, records, dry_run=False):
    out_dir = os.path.join(OVERLAY_DIR, source)
    if not dry_run:
        os.makedirs(out_dir, exist_ok=True)
    written = 0
    for record in records:
        path = os.path.join(out_dir, safe_filename(record["upstream_id"]) + ".json")
        text = json.dumps(record, indent=2, ensure_ascii=False) + "\n"
        if dry_run:
            print(f"  would write {os.path.relpath(path, PROJECT_DIR)}")
            continue
        old = None
        if os.path.isfile(path):
            with open(path) as f:
                old = f.read()
        if old != text:
            with open(path, "w") as f:
                f.write(text)
            written += 1
    return written


def load_overlay_signoffs():
    """Read overlay/signoffs.toml (hand-maintained; never written by this script)."""
    if not os.path.isfile(SIGNOFFS_PATH):
        return []
    config = load_config(SIGNOFFS_PATH)
    return config.get("signoff", []) or []


def attach_signoffs(record, signoffs):
    """Attach our sign-offs, flagging any whose reviewed statement has since changed."""
    attached = []
    for s in signoffs:
        if s.get("source") != record["source"]:
            continue
        if str(s.get("upstream_id")) != str(record["upstream_id"]):
            continue
        declarations = s.get("declarations") or ["*"]
        reviewed_hash = s.get("statement_hash", "")
        stale = bool(reviewed_hash) and reviewed_hash != record["statement_hash"]
        attached.append({
            "github_user": s.get("github_user", ""),
            "date": s.get("date", ""),
            "issue": s.get("issue"),
            "verdict": s.get("verdict", "approved"),
            "declarations": declarations,
            "comment": s.get("comment", ""),
            "status": "stale" if stale else "current",
        })
    record["signoffs"] = attached
    record["has_human_signoff"] = any(
        a["status"] == "current" and a["verdict"] == "approved" for a in attached
    )
    return record


def reindex():
    signoffs = load_overlay_signoffs()
    records = []
    for source in sorted(SOURCES):
        for path in sorted(glob.glob(os.path.join(OVERLAY_DIR, source, "*.json"))):
            with open(path) as f:
                record = json.load(f)
            records.append(attach_signoffs(record, signoffs))

    index = {
        "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "sources": {
            name: {
                "home": meta["home"],
                "feed": meta["url"],
                "human_signoff": meta["human_signoff"],
                "note": meta["note"],
                "count": sum(1 for r in records if r["source"] == name),
            }
            for name, meta in SOURCES.items()
        },
        "signed_off": sum(1 for r in records if r.get("has_human_signoff")),
        "records": records,
    }
    os.makedirs(OVERLAY_DIR, exist_ok=True)
    path = os.path.join(OVERLAY_DIR, "index.json")
    with open(path, "w") as f:
        json.dump(index, f, indent=2, ensure_ascii=False)
        f.write("\n")
    print(f"Wrote {os.path.relpath(path, PROJECT_DIR)}: {len(records)} record(s), "
          f"{index['signed_off']} with a current human sign-off")
    return index


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", choices=sorted(SOURCES))
    ap.add_argument("--all", action="store_true", help="import every known source")
    ap.add_argument("--limit", type=int, help="import at most N entries")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--reindex", action="store_true", help="rebuild overlay/index.json only")
    args = ap.parse_args()

    if args.reindex and not (args.source or args.all):
        reindex()
        return 0

    if not args.source and not args.all:
        ap.error("give --source, --all, or --reindex")

    sources = sorted(SOURCES) if args.all else [args.source]
    for source in sources:
        print(f"Importing {source} from {SOURCES[source]['url']}")
        try:
            records = IMPORTERS[source](args.limit)
        except Exception as exc:  # noqa: BLE001 - network/format errors are expected here
            print(f"  ERROR: {exc}", file=sys.stderr)
            continue
        written = write_records(source, records, args.dry_run)
        with_informal = sum(1 for r in records if r.get("informal"))
        print(f"  {len(records)} record(s), {written} written/updated, "
              f"{with_informal} carry per-declaration informal statements")

    if not args.dry_run:
        reindex()
    return 0


if __name__ == "__main__":
    sys.exit(main())
