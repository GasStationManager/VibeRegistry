#!/usr/bin/env python3
"""Adopt informal statements from an entry's upstream project.

A human sign-off asks one question: *does this Lean statement say the thing the
mathematics says?* Answering it means having the informal statement in front of
you. Most serious projects already wrote one down — this script goes and gets it
instead of making the reviewer hunt:

  blueprint   leanblueprint LaTeX (`blueprint/src/**/*.tex`), where
              `\\lean{Foo.bar}` already ties a prose statement to a declaration
  yaml        formalization.yaml (the Mathlib Initiative standard, also used by
              Palomar submissions) or LeanPool's projects.yml — any YAML with a
              list of results carrying a declaration name and an informal text

Output: informal/<entry-id>.json, consumed by generate_signoff_packet.py and
build_search_index.py.

Usage:
    fetch_blueprint_statements.py entries/<id>.toml [--repo-dir DIR]
                                  [--source auto|blueprint|yaml] [--stdout]

With no --repo-dir the impl repo is fetched at the entry's pinned commit into
work/<entry-id>/upstream (shallow, one commit).
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config  # noqa: E402

# leanblueprint environments that carry a statement worth showing a reviewer.
STATEMENT_ENVS = (
    "theorem", "lemma", "proposition", "corollary", "definition",
    "conjecture", "claim", "fact",
)

_ENV_RE = re.compile(
    r"\\begin\{(?P<env>" + "|".join(STATEMENT_ENVS) + r")\}"
    r"(?P<opts>\[[^\]]*\])?"
    r"(?P<body>.*?)"
    r"\\end\{(?P=env)\}",
    re.DOTALL,
)
_LEAN_RE = re.compile(r"\\lean\{(?P<names>[^}]*)\}")
_LABEL_RE = re.compile(r"\\label\{(?P<label>[^}]*)\}")
_LEANOK_RE = re.compile(r"\\leanok\b")
# Blueprint bookkeeping macros: metadata for the blueprint graph, noise here.
_STRIP_RE = re.compile(r"\\(?:lean|label|uses|leanok|proves|notready|discussion)\b(?:\{[^}]*\})?")


def _clean_latex(body: str) -> str:
    text = _STRIP_RE.sub("", body)
    text = re.sub(r"%.*", "", text)
    text = re.sub(r"\n\s*\n\s*\n+", "\n\n", text)
    return text.strip()


def parse_blueprint(text: str, source_file: str):
    """Extract declaration -> informal statement from one blueprint .tex file."""
    found = {}
    for m in _ENV_RE.finditer(text):
        body = m.group("body")
        lean = _LEAN_RE.search(body)
        if not lean:
            continue  # no declaration tied to it — nothing to pair with a spec
        names = [n.strip() for n in lean.group("names").split(",") if n.strip()]
        label = _LABEL_RE.search(body)
        opts = (m.group("opts") or "").strip("[]").strip()
        line = text.count("\n", 0, m.start()) + 1
        record = {
            "kind": m.group("env"),
            "title": opts,
            "label": label.group("label") if label else "",
            "statement": _clean_latex(body),
            "leanok": bool(_LEANOK_RE.search(body)),
            "source_file": source_file,
            "line": line,
            "origin": "blueprint",
        }
        for name in names:
            found[name] = record
    return found


# YAML shapes we understand. Both formalization.yaml and LeanPool's projects.yml
# describe results as "this declaration means this in words"; the key names
# differ, so accept the common spellings rather than one exact schema.
_RESULT_LIST_KEYS = ("main_results", "results", "theorems", "declarations", "statements")
_DECL_KEYS = ("declaration", "name", "lean", "lean_name", "decl")
_INFORMAL_KEYS = ("informal", "statement", "informal_statement", "description", "summary")


def _walk_results(node, out, source_file):
    """Recursively find result lists anywhere in a YAML document."""
    if isinstance(node, dict):
        for key, value in node.items():
            if key in _RESULT_LIST_KEYS and isinstance(value, list):
                for item in value:
                    if not isinstance(item, dict):
                        continue
                    decl = next((item[k] for k in _DECL_KEYS if item.get(k)), None)
                    informal = next((item[k] for k in _INFORMAL_KEYS if item.get(k)), None)
                    if not decl or not informal:
                        continue
                    for name in [n.strip() for n in str(decl).split(",") if n.strip()]:
                        out[name] = {
                            "kind": item.get("kind", "theorem"),
                            "title": str(item.get("title", "")).strip(),
                            "label": "",
                            "statement": str(informal).strip(),
                            "leanok": True,
                            "source_file": source_file,
                            "line": 0,
                            "origin": "yaml",
                        }
            _walk_results(value, out, source_file)
    elif isinstance(node, list):
        for item in node:
            _walk_results(item, out, source_file)


def parse_yaml_results(path: str, rel_path: str):
    try:
        import yaml
    except ImportError:
        print("ERROR: PyYAML is required to read YAML statement sources "
              "(pip install pyyaml)", file=sys.stderr)
        return {}
    with open(path) as f:
        try:
            doc = yaml.safe_load(f)
        except Exception as exc:  # noqa: BLE001 - upstream file, any error is theirs
            print(f"  WARNING: could not parse {rel_path}: {exc}", file=sys.stderr)
            return {}
    out = {}
    _walk_results(doc, out, rel_path)
    return out


def fetch_repo(url: str, commit: str, dest: str) -> str:
    """Shallow-fetch exactly the pinned commit."""
    if os.path.isdir(os.path.join(dest, ".git")):
        print(f"Reusing checkout: {dest}")
        subprocess.run(["git", "-C", dest, "checkout", "-q", commit], check=True)
        return dest
    os.makedirs(dest, exist_ok=True)
    print(f"Fetching {url} @ {commit[:12]} into {dest}")
    subprocess.run(["git", "-C", dest, "init", "-q"], check=True)
    subprocess.run(["git", "-C", dest, "remote", "add", "origin", url], check=True)
    subprocess.run(["git", "-C", dest, "fetch", "-q", "--depth", "1", "origin", commit], check=True)
    subprocess.run(["git", "-C", dest, "checkout", "-q", "FETCH_HEAD"], check=True)
    return dest


def collect(repo_dir: str, source: str):
    """Gather informal statements from a checked-out repo."""
    statements = {}
    files = []

    if source in ("auto", "blueprint"):
        blueprint_dir = os.path.join(repo_dir, "blueprint")
        for root, _dirs, names in os.walk(blueprint_dir):
            for name in sorted(names):
                if not name.endswith(".tex"):
                    continue
                path = os.path.join(root, name)
                rel = os.path.relpath(path, repo_dir)
                with open(path, errors="replace") as f:
                    found = parse_blueprint(f.read(), rel)
                if found:
                    files.append(rel)
                    statements.update(found)

    if source in ("auto", "yaml"):
        candidates = ["formalization.yaml", "formalization.yml", "projects.yml"]
        for rel in candidates:
            path = os.path.join(repo_dir, rel)
            if os.path.isfile(path):
                found = parse_yaml_results(path, rel)
                if found:
                    files.append(rel)
                    # Blueprint statements win: they are written against the
                    # declaration, while YAML summaries are often per-project.
                    for name, record in found.items():
                        statements.setdefault(name, record)

    return statements, files


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("entry", help="entries/<id>.toml")
    ap.add_argument("--repo-dir", help="existing checkout of the impl repo")
    ap.add_argument("--source", choices=("auto", "blueprint", "yaml"), default="auto")
    ap.add_argument("--stdout", action="store_true", help="print instead of writing")
    args = ap.parse_args()

    config = load_config(args.entry)
    entry_id = config["project"]["id"]
    url = config["project"]["url"]
    commit = config["project"].get("commit", "")

    repo_dir = args.repo_dir
    if not repo_dir:
        default_repo = os.path.join(PROJECT_DIR, "work", entry_id, "repo")
        if os.path.isdir(default_repo):
            repo_dir = default_repo
        else:
            repo_dir = fetch_repo(
                url, commit, os.path.join(PROJECT_DIR, "work", entry_id, "upstream")
            )

    statements, files = collect(repo_dir, args.source)

    registered = []
    for group in config.get("theorems", []):
        registered.extend(group.get("names", []))

    matched = sorted(n for n in registered if n in statements)
    unmatched = sorted(n for n in registered if n not in statements)

    doc = {
        "entry_id": entry_id,
        "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source": {
            "repository": url,
            "commit": commit,
            "files": files,
            "mode": args.source,
        },
        "coverage": {
            "registered": len(registered),
            "matched": len(matched),
            "unmatched": unmatched,
        },
        # Keep every statement found, not just matched ones: an unmatched name
        # is often a spelling difference a reviewer can fix by hand.
        "statements": statements,
    }

    text = json.dumps(doc, indent=2, ensure_ascii=False) + "\n"
    if args.stdout:
        print(text, end="")
    else:
        out_dir = os.path.join(PROJECT_DIR, "informal")
        os.makedirs(out_dir, exist_ok=True)
        out_path = os.path.join(out_dir, f"{entry_id}.json")
        with open(out_path, "w") as f:
            f.write(text)
        print(f"Wrote {out_path}")

    print(f"  sources: {', '.join(files) if files else 'none found'}")
    print(f"  informal statements found: {len(statements)}")
    print(f"  registered declarations covered: {len(matched)}/{len(registered)}")
    if unmatched:
        print(f"  no informal statement for: {', '.join(unmatched)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
