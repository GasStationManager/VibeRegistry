#!/usr/bin/env python3
"""Hash the exact spec statement behind each registered declaration.

A verdict is about one statement, not about a name. Without this, a spec file can
be edited under an unchanged theorem name and the old `comparator: pass` still
reads as current for the new statement — the registry would be publishing a
verdict for text nobody checked.

So each run records, per declaration, the hash of the declaration source it
verified. Readers (build_search_index.py) recompute the hash from the current
spec and only show a verdict when it still matches.

Usage:
    spec_statement_hash.py entries/<id>.toml [--spec-dir DIR]

Prints JSON: {"<declaration>": "sha256:...", ...}. A declaration the scanner
cannot locate maps to "" — absent evidence, never a matching hash.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(os.path.dirname(SCRIPT_DIR))
sys.path.insert(0, SCRIPT_DIR)

from parse_toml import load_config  # noqa: E402
from lean_decls import find_declaration  # noqa: E402


def statement_hashes(config, spec_dir):
    """declaration name -> sha256 of its source text in the spec."""
    out = {}
    cache = {}
    for group in config.get("theorems", []):
        module = group.get("spec_module", "")
        if not module:
            continue
        path = os.path.join(spec_dir, module.replace(".", "/") + ".lean")
        if path not in cache:
            try:
                with open(path, errors="replace") as f:
                    cache[path] = f.read()
            except OSError:
                cache[path] = None
        text = cache[path]
        for name in group.get("names", []):
            if text is None:
                out[name] = ""
                continue
            decl = find_declaration(text, name)
            if decl is None or not decl.source.strip():
                out[name] = ""
                continue
            # The declaration text alone: a verdict should survive edits
            # elsewhere in the file, and not survive edits to this statement.
            digest = hashlib.sha256(decl.source.strip().encode()).hexdigest()
            out[name] = f"sha256:{digest}"
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("entry")
    ap.add_argument("--spec-dir", help="defaults to specs/<entry id>/")
    args = ap.parse_args()

    config = load_config(args.entry)
    entry_id = config["project"]["id"]
    spec_dir = args.spec_dir or os.path.join(PROJECT_DIR, "specs", entry_id)

    print(json.dumps(statement_hashes(config, spec_dir), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
