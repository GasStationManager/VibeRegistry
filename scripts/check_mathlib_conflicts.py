#!/usr/bin/env python3
"""Flag spec declarations that collide with Mathlib's.

A registry of statements is only readable if names mean what they normally mean.
Spec files legitimately *replicate* definitions from the implementation so a
statement can be written standalone (CLAUDE.md, rule 2) — but a replicated
definition that lands on a name Mathlib already owns is a different thing: the
statement then reads like Mathlib's notion and means the spec's. That is exactly
the failure a reader of the registry cannot catch by eye, so it gets checked.

What is reported:
  conflict  a spec declares a fully-qualified name that exists in Mathlib
  warning   a spec sets an `attribute`/`export`/`instance` on a Mathlib name,
            which can change how existing Mathlib declarations elaborate

An entry may record deliberate exceptions:

    [[mathlib_conflict_exemptions]]
    name = "Polynomial.myVariant"
    reason = "Upstream renamed this in Mathlib after the pinned revision."

Needs the name list from fetch_mathlib_names.py.

Usage:
    check_mathlib_conflicts.py [entries/<id>.toml ...] [--json] [--names-file PATH]
    check_mathlib_conflicts.py --all
Exit codes: 0 clean, 1 conflicts found, 2 setup problem.
"""

from __future__ import annotations

import argparse
import glob
import gzip
import json
import os
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config  # noqa: E402
from lean_decls import find_declarations  # noqa: E402

DEFAULT_NAMES = os.path.join(PROJECT_DIR, "data", "mathlib-names.tsv.gz")

_ATTRIBUTE_RE = re.compile(r"^\s*attribute\s*\[(?P<attrs>[^\]]*)\]\s*(?P<targets>.+?)\s*$")
_EXPORT_RE = re.compile(r"^\s*export\s+(?P<ns>\S+)\s*\((?P<names>[^)]*)\)")


def load_mathlib_names(path):
    if not os.path.isfile(path):
        return None
    names = {}
    with gzip.open(path, "rt") as f:
        for line in f:
            name, _, kind = line.rstrip("\n").partition("\t")
            if name:
                names[name] = kind
    return names


def spec_files_for(entry_id, config):
    """Every spec file an entry's theorem groups point at."""
    seen = []
    for group in config.get("theorems", []):
        module = group.get("spec_module", "")
        if not module:
            continue
        rel = module.replace(".", "/") + ".lean"
        path = os.path.join(PROJECT_DIR, "specs", entry_id, rel)
        if path not in seen:
            seen.append(path)
    return seen


def check_file(path, mathlib, exemptions):
    """Return (conflicts, warnings) for one spec file."""
    conflicts, warnings = [], []
    rel = os.path.relpath(path, PROJECT_DIR)
    if not os.path.isfile(path):
        warnings.append({"file": rel, "line": 0, "kind": "missing-spec",
                         "message": f"spec file not found: {rel}"})
        return conflicts, warnings

    with open(path, errors="replace") as f:
        text = f.read()

    for decl in find_declarations(text):
        if decl.name in exemptions:
            continue
        mathlib_kind = mathlib.get(decl.name)
        if mathlib_kind is None:
            continue
        conflicts.append({
            "file": rel,
            "line": decl.start_line,
            "kind": "shadows-mathlib",
            "name": decl.name,
            "spec_kind": decl.kind,
            "mathlib_kind": mathlib_kind,
            "message": (
                f"{decl.kind} `{decl.name}` has the same fully-qualified name as a "
                f"Mathlib {mathlib_kind}. A reader will assume Mathlib's meaning."
            ),
        })

    for lineno, line in enumerate(text.split("\n"), start=1):
        attr = _ATTRIBUTE_RE.match(line)
        if attr:
            targets = [t for t in re.split(r"[\s,]+", attr.group("targets")) if t]
            hit = [t for t in targets if t in mathlib and t not in exemptions]
            if hit:
                warnings.append({
                    "file": rel, "line": lineno, "kind": "attribute-on-mathlib",
                    "name": ", ".join(hit),
                    "message": (
                        f"sets [{attr.group('attrs').strip()}] on Mathlib declaration(s) "
                        f"{', '.join(hit)}; this changes elaboration for everything "
                        f"built on top of them."
                    ),
                })
        exp = _EXPORT_RE.match(line)
        if exp:
            warnings.append({
                "file": rel, "line": lineno, "kind": "export",
                "name": exp.group("ns"),
                "message": f"`export {exp.group('ns')}` can make unqualified names "
                           f"resolve differently than a reader expects.",
            })

    return conflicts, warnings


def check_entry(entry_path, mathlib):
    config = load_config(entry_path)
    entry_id = config["project"]["id"]
    exemptions = {
        e.get("name"): e.get("reason", "")
        for e in config.get("mathlib_conflict_exemptions", []) or []
        if e.get("name")
    }
    conflicts, warnings = [], []
    for path in spec_files_for(entry_id, config):
        c, w = check_file(path, mathlib, exemptions)
        conflicts.extend(c)
        warnings.extend(w)
    return {
        "entry_id": entry_id,
        "exemptions": exemptions,
        "conflicts": conflicts,
        "warnings": warnings,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("entries", nargs="*", help="entries/<id>.toml (default: --all)")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--names-file", default=DEFAULT_NAMES)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    mathlib = load_mathlib_names(args.names_file)
    if mathlib is None:
        print(
            f"ERROR: Mathlib name list not found at {args.names_file}\n"
            f"       Run: python3 scripts/fetch_mathlib_names.py",
            file=sys.stderr,
        )
        return 2

    entries = args.entries or sorted(glob.glob(os.path.join(PROJECT_DIR, "entries", "*.toml")))
    reports = [check_entry(e, mathlib) for e in entries]

    if args.json:
        print(json.dumps({"entries": reports, "mathlib_declarations": len(mathlib)}, indent=2))
    else:
        total_c = total_w = 0
        for report in reports:
            print(f"{report['entry_id']}: "
                  f"{len(report['conflicts'])} conflict(s), {len(report['warnings'])} warning(s)")
            for c in report["conflicts"]:
                print(f"  CONFLICT {c['file']}:{c['line']}: {c['message']}")
            for w in report["warnings"]:
                print(f"  warning  {w['file']}:{w['line']}: {w['message']}")
            total_c += len(report["conflicts"])
            total_w += len(report["warnings"])
        print(f"\nChecked against {len(mathlib)} Mathlib declarations: "
              f"{total_c} conflict(s), {total_w} warning(s)")

    return 1 if any(r["conflicts"] for r in reports) else 0


if __name__ == "__main__":
    sys.exit(main())
