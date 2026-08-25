#!/usr/bin/env python3
"""Check that spec files are standalone.

CLAUDE.md rule 1: a spec imports only Mathlib and other spec files. The reason is
the whole point of the registry — a spec is a *statement you can audit on its
own*. A spec that imports the implementation states its theorem in terms of
definitions the implementation supplies, so vetting the statement means vetting
the implementation too, and the separation the registry publishes is gone.

Palomar enforces the same property mechanically: a Challenge module's transitive
imports must resolve to Lean core or an allowlisted closure and nothing else.
This is our version of that rule, at the level of direct imports.

An entry may record a deliberate exception:

    [[spec_import_exemptions]]
    module = "Zip.Native.DeflateDynamic"
    reason = "Systems entry: the statement is about the impl's own encoder."

Usage:
    check_spec_imports.py [entries/<id>.toml ...] [--all] [--json]
Exit codes: 0 clean, 1 non-standalone imports found.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config  # noqa: E402

_IMPORT_RE = re.compile(r"^\s*import\s+(?P<module>[^\s]+)")

# Roots a standalone spec may import: Mathlib, our own spec tree, Lean core and
# the libraries Mathlib itself is built on.
ALLOWED_ROOTS = {"Mathlib", "Registry", "Init", "Std", "Lean", "Batteries", "Aesop", "Qq", "Plausible"}


def check_file(path, exemptions):
    rel = os.path.relpath(path, PROJECT_DIR)
    findings = []
    if not os.path.isfile(path):
        return [{"file": rel, "line": 0, "module": "", "kind": "missing-spec",
                 "message": f"spec file not found: {rel}"}]

    with open(path, errors="replace") as f:
        for lineno, line in enumerate(f.read().split("\n"), start=1):
            m = _IMPORT_RE.match(line)
            if not m:
                continue
            module = m.group("module")
            root = module.split(".")[0]
            if root in ALLOWED_ROOTS or module in exemptions:
                continue
            findings.append({
                "file": rel,
                "line": lineno,
                "module": module,
                "kind": "non-standalone-import",
                "message": (
                    f"imports `{module}`, which is outside Mathlib and the spec tree. "
                    f"The statement then depends on definitions the implementation "
                    f"supplies, so it cannot be audited on its own."
                ),
            })
    return findings


def check_entry(entry_path):
    config = load_config(entry_path)
    entry_id = config["project"]["id"]
    exemptions = {
        e.get("module"): e.get("reason", "")
        for e in config.get("spec_import_exemptions", []) or []
        if e.get("module")
    }
    seen, findings = [], []
    for group in config.get("theorems", []):
        module = group.get("spec_module", "")
        if not module:
            continue
        path = os.path.join(PROJECT_DIR, "specs", entry_id,
                            module.replace(".", "/") + ".lean")
        if path in seen:
            continue
        seen.append(path)
        findings.extend(check_file(path, exemptions))
    return {"entry_id": entry_id, "exemptions": exemptions, "findings": findings}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("entries", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    entries = args.entries or sorted(glob.glob(os.path.join(PROJECT_DIR, "entries", "*.toml")))
    reports = [check_entry(e) for e in entries]

    if args.json:
        print(json.dumps({"entries": reports}, indent=2))
    else:
        total = 0
        for report in reports:
            findings = report["findings"]
            print(f"{report['entry_id']}: {len(findings)} finding(s)"
                  + (f", {len(report['exemptions'])} exemption(s)" if report["exemptions"] else ""))
            for f in findings:
                print(f"  {f['file']}:{f['line']}: {f['message']}")
            total += len(findings)
        print(f"\n{total} non-standalone import(s)")

    return 1 if any(r["findings"] for r in reports) else 0


if __name__ == "__main__":
    sys.exit(main())
