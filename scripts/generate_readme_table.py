#!/usr/bin/env python3
"""
Generate the Registry Entries table for README.md from entry configs and results.

Reads registry.toml for the entry list, each entry's TOML for metadata and
sign-offs, and results/<id>/latest.json for verification status.

Usage:
    python3 scripts/generate_readme_table.py          # print table to stdout
    python3 scripts/generate_readme_table.py --update  # update README.md in-place
"""

import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config, get_field

# Markers in README.md that delimit the auto-generated table
TABLE_BEGIN = "<!-- BEGIN REGISTRY TABLE -->"
TABLE_END = "<!-- END REGISTRY TABLE -->"


def count_theorems(config):
    """Count total theorem/declaration names across all groups."""
    total = 0
    for group in config.get("theorems", []):
        total += len(group.get("names", []))
    return total


def describe_theorems(entry_id, config):
    """Short human-readable description of the theorems."""
    descriptions = {
        "artificial-theorems": "Robbins-Siegmund, SGD convergence, Value Iteration",
        "stat-learning": "Gaussian concentration, Dudley's integral, Efron-Stein, Poincare",
    }
    count = count_theorems(config)
    desc = descriptions.get(entry_id, "")
    if desc:
        return f"{desc} ({count} theorems)"
    return f"{count} theorems"


def load_results(entry_id):
    """Load latest results JSON, or None if missing."""
    path = os.path.join(PROJECT_DIR, "results", entry_id, "latest.json")
    if not os.path.isfile(path):
        return None
    with open(path) as f:
        return json.load(f)


def format_verification(results):
    """Format verification level and status."""
    if results is None:
        return "—", "Pending"
    level = results.get("verification_level", 0)
    overall = results.get("overall", "unknown")
    level_str = f"Level {level}" if level else "—"
    status = "Verified" if overall == "pass" else "Failed" if overall == "fail" else "Pending"
    return level_str, status


def format_signoffs(config):
    """Format sign-off summary."""
    signoffs = config.get("signoffs", [])
    if not signoffs:
        return "—"
    current = sum(1 for s in signoffs if s.get("status") == "current")
    total = len(signoffs)
    if current == total:
        return f"{current} sign-off{'s' if current != 1 else ''}"
    return f"{current}/{total} current"


def generate_table():
    """Generate the markdown table."""
    registry = load_config(os.path.join(PROJECT_DIR, "registry.toml"))
    entries = registry.get("entries", [])

    rows = []
    for entry in entries:
        entry_id = entry["id"]
        config_path = os.path.join(PROJECT_DIR, entry["config"])
        config = load_config(config_path)

        name = get_field(config, "project.name")
        url = get_field(config, "project.url")
        toolchain = get_field(config, "lean.toolchain")
        # Extract just the version from e.g. "leanprover/lean4:v4.27.0"
        lean_ver = toolchain.split(":")[-1] if ":" in toolchain else toolchain

        theorems_desc = describe_theorems(entry_id, config)
        results = load_results(entry_id)
        verification, status = format_verification(results)
        signoffs = format_signoffs(config)

        rows.append(
            f"| [{name}]({url}) | {theorems_desc} | {lean_ver} | {verification} | {signoffs} | {status} |"
        )

    header = "| Entry | Theorems | Lean | Verification | Sign-offs | Status |"
    separator = "|-------|----------|------|--------------|-----------|--------|"
    lines = [header, separator] + rows
    return "\n".join(lines)


def main():
    table = generate_table()
    update = "--update" in sys.argv

    if not update:
        print(table)
        return

    readme_path = os.path.join(PROJECT_DIR, "README.md")
    with open(readme_path) as f:
        content = f.read()

    if TABLE_BEGIN in content and TABLE_END in content:
        before = content[: content.index(TABLE_BEGIN) + len(TABLE_BEGIN)]
        after = content[content.index(TABLE_END) :]
        content = before + "\n" + table + "\n" + after
    else:
        print("WARNING: Table markers not found in README.md — cannot update", file=sys.stderr)
        print("Add these markers around the table:", file=sys.stderr)
        print(f"  {TABLE_BEGIN}", file=sys.stderr)
        print(f"  {TABLE_END}", file=sys.stderr)
        sys.exit(1)

    with open(readme_path, "w") as f:
        f.write(content)

    print("README.md updated.")


if __name__ == "__main__":
    main()
