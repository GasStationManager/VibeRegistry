#!/usr/bin/env python3
"""
Filter comparator config files to only include theorem declarations.

The comparator tool only accepts thmInfo and axiomInfo constants.
Helper definitions (def, structure, etc.) cause "constant kind don't match"
errors. This script uses lean4export to determine which declarations are
theorems and filters configs accordingly.

Usage:
    python3 filter_comparator_theorems.py <repo_dir> <lean4export_bin> <config_dir>

Modifies config JSON files in-place. Removes configs with no theorems left.
"""

import sys
import os
import json
import subprocess


def get_decl_kinds(repo_dir, lean4export_bin, module, names):
    """Use lean4export to determine the kind (def/thm/ax/ind) of each name."""
    if not names:
        return {}

    cmd = [lean4export_bin, module, "--"] + names
    try:
        result = subprocess.run(
            ["lake", "env"] + cmd,
            capture_output=True, text=True, cwd=repo_dir, timeout=120
        )
    except subprocess.TimeoutExpired:
        print(f"  WARNING: lean4export timed out for {module}", file=sys.stderr)
        return {}

    if result.returncode != 0:
        print(f"  WARNING: lean4export failed for {module}: {result.stderr[:200]}",
              file=sys.stderr)
        return {}

    # Parse NDJSON output to build name index and find declaration entries
    name_table = {}  # idx -> (pre, str)
    decl_kinds = {}  # resolved_name -> kind

    for line in result.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue

        # Collect name entries: {"in": idx, "str": {"pre": pre_idx, "str": "name"}}
        if "in" in obj and "str" in obj:
            idx = obj["in"]
            pre = obj["str"].get("pre", 0)
            s = obj["str"].get("str", "")
            name_table[idx] = (pre, s)

        # Check for declaration entries
        for kind in ("def", "thm", "ax", "ind", "quot", "ctor", "rec"):
            if kind in obj:
                name_idx = obj[kind].get("name")
                if name_idx is not None:
                    resolved = _resolve_name(name_table, name_idx)
                    if resolved in names:
                        decl_kinds[resolved] = kind
                break

    return decl_kinds


def _resolve_name(name_table, idx):
    """Resolve a name index to a dotted string."""
    parts = []
    while idx in name_table:
        pre, s = name_table[idx]
        parts.append(s)
        idx = pre
    parts.reverse()
    return ".".join(parts)


def filter_configs(repo_dir, lean4export_bin, config_dir):
    """Filter all comparator configs to theorem-only names."""
    configs = sorted(f for f in os.listdir(config_dir) if f.endswith(".json"))
    removed = 0
    filtered_names = 0

    for config_name in configs:
        config_path = os.path.join(config_dir, config_name)
        with open(config_path) as f:
            config = json.load(f)

        challenge_module = config.get("challenge_module", "")
        names = config.get("theorem_names", [])

        if not names:
            continue

        # Get declaration kinds from the challenge (spec) module
        kinds = get_decl_kinds(repo_dir, lean4export_bin, challenge_module, names)

        # Filter to only theorems and axioms (what comparator accepts)
        thm_names = [n for n in names if kinds.get(n) in ("thm", "ax")]
        non_thm = [n for n in names if n not in [t for t in thm_names]]

        if non_thm:
            kind_info = ", ".join(f"{n} ({kinds.get(n, '?')})" for n in non_thm)
            print(f"  {config_name}: filtered out non-theorems: {kind_info}")
            filtered_names += len(non_thm)

        if not thm_names:
            # No theorems left — remove this config
            os.remove(config_path)
            print(f"  {config_name}: removed (no theorems)")
            removed += 1
        elif len(thm_names) < len(names):
            # Update config with filtered names
            config["theorem_names"] = thm_names
            with open(config_path, "w") as f:
                json.dump(config, f, indent=2)
                f.write("\n")

    print(f"  Filtered {filtered_names} non-theorem name(s), removed {removed} config(s)")


def main():
    if len(sys.argv) < 4:
        print(f"Usage: {sys.argv[0]} <repo_dir> <lean4export_bin> <config_dir>",
              file=sys.stderr)
        sys.exit(1)

    repo_dir = sys.argv[1]
    lean4export_bin = sys.argv[2]
    config_dir = sys.argv[3]

    filter_configs(repo_dir, lean4export_bin, config_dir)


if __name__ == "__main__":
    main()
