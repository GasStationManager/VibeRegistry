#!/usr/bin/env python3
"""
Filter comparator config files for compatibility with the comparator tool.

Two filters are applied:
1. Non-theorem filter: The comparator only accepts thmInfo and axiomInfo
   constants. Helper definitions (def, structure, etc.) cause "constant kind
   don't match" errors.
2. Cross-reference filter: If theorem B's type references theorem A (e.g. via
   Classical.choose), the comparator's transitive check (Phase 2) will compare
   A's full ConstantInfo including its proof value. Since the spec has sorry
   and the impl has the real proof, this always fails. We detect and exclude
   such dependent theorems.

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


def get_type_deps(repo_dir, lean4export_bin, module, names):
    """Get the set of constants referenced in each theorem's type.

    Returns dict mapping name -> set of constant names used in type.
    """
    if not names:
        return {}

    cmd = [lean4export_bin, module, "--"] + names
    try:
        result = subprocess.run(
            ["lake", "env"] + cmd,
            capture_output=True, text=True, cwd=repo_dir, timeout=120
        )
    except subprocess.TimeoutExpired:
        return {}
    if result.returncode != 0:
        return {}

    name_table = {}   # idx -> (pre, str)
    expr_table = {}   # idx -> expr_obj
    thm_entries = []  # list of thm dicts

    for line in result.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue

        if "in" in obj:
            in_idx = obj["in"]
            if "str" in obj:
                name_table[in_idx] = (obj["str"].get("pre", 0), obj["str"].get("str", ""))
            elif "num" in obj:
                name_table[in_idx] = (obj["num"].get("pre", 0), str(obj["num"].get("i", "")))

        if "ie" in obj:
            expr_table[obj["ie"]] = obj

        if "thm" in obj:
            thm_entries.append(obj["thm"])

    def resolve(idx):
        parts = []
        while idx in name_table:
            pre, s = name_table[idx]
            parts.append(s)
            idx = pre
        parts.reverse()
        return ".".join(parts)

    def collect_consts(expr_idx, visited=None):
        """Collect all constant names referenced in an expression."""
        if visited is None:
            visited = set()
        if expr_idx in visited or expr_idx not in expr_table:
            return set()
        visited.add(expr_idx)
        e = expr_table[expr_idx]
        consts = set()
        if "const" in e:
            consts.add(resolve(e["const"]["name"]))
        for key in ("forallE", "lam", "letE"):
            if key in e:
                sub = e[key]
                for field in ("type", "body", "value"):
                    if field in sub:
                        consts |= collect_consts(sub[field], visited)
        if "app" in e:
            consts |= collect_consts(e["app"]["fn"], visited)
            consts |= collect_consts(e["app"]["arg"], visited)
        return consts

    deps = {}
    name_set = set(names)
    for thm in thm_entries:
        resolved = resolve(thm["name"])
        if resolved in name_set:
            type_idx = thm.get("type")
            if type_idx is not None:
                deps[resolved] = collect_consts(type_idx)

    return deps


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

        # Filter 1: Get declaration kinds, keep only theorems/axioms
        kinds = get_decl_kinds(repo_dir, lean4export_bin, challenge_module, names)

        thm_names = [n for n in names if kinds.get(n) in ("thm", "ax")]
        non_thm = [n for n in names if kinds.get(n) not in ("thm", "ax")]

        if non_thm:
            kind_info = ", ".join(f"{n} ({kinds.get(n, '?')})" for n in non_thm)
            print(f"  {config_name}: filtered out non-theorems: {kind_info}")
            filtered_names += len(non_thm)

        # Filter 2: Remove theorems whose types reference other target theorems
        if len(thm_names) > 1:
            deps = get_type_deps(repo_dir, lean4export_bin, challenge_module, thm_names)
            thm_set = set(thm_names)
            xref_removed = []
            safe_names = []
            for n in thm_names:
                type_consts = deps.get(n, set())
                # Check if type references any other target theorem
                refs = type_consts & (thm_set - {n})
                if refs:
                    xref_removed.append((n, refs))
                else:
                    safe_names.append(n)
            if xref_removed:
                for n, refs in xref_removed:
                    ref_str = ", ".join(sorted(refs))
                    print(f"  {config_name}: filtered {n} (type references target: {ref_str})")
                    filtered_names += 1
                thm_names = safe_names

        if not thm_names:
            os.remove(config_path)
            print(f"  {config_name}: removed (no theorems)")
            removed += 1
        elif len(thm_names) < len(names):
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
