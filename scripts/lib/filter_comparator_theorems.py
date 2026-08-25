#!/usr/bin/env python3
"""
Filter comparator config files for compatibility with the comparator tool.

Two filters are applied:
1. Non-theorem filter: comparator's theorem_names only accepts thmInfo and
   axiomInfo constants. Helper definitions (def, structure, etc.) cause
   "constant kind don't match" errors there. With --definitions-mode compare
   they are moved to comparator's definition_names instead of being dropped;
   with the default drop mode they are removed, and a group left with nothing
   but definitions has its config deleted (the caller then records the group as
   not-applicable rather than pretending it was checked).
2. Cross-reference filter: If theorem B's type references theorem A (e.g. via
   Classical.choose), the comparator's transitive check (Phase 2) will compare
   A's full ConstantInfo including its proof value. Since the spec has sorry
   and the impl has the real proof, this always fails. We detect and exclude
   such dependent theorems.

Usage:
    python3 filter_comparator_theorems.py <repo_dir> <lean4export_bin> <config_dir>
        [--definitions-mode drop|compare]

Modifies config JSON files in-place. Removes configs with nothing left to check.
"""

import sys
import os
import json
import subprocess


def _lake_env(repo_dir):
    """`lake env`, reconfiguring first where the project needs it.

    Some projects' compiled Lake configs are rejected by a plain `lake env` and
    accepted only with -R. Without this, lean4export never ran for such a
    project, every declaration's kind came back unknown, and the run failed for
    a reason that had nothing to do with the mathematics.
    """
    if os.environ.get("LAKE_NEEDS_RECONFIGURE") == "1":
        return ["lake", "env", "-R"]
    return ["lake", "env"]


def _resolve_name(name_table, idx):
    """Resolve a name index to a dotted string."""
    parts = []
    while idx in name_table:
        pre, part = name_table[idx]
        parts.append(part)
        idx = pre
    parts.reverse()
    return ".".join(parts)


# lean4export emits two different export formats, and which one you get depends
# on the revision comparator pins you to:
#
#   2.x  plain text. First line is the bare version, names are
#        `<idx> #NS <parent> <string>`, declarations are `#THM <name_idx> ...`
#   3.x  NDJSON. First line is a JSON meta header, names are
#        {"in": idx, "str": {...}}, declarations are {"thm": {...}} — and a
#        mutual block arrives as a LIST under one key.
#
# Handling only the JSON dict shape is how this filter came to report every
# declaration as "kind unknown": it crashed on a list, and read nothing at all
# from a 2.x export.
def _kinds_from_text_export(text, names):
    name_table = {}
    kinds = {}
    wanted = set(names)
    markers = {
        "#THM": "thm", "#AX": "ax", "#DEF": "def", "#OPAQ": "opaque",
        "#IND": "ind", "#CTOR": "ctor", "#REC": "rec", "#QUOT": "quot",
    }
    for line in text.splitlines():
        parts = line.split()
        if len(parts) >= 4 and parts[1] in ("#NS", "#NI"):
            try:
                name_table[int(parts[0])] = (int(parts[2]), parts[3])
            except ValueError:
                pass
            continue
        if not parts:
            continue
        kind = markers.get(parts[0])
        if kind is None or len(parts) < 2:
            continue
        try:
            name_idx = int(parts[1])
        except ValueError:
            continue
        resolved = _resolve_name(name_table, name_idx)
        if resolved in wanted:
            kinds[resolved] = kind
    return kinds


def _kinds_from_json_export(text, names):
    name_table = {}
    kinds = {}
    wanted = set(names)
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue

        if "in" in obj and "str" in obj:
            name_table[obj["in"]] = (obj["str"].get("pre", 0), obj["str"].get("str", ""))
            continue

        for kind in ("def", "thm", "ax", "ind", "quot", "ctor", "rec", "opaque"):
            if kind not in obj:
                continue
            entries = obj[kind] if isinstance(obj[kind], list) else [obj[kind]]
            for entry in entries:
                if not isinstance(entry, dict):
                    continue
                name_idx = entry.get("name")
                if name_idx is None:
                    continue
                resolved = _resolve_name(name_table, name_idx)
                if resolved in wanted:
                    kinds[resolved] = kind
            break
    return kinds


def get_decl_kinds(repo_dir, lean4export_bin, module, names):
    """Use lean4export to determine the kind (def/thm/ax/ind) of each name.

    A name missing from the result means lean4export could not tell us its kind —
    which is NOT the same as "it is not a theorem". Callers must not drop a name
    on that basis: doing so silently discarded three real theorems when
    lean4export failed to load the module, and the run then reported a pass with
    nothing checked.
    """
    if not names:
        return {}

    cmd = [lean4export_bin, module, "--"] + names
    try:
        result = subprocess.run(
            _lake_env(repo_dir) + cmd,
            capture_output=True, text=True, cwd=repo_dir, timeout=600
        )
    except subprocess.TimeoutExpired:
        print(f"  WARNING: lean4export timed out for {module}", file=sys.stderr)
        return {}

    if result.returncode != 0:
        print(f"  WARNING: lean4export failed for {module}: {result.stderr[:200]}",
              file=sys.stderr)
        return {}

    if result.stdout.lstrip()[:1] == "{":
        return _kinds_from_json_export(result.stdout, names)
    return _kinds_from_text_export(result.stdout, names)


def _deps_from_json_export(text, names):
    """Type dependencies from the NDJSON (3.x) export."""
    name_table = {}
    expr_table = {}
    decls = []          # (name_idx, type_idx)
    wanted = set(names)

    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue

        if "in" in obj:
            idx = obj["in"]
            if "str" in obj:
                name_table[idx] = (obj["str"].get("pre", 0), obj["str"].get("str", ""))
            elif "num" in obj:
                name_table[idx] = (obj["num"].get("pre", 0), str(obj["num"].get("i", "")))

        if "ie" in obj:
            expr_table[obj["ie"]] = obj

        for kind in ("thm", "def", "opaque", "ax"):
            if kind not in obj:
                continue
            # A mutual block arrives as a list of declarations under one key.
            entries = obj[kind] if isinstance(obj[kind], list) else [obj[kind]]
            for entry in entries:
                if isinstance(entry, dict) and entry.get("name") is not None:
                    decls.append((entry["name"], entry.get("type")))
            break

    def collect(expr_idx, visited=None):
        if visited is None:
            visited = set()
        if expr_idx is None or expr_idx in visited or expr_idx not in expr_table:
            return set()
        visited.add(expr_idx)
        expr = expr_table[expr_idx]
        consts = set()
        if "const" in expr:
            consts.add(_resolve_name(name_table, expr["const"]["name"]))
        for key in ("forallE", "lam", "letE"):
            if key in expr:
                sub = expr[key]
                for field in ("type", "body", "value"):
                    if field in sub:
                        consts |= collect(sub[field], visited)
        if "app" in expr:
            consts |= collect(expr["app"].get("fn"), visited)
            consts |= collect(expr["app"].get("arg"), visited)
        return consts

    deps = {}
    for name_idx, type_idx in decls:
        resolved = _resolve_name(name_table, name_idx)
        if resolved in wanted and type_idx is not None:
            deps[resolved] = collect(type_idx)
    return deps


# Text-format expression markers, and which of their operands are expressions.
# #EA fn arg | #EL info name type body | #EP info name type body | #EZ ... |
# #EJ struct idx expr | #EM data expr | #EC name (universes...)
_TEXT_EXPR_OPERANDS = {
    "#EA": (0, 1),
    "#EL": (2, 3),
    "#EP": (2, 3),
    "#EZ": (2, 3),
    "#EJ": (2,),
    "#EM": (1,),
}


def _deps_from_text_export(text, names):
    """Type dependencies from the flat text (2.x) export.

    The 2.x exporter emits `<idx> #EC <nameIdx>` style lines rather than JSON, so
    the JSON walker read nothing at all from it and every dependency came back
    empty — which silently disabled the cross-reference filter.
    """
    name_table = {}
    expr_lines = {}     # expr idx -> (marker, [operand tokens])
    decls = []          # (name_idx, type_idx)
    wanted = set(names)

    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue

        if len(parts) >= 4 and parts[1] in ("#NS", "#NI"):
            try:
                name_table[int(parts[0])] = (int(parts[2]), parts[3])
            except ValueError:
                pass
            continue

        if len(parts) >= 2 and parts[1].startswith("#E"):
            try:
                expr_lines[int(parts[0])] = (parts[1], parts[2:])
            except ValueError:
                pass
            continue

        if parts[0] in ("#THM", "#DEF", "#OPAQ", "#AX") and len(parts) >= 3:
            try:
                decls.append((int(parts[1]), int(parts[2])))
            except ValueError:
                pass

    def collect(expr_idx, visited=None):
        if visited is None:
            visited = set()
        if expr_idx in visited or expr_idx not in expr_lines:
            return set()
        visited.add(expr_idx)
        marker, operands = expr_lines[expr_idx]
        consts = set()
        if marker == "#EC" and operands:
            try:
                consts.add(_resolve_name(name_table, int(operands[0])))
            except ValueError:
                pass
            return consts
        for position in _TEXT_EXPR_OPERANDS.get(marker, ()):
            if position < len(operands):
                try:
                    consts |= collect(int(operands[position]), visited)
                except ValueError:
                    continue
        return consts

    deps = {}
    for name_idx, type_idx in decls:
        resolved = _resolve_name(name_table, name_idx)
        if resolved in wanted:
            deps[resolved] = collect(type_idx)
    return deps


def get_type_deps(repo_dir, lean4export_bin, module, names):
    """Constants referenced in each theorem's type, in either export format.

    Used to drop a theorem whose statement mentions another target theorem:
    comparator compares such a reference's full ConstantInfo, and the spec's
    `sorry` can never match the implementation's real proof.
    """
    if not names:
        return {}

    cmd = [lean4export_bin, module, "--"] + names
    try:
        result = subprocess.run(
            _lake_env(repo_dir) + cmd,
            capture_output=True, text=True, cwd=repo_dir, timeout=600
        )
    except subprocess.TimeoutExpired:
        print(f"  WARNING: lean4export timed out reading dependencies for {module}",
              file=sys.stderr)
        return {}
    if result.returncode != 0:
        print(f"  WARNING: lean4export failed reading dependencies for {module}: "
              f"{result.stderr[:200]}", file=sys.stderr)
        return {}

    if result.stdout.lstrip()[:1] == "{":
        return _deps_from_json_export(result.stdout, names)
    return _deps_from_text_export(result.stdout, names)


def filter_configs(repo_dir, lean4export_bin, config_dir, definitions_mode="drop"):
    """Filter comparator configs by declaration kind.

    definitions_mode:
      drop     non-theorem names are removed (legacy behaviour)
      compare  non-theorem names move to comparator's definition_names
    """
    configs = sorted(f for f in os.listdir(config_dir) if f.endswith(".json"))
    removed = 0
    filtered_names = 0
    unknown_total = 0
    # Machine-readable outcome per config. The caller uses it to tell "there was
    # genuinely nothing here for comparator to check" apart from "we could not
    # find out" — only the first may be recorded as not-applicable.
    report = {"configs": {}}

    for config_name in configs:
        # The caller looks these up by the config's stem, which is how it derives
        # a config name from a theorem group's impl module. Keying the report by
        # the filename instead made every lookup miss, and a group the filter had
        # deliberately dropped was reported as a failure rather than as having
        # nothing to check.
        report_key = os.path.splitext(config_name)[0]
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
        unknown = [n for n in names if n not in kinds]
        non_thm = [n for n in names if n in kinds and kinds[n] not in ("thm", "ax")]

        if unknown:
            # Leave the config alone and let the caller fail the run. Guessing
            # here is how unchecked theorems get reported as checked.
            print(f"  ERROR {config_name}: could not determine the kind of "
                  f"{', '.join(unknown)} — lean4export did not report them. "
                  f"Leaving the config untouched; comparator will run against it.")
            report["configs"][report_key] = {
                "status": "unknown-kinds",
                "kept": names,
                "unknown": unknown,
            }
            unknown_total += len(unknown)
            continue

        if non_thm:
            kind_info = ", ".join(f"{n} ({kinds.get(n, '?')})" for n in non_thm)
            if definitions_mode == "compare":
                print(f"  {config_name}: comparing as definitions: {kind_info}")
                config["definition_names"] = non_thm
            else:
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

        keep_definitions = bool(config.get("definition_names"))

        if not thm_names and not keep_definitions:
            os.remove(config_path)
            print(f"  {config_name}: removed (nothing comparator can check)")
            removed += 1
            report["configs"][report_key] = {
                "status": "removed",
                "kept": [],
                "dropped_non_theorem": non_thm,
            }
        else:
            report["configs"][report_key] = {
                "status": "ok",
                "kept": thm_names,
                "definitions": config.get("definition_names", []),
                "dropped_non_theorem": non_thm,
            }
            if len(thm_names) < len(names) or keep_definitions:
                config["theorem_names"] = thm_names
                with open(config_path, "w") as f:
                    json.dump(config, f, indent=2)
                    f.write("\n")

    report["unknown_total"] = unknown_total
    with open(os.path.join(config_dir, "_filter_report.json"), "w") as f:
        json.dump(report, f, indent=2)
        f.write("\n")

    print(f"  Filtered {filtered_names} non-theorem name(s), removed {removed} config(s)")
    if unknown_total:
        print(f"  {unknown_total} name(s) of unknown kind — the caller must not "
              f"treat these groups as checked")
    return unknown_total


def main():
    argv = list(sys.argv[1:])
    definitions_mode = "drop"
    if "--definitions-mode" in argv:
        idx = argv.index("--definitions-mode")
        if idx + 1 >= len(argv):
            print("ERROR: --definitions-mode needs a value (drop|compare)", file=sys.stderr)
            sys.exit(1)
        definitions_mode = argv[idx + 1]
        del argv[idx:idx + 2]

    if definitions_mode not in ("drop", "compare"):
        print(f"ERROR: unknown --definitions-mode '{definitions_mode}'", file=sys.stderr)
        sys.exit(1)

    if len(argv) < 3:
        print(f"Usage: {sys.argv[0]} <repo_dir> <lean4export_bin> <config_dir> "
              f"[--definitions-mode drop|compare]", file=sys.stderr)
        sys.exit(1)

    repo_dir, lean4export_bin, config_dir = argv[0], argv[1], argv[2]

    unknown_total = filter_configs(repo_dir, lean4export_bin, config_dir, definitions_mode)
    # Non-zero when any declaration's kind could not be established.
    sys.exit(1 if unknown_total else 0)


if __name__ == "__main__":
    main()
