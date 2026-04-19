#!/usr/bin/env python3
"""
Parse two lean4export NDJSON files, extract the ConstantInfo for a given name,
resolve indices to names, and output canonical forms for diffing.

Usage: canonical_const_diff.py <const_name> <spec_export> <impl_export>

Prints canonical form from each side, then a diff.

Field names follow lean4export 3.1.0 (see leanprover/lean4export's
``Export.lean`` and ``format_ndjson.md`` on branch ``master``):

    - Names are tagged ``"in"`` with payload under ``"str"`` / ``"num"``.
    - Levels are tagged ``"il"``; the level kind lives at the top level under
      ``"succ"`` (int level idx), ``"max"``/``"imax"`` (``[lhs, rhs]`` arrays of
      level idxs), or ``"param"`` (int *name* idx).
    - Expressions are tagged ``"ie"``; literals appear top-level as
      ``"natVal"`` (string of digits) or ``"strVal"`` (string).
    - Declarations are tagged ``"axiom"``, ``"def"``, ``"thm"``, ``"opaque"``,
      ``"quot"``, and ``"inductive"`` (the latter aggregates ``types``,
      ``ctors``, ``recs``).
"""
from __future__ import annotations
import json
import sys
from difflib import unified_diff


def parse_export(path):
    """Parse NDJSON, return (name_table, expr_table, level_table, thm_entries, def_entries, ax_entries)."""
    names = {}   # idx -> (pre_idx, str_or_num)
    exprs = {}   # idx -> expr_obj
    levels = {}  # idx -> level_obj
    thms = []    # list of thm dicts
    defs = []    # list of def dicts
    axs = []     # list of axiom dicts
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            # Names: tagged with "in"
            if "in" in obj:
                idx = obj["in"]
                if "str" in obj:
                    names[idx] = (obj["str"].get("pre", 0), obj["str"].get("str", ""))
                elif "num" in obj:
                    names[idx] = (obj["num"].get("pre", 0), str(obj["num"].get("i", "")))
            # Expressions: tagged with "ie"
            if "ie" in obj:
                exprs[obj["ie"]] = obj
            # Levels: tagged with "il" (NOT "iu" — see Export.lean dumpLevel)
            if "il" in obj:
                levels[obj["il"]] = obj
            if "thm" in obj:
                thms.append(obj["thm"])
            if "def" in obj:
                defs.append(obj["def"])
            # Axioms: tagged "axiom" (NOT "ax") per Export.lean dumpAxiomVal
            if "axiom" in obj:
                axs.append(obj["axiom"])
    return names, exprs, levels, thms, defs, axs


def resolve_name(names, idx):
    """Resolve a name index to a dotted string."""
    parts = []
    seen = set()
    while idx in names and idx not in seen:
        seen.add(idx)
        pre, s = names[idx]
        parts.append(s)
        idx = pre
    parts.reverse()
    return ".".join(parts) if parts else f"<anon:{idx}>"


def resolve_level(names, levels, idx):
    """Resolve a level index to a string representation.

    Per ``Export.lean``, the level kind lives at the top level of the entry:
    ``succ`` (int level idx), ``max``/``imax`` (``[lhs, rhs]`` array of level
    idxs), and ``param`` (int *name* idx). Index 0 denotes ``Level.zero``,
    which is never serialized as its own entry.
    """
    if idx == 0:
        return "0"
    if idx not in levels:
        return f"<level:{idx}>"
    obj = levels[idx]
    # "succ": top-level int payload (level idx of predecessor)
    if "succ" in obj:
        return f"(succ {resolve_level(names, levels, obj['succ'])})"
    # "max": top-level [lhs, rhs] array of level idxs
    if "max" in obj:
        lhs, rhs = obj["max"]
        return f"(max {resolve_level(names, levels, lhs)} {resolve_level(names, levels, rhs)})"
    # "imax": top-level [lhs, rhs] array of level idxs
    if "imax" in obj:
        lhs, rhs = obj["imax"]
        return f"(imax {resolve_level(names, levels, lhs)} {resolve_level(names, levels, rhs)})"
    # "param": top-level int *name* idx (resolve via name table)
    if "param" in obj:
        return f"@{resolve_name(names, obj['param'])}"
    return f"<level:{idx}>"


def canonical_expr(names, exprs, levels, idx, depth=0, max_depth=200, indent_level=0):
    """Recursively convert an expression to a canonical string form.

    Names are resolved; bound variable names are preserved; structure is made
    explicit. Output is Lisp-like, pretty-printed with one line per Pi/Lam/App-spine
    element so the diff localizes the actual divergence.
    """
    ind = "  " * (indent_level + 1)
    if depth > max_depth:
        return "<...>"
    if idx not in exprs:
        # Bound variables (de Bruijn indices) show up as raw numbers
        return f"#{idx}"
    e = exprs[idx]
    # "bvar": top-level int (de Bruijn index)
    if "bvar" in e:
        return f"#bvar{e['bvar']}"
    # "sort": top-level int level idx
    if "sort" in e:
        return f"(Sort {resolve_level(names, levels, e['sort'])})"
    if "fvar" in e:
        return f"#fvar{e['fvar']}"
    if "mvar" in e:
        return f"#mvar{e['mvar']}"
    # "const": {"name": int, "us": [level idx, ...]}
    if "const" in e:
        c = e["const"]
        name = resolve_name(names, c["name"])
        us = " ".join(resolve_level(names, levels, u) for u in c.get("us", []))
        if us:
            return f"(Const {name} {{{us}}})"
        return f"(Const {name})"
    # "app": {"fn": expr idx, "arg": expr idx} — flatten left-assoc spines
    if "app" in e:
        spine = []
        cur_idx = idx
        while cur_idx in exprs and "app" in exprs[cur_idx]:
            spine.append(exprs[cur_idx]["app"]["arg"])
            cur_idx = exprs[cur_idx]["app"]["fn"]
        head = canonical_expr(names, exprs, levels, cur_idx, depth + 1, max_depth, indent_level + 1)
        args = [canonical_expr(names, exprs, levels, a, depth + 1, max_depth, indent_level + 1)
                for a in reversed(spine)]
        if len(args) <= 1 and all(len(a) < 60 for a in args) and len(head) < 60:
            return f"(App {head} {' '.join(args)})"
        return "(App " + head + "\n" + "\n".join(ind + a for a in args) + ")"
    # "lam": {"name", "type", "body", "binderInfo"}
    if "lam" in e:
        bi = e["lam"].get("binderInfo", "default")
        nm = resolve_name(names, e["lam"].get("name", 0))
        ty = canonical_expr(names, exprs, levels, e["lam"]["type"], depth + 1, max_depth, indent_level + 1)
        body = canonical_expr(names, exprs, levels, e["lam"]["body"], depth + 1, max_depth, indent_level + 1)
        return f"(Lam [{bi}] {nm} :\n{ind}{ty}\n{ind}=>\n{ind}{body})"
    # "forallE": {"name", "type", "body", "binderInfo"}
    if "forallE" in e:
        bi = e["forallE"].get("binderInfo", "default")
        nm = resolve_name(names, e["forallE"].get("name", 0))
        ty = canonical_expr(names, exprs, levels, e["forallE"]["type"], depth + 1, max_depth, indent_level + 1)
        body = canonical_expr(names, exprs, levels, e["forallE"]["body"], depth + 1, max_depth, indent_level + 1)
        return f"(Pi [{bi}] {nm} :\n{ind}{ty}\n{ind}->\n{ind}{body})"
    # "letE": {"name", "type", "value", "body", "nondep"}
    if "letE" in e:
        nm = resolve_name(names, e["letE"].get("name", 0))
        ty = canonical_expr(names, exprs, levels, e["letE"]["type"], depth + 1, max_depth, indent_level + 1)
        val = canonical_expr(names, exprs, levels, e["letE"]["value"], depth + 1, max_depth, indent_level + 1)
        body = canonical_expr(names, exprs, levels, e["letE"]["body"], depth + 1, max_depth, indent_level + 1)
        return f"(Let {nm} :\n{ind}{ty}\n{ind}:=\n{ind}{val}\n{ind}in\n{ind}{body})"
    # Literals: top-level "natVal" (string of digits) or "strVal" (string)
    if "natVal" in e:
        return f"(Lit {e['natVal']})"
    if "strVal" in e:
        return f"(LitStr {e['strVal']!r})"
    # "proj": {"typeName": name idx, "idx": int field, "struct": expr idx}
    if "proj" in e:
        p = e["proj"]
        s = canonical_expr(names, exprs, levels, p["struct"], depth + 1, max_depth, indent_level + 1)
        return f"(Proj {resolve_name(names, p.get('typeName', 0))} #{p.get('idx', '?')} {s})"
    # "mdata": {"data": <opaque>, "expr": expr idx} — transparent for canonical form
    if "mdata" in e:
        return canonical_expr(names, exprs, levels, e["mdata"]["expr"], depth + 1, max_depth, indent_level)
    return f"<unknown:{sorted(k for k in e.keys() if k != 'ie')}>"


def _format_level_params(names, lps):
    """Render a declaration's ``levelParams`` (list of name indices) as ``@<name>``."""
    return [f"@{resolve_name(names, p)}" for p in lps]


def canonicalize_const(names, exprs, levels, thms, defs, target_name):
    """Find the constant by name and return a canonical description."""
    for thm in thms:
        if resolve_name(names, thm["name"]) == target_name:
            lp = _format_level_params(names, thm.get("levelParams", []))
            ty = canonical_expr(names, exprs, levels, thm["type"])
            val = canonical_expr(names, exprs, levels, thm.get("value", 0))
            return (f"KIND: thm\n"
                    f"LEVEL_PARAMS: {lp}\n"
                    f"TYPE:\n  {ty}\n"
                    f"VALUE:\n  {val}\n")
    for d in defs:
        if resolve_name(names, d["name"]) == target_name:
            lp = _format_level_params(names, d.get("levelParams", []))
            ty = canonical_expr(names, exprs, levels, d["type"])
            val = canonical_expr(names, exprs, levels, d.get("value", 0))
            safety = d.get("safety", "unsafe?")
            hints = d.get("hints", "?")
            return (f"KIND: def\n"
                    f"LEVEL_PARAMS: {lp}\n"
                    f"SAFETY: {safety}\n"
                    f"HINTS: {hints}\n"
                    f"TYPE:\n  {ty}\n"
                    f"VALUE:\n  {val}\n")
    return None


def main():
    if len(sys.argv) != 4:
        print(f"Usage: {sys.argv[0]} <const_name> <spec_export> <impl_export>",
              file=sys.stderr)
        sys.exit(2)

    target, spec_path, impl_path = sys.argv[1], sys.argv[2], sys.argv[3]

    print(f"Loading spec export: {spec_path}", file=sys.stderr)
    spec_data = parse_export(spec_path)
    print(f"Loading impl export: {impl_path}", file=sys.stderr)
    impl_data = parse_export(impl_path)

    spec_names, spec_exprs, spec_levels, spec_thms, spec_defs, _ = spec_data
    impl_names, impl_exprs, impl_levels, impl_thms, impl_defs, _ = impl_data

    spec_canon = canonicalize_const(spec_names, spec_exprs, spec_levels,
                                    spec_thms, spec_defs, target)
    impl_canon = canonicalize_const(impl_names, impl_exprs, impl_levels,
                                    impl_thms, impl_defs, target)

    if spec_canon is None:
        print(f"FATAL: '{target}' not found in spec export", file=sys.stderr)
        sys.exit(1)
    if impl_canon is None:
        print(f"FATAL: '{target}' not found in impl export", file=sys.stderr)
        sys.exit(1)

    print(f"=== UNIFIED DIFF (spec vs impl) for {target} ===")
    spec_lines = spec_canon.splitlines(keepends=True)
    impl_lines = impl_canon.splitlines(keepends=True)
    print(f"Spec canonical form: {len(spec_lines)} lines")
    print(f"Impl canonical form: {len(impl_lines)} lines")
    diff_lines = list(unified_diff(
        spec_lines, impl_lines,
        fromfile="spec", tofile="impl", n=3, lineterm=""))
    print(f"Diff lines: {len(diff_lines)}")
    print("")
    for line in diff_lines:
        print(line.rstrip("\n"))


if __name__ == "__main__":
    main()
