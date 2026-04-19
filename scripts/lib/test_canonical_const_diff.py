#!/usr/bin/env python3
"""
Unit tests for canonical_const_diff.py.

Run: ``python3 scripts/lib/test_canonical_const_diff.py``

No pytest dependency. The synthetic NDJSON fragment below mirrors the lean4export
3.1.0 schema (see leanprover/lean4export's ``Export.lean`` / ``format_ndjson.md``)
and exercises:

    * Every Level kind: ``succ``, ``max``, ``imax``, ``param``
    * Both literal kinds: ``natVal`` and ``strVal``
    * ``Expr.proj``, ``Expr.mdata``, ``Expr.lam``, ``Expr.forallE``
    * A ``thm`` declaration whose ``type`` and ``value`` cover all of the above

The asserted invariant: ``canonicalize_const`` must produce output free of
``<level:N>`` and ``<unknown:...>`` placeholders for every node we exercise.
"""
from __future__ import annotations
import os
import sys
import tempfile
import textwrap

# Ensure we import the sibling module no matter where pytest is invoked from.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from canonical_const_diff import (  # noqa: E402
    parse_export,
    resolve_name,
    resolve_level,
    canonical_expr,
    canonicalize_const,
)


# ---------------------------------------------------------------------------
# Synthetic NDJSON fragment
# ---------------------------------------------------------------------------
# Layout (one JSON object per line):
#
#   Names (tag "in"):
#     1: "Foo"                   2: "Foo.bar"        3: "Pair"
#     4: "Pair.fst"              5: "u"              6: "v"
#     7: "α"                     8: "x"              9: "y"
#    10: "List"                 11: "Eq"
#
#   Levels (tag "il"):
#     1: param u                 2: succ 1           3: param v
#     4: max  1 3                5: imax 1 3
#
#   Expressions (tag "ie"):
#     1: Sort (succ u)               -- uses level idx 2
#     2: bvar 0
#     3: Const Pair {max u v}        -- uses level idx 4
#     4: app (#3) (#1)               -- (Pair (Sort (succ u)))
#     5: proj Pair #0 of #4
#     6: mdata wrapping #5
#     7: natVal "42"
#     8: strVal "hi"
#     9: Const Eq {imax u v}         -- uses level idx 5
#    10: app (#9) (#7)               -- (Eq 42)
#    11: app (#10) (#8)              -- (Eq 42 "hi"), drives an App spine
#    12: lam α : (Sort u) => bvar 0  -- identity at type Sort u
#    13: forallE x : (#1) -> bvar 0  -- ∀ (x : Sort (succ u)), bvar 0
#    14: letE y : (#1) := #6 in #11  -- ties proj+mdata+lits+app together
#    15: app (#12) (#14)             -- ((λα. α) (let y := proj … in Eq 42 "hi"))
#
#   Theorem (tag "thm"):
#     name=2 (Foo.bar), levelParams=[5,6], type=#13, value=#15

SYNTHETIC_NDJSON = "\n".join([
    # Names
    '{"in":1,"str":{"pre":0,"str":"Foo"}}',
    '{"in":2,"str":{"pre":1,"str":"bar"}}',
    '{"in":3,"str":{"pre":0,"str":"Pair"}}',
    '{"in":4,"str":{"pre":3,"str":"fst"}}',
    '{"in":5,"str":{"pre":0,"str":"u"}}',
    '{"in":6,"str":{"pre":0,"str":"v"}}',
    '{"in":7,"str":{"pre":0,"str":"\\u03b1"}}',
    '{"in":8,"str":{"pre":0,"str":"x"}}',
    '{"in":9,"str":{"pre":0,"str":"y"}}',
    '{"in":10,"str":{"pre":0,"str":"List"}}',
    '{"in":11,"str":{"pre":0,"str":"Eq"}}',

    # Levels
    '{"il":1,"param":5}',
    '{"il":2,"succ":1}',
    '{"il":3,"param":6}',
    '{"il":4,"max":[1,3]}',
    '{"il":5,"imax":[1,3]}',

    # Expressions
    '{"ie":1,"sort":2}',
    '{"ie":2,"bvar":0}',
    '{"ie":3,"const":{"name":3,"us":[4]}}',
    '{"ie":4,"app":{"fn":3,"arg":1}}',
    '{"ie":5,"proj":{"typeName":3,"idx":0,"struct":4}}',
    '{"ie":6,"mdata":{"data":{},"expr":5}}',
    '{"ie":7,"natVal":"42"}',
    '{"ie":8,"strVal":"hi"}',
    '{"ie":9,"const":{"name":11,"us":[5]}}',
    '{"ie":10,"app":{"fn":9,"arg":7}}',
    '{"ie":11,"app":{"fn":10,"arg":8}}',
    '{"ie":12,"lam":{"name":7,"type":1,"body":2,"binderInfo":"default"}}',
    '{"ie":13,"forallE":{"name":8,"type":1,"body":2,"binderInfo":"default"}}',
    '{"ie":14,"letE":{"name":9,"type":1,"value":6,"body":11,"nondep":false}}',
    '{"ie":15,"app":{"fn":12,"arg":14}}',

    # Theorem declaration
    '{"thm":{"name":2,"levelParams":[5,6],"type":13,"value":15,"all":[2]}}',
]) + "\n"


def _load_synthetic():
    """Write the synthetic NDJSON to a temp file and parse it."""
    with tempfile.NamedTemporaryFile("w", suffix=".ndjson", delete=False) as fh:
        fh.write(SYNTHETIC_NDJSON)
        path = fh.name
    try:
        return parse_export(path)
    finally:
        os.unlink(path)


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def _check(condition, message):
    if not condition:
        raise AssertionError(message)


def test_parse_collects_all_kinds():
    names, exprs, levels, thms, defs, axs = _load_synthetic()
    _check(len(names) == 11, f"expected 11 names, got {len(names)}: {sorted(names)}")
    _check(len(levels) == 5, f"expected 5 levels, got {len(levels)}: {sorted(levels)}")
    _check(len(exprs) == 15, f"expected 15 exprs, got {len(exprs)}: {sorted(exprs)}")
    _check(len(thms) == 1, f"expected 1 thm, got {len(thms)}")
    _check(defs == [] and axs == [], "no defs or axioms in fragment")


def test_resolve_name_handles_dotted_and_anon():
    names, *_ = _load_synthetic()
    _check(resolve_name(names, 2) == "Foo.bar",
           f"Foo.bar should round-trip, got {resolve_name(names, 2)!r}")
    _check(resolve_name(names, 4) == "Pair.fst",
           f"Pair.fst should round-trip, got {resolve_name(names, 4)!r}")
    _check(resolve_name(names, 999).startswith("<anon:"),
           "missing name index should render as <anon:...>")


def test_resolve_level_covers_every_kind():
    names, exprs, levels, *_ = _load_synthetic()
    # 0 -> "0" (Level.zero is never serialized)
    _check(resolve_level(names, levels, 0) == "0", "level idx 0 should be '0'")
    # param u
    got = resolve_level(names, levels, 1)
    _check(got == "@u", f"param: expected @u, got {got!r}")
    # succ (param u)
    got = resolve_level(names, levels, 2)
    _check(got == "(succ @u)", f"succ: expected (succ @u), got {got!r}")
    # max u v
    got = resolve_level(names, levels, 4)
    _check(got == "(max @u @v)", f"max: expected (max @u @v), got {got!r}")
    # imax u v
    got = resolve_level(names, levels, 5)
    _check(got == "(imax @u @v)", f"imax: expected (imax @u @v), got {got!r}")
    # No "<level:N>" placeholder anywhere
    for idx in (1, 2, 3, 4, 5):
        rendered = resolve_level(names, levels, idx)
        _check("<level:" not in rendered, f"unexpected placeholder in {rendered!r}")


def test_canonical_expr_renders_literals_and_proj_and_mdata():
    names, exprs, levels, *_ = _load_synthetic()
    nat = canonical_expr(names, exprs, levels, 7)
    _check(nat == "(Lit 42)", f"natVal: expected (Lit 42), got {nat!r}")
    s = canonical_expr(names, exprs, levels, 8)
    _check(s == "(LitStr 'hi')", f"strVal: expected (LitStr 'hi'), got {s!r}")
    proj_render = canonical_expr(names, exprs, levels, 5)
    _check(proj_render.startswith("(Proj Pair #0 "),
           f"proj should start '(Proj Pair #0 ', got {proj_render!r}")
    # mdata is transparent
    mdata_render = canonical_expr(names, exprs, levels, 6)
    _check(mdata_render == proj_render,
           f"mdata should be transparent; got {mdata_render!r} vs {proj_render!r}")


def test_canonical_expr_handles_lam_forallE_letE_app():
    names, exprs, levels, *_ = _load_synthetic()
    lam = canonical_expr(names, exprs, levels, 12)
    _check(lam.startswith("(Lam [default] \u03b1 :"),
           f"lam header wrong: {lam!r}")
    pi = canonical_expr(names, exprs, levels, 13)
    _check(pi.startswith("(Pi [default] x :"),
           f"forallE header wrong: {pi!r}")
    let_render = canonical_expr(names, exprs, levels, 14)
    _check(let_render.startswith("(Let y :"), f"letE header wrong: {let_render!r}")
    app = canonical_expr(names, exprs, levels, 15)
    _check(app.startswith("(App "), f"app should render as (App ...), got {app!r}")


def test_canonicalize_const_full_render_has_no_placeholders():
    names, exprs, levels, thms, defs, _axs = _load_synthetic()
    out = canonicalize_const(names, exprs, levels, thms, defs, "Foo.bar")
    _check(out is not None, "Foo.bar should be found")
    # The whole point of issue #5: no <level:N> or <unknown:...> placeholders
    _check("<level:" not in out, f"<level:N> placeholder leaked:\n{out}")
    _check("<unknown:" not in out, f"<unknown:...> placeholder leaked:\n{out}")
    # Sanity: each covered feature appears in the rendered text
    for needle in (
        "KIND: thm",
        "@u",                    # param u (in level params and inside max/imax/succ)
        "@v",                    # param v
        "(succ @u)",             # Level.succ
        "(max @u @v)",           # Level.max
        "(imax @u @v)",          # Level.imax
        "(Pi [default] x",       # forallE
        "(Lam [default] \u03b1", # lam
        "(Let y",                # letE
        "(Lit 42)",              # natVal
        "(LitStr 'hi')",         # strVal
        "(Proj Pair #0 ",        # proj
        "(Const Pair",           # const + level array
        "(Const Eq",
    ):
        _check(needle in out, f"missing {needle!r} in canonical render:\n{out}")
    # levelParams render via the name table (not raw indices)
    _check("LEVEL_PARAMS: ['@u', '@v']" in out,
           f"levelParams should resolve via name table; got:\n{out}")


def test_canonicalize_const_returns_none_for_missing():
    names, exprs, levels, thms, defs, _axs = _load_synthetic()
    out = canonicalize_const(names, exprs, levels, thms, defs, "DoesNotExist")
    _check(out is None, f"missing constant should return None, got {out!r}")


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def main() -> int:
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    failures = []
    for t in tests:
        try:
            t()
        except AssertionError as exc:
            failures.append((t.__name__, str(exc)))
            print(f"FAIL {t.__name__}: {exc}")
        except Exception as exc:  # noqa: BLE001
            failures.append((t.__name__, f"{type(exc).__name__}: {exc}"))
            print(f"ERROR {t.__name__}: {type(exc).__name__}: {exc}")
        else:
            print(f"ok   {t.__name__}")
    print(textwrap.dedent(f"""
        ---
        ran {len(tests)} test(s); {len(failures)} failure(s)
    """).strip())
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
