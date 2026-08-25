#!/usr/bin/env python3
"""Fixtures for both lean4export formats, for kinds and for type dependencies.

lean4export has emitted two shapes: a flat text export (2.x) and NDJSON (3.x).
Assuming one of them has twice produced a silent wrong answer here — dropping
real theorems as "not theorems", and reporting no dependencies at all — so both
are pinned by fixtures.

Run: python3 scripts/lib/test_export_parsing.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from filter_comparator_theorems import (  # noqa: E402
    _deps_from_json_export,
    _deps_from_text_export,
    _kinds_from_json_export,
    _kinds_from_text_export,
)

# --- text (2.x) ----------------------------------------------------------
# Names: 1=Foo, 2=Foo.bar, 3=Foo.baz, 4=Nat, 5=Foo.helper
# Foo.bar : Nat -> Foo.baz ... (its type mentions Foo.baz, a sibling target)
TEXT_EXPORT = """\
1 #NS 0 Foo
2 #NS 1 bar
3 #NS 1 baz
4 #NS 0 Nat
5 #NS 1 helper
0 #EC 4
1 #EC 3
2 #EA 0 1
3 #EP 0 0 0 2
4 #EC 4
#THM 2 3 4
#DEF 5 0 0
"""

# --- NDJSON (3.x) --------------------------------------------------------
JSON_EXPORT = "\n".join([
    '{"in": 1, "str": {"pre": 0, "str": "Foo"}}',
    '{"in": 2, "str": {"pre": 1, "str": "bar"}}',
    '{"in": 3, "str": {"pre": 1, "str": "baz"}}',
    '{"in": 4, "str": {"pre": 0, "str": "Nat"}}',
    '{"ie": 10, "const": {"name": 4}}',
    '{"ie": 11, "const": {"name": 3}}',
    '{"ie": 12, "app": {"fn": 10, "arg": 11}}',
    # A mutual block: two declarations under one key, as a list.
    '{"thm": [{"name": 2, "type": 12, "value": 10}, {"name": 3, "type": 10, "value": 10}]}',
])

FAILURES = []


def check(label, got, want):
    if got == want:
        print(f"ok   {label}")
    else:
        print(f"FAIL {label}\n       got:  {got!r}\n       want: {want!r}")
        FAILURES.append(label)


def main():
    names = ["Foo.bar", "Foo.baz"]

    check("text export: kinds",
          _kinds_from_text_export(TEXT_EXPORT, names + ["Foo.helper"]),
          {"Foo.bar": "thm", "Foo.helper": "def"})

    check("json export: kinds, including a mutual block",
          _kinds_from_json_export(JSON_EXPORT, names),
          {"Foo.bar": "thm", "Foo.baz": "thm"})

    # Foo.bar's type is `∀ _ : Nat, Nat → Foo.baz`-ish: it mentions Foo.baz.
    check("text export: type dependencies",
          _deps_from_text_export(TEXT_EXPORT, names),
          {"Foo.bar": {"Nat", "Foo.baz"}})

    check("json export: type dependencies from a mutual block",
          _deps_from_json_export(JSON_EXPORT, names),
          {"Foo.bar": {"Nat", "Foo.baz"}, "Foo.baz": {"Nat"}})

    # The cross-reference filter depends on this: a theorem whose type names a
    # sibling target must be detectable in BOTH formats.
    for label, deps in (("text", _deps_from_text_export(TEXT_EXPORT, names)),
                        ("json", _deps_from_json_export(JSON_EXPORT, names))):
        refs = deps.get("Foo.bar", set()) & {"Foo.baz"}
        check(f"{label} export: sibling reference is visible to the xref filter",
              refs, {"Foo.baz"})

    print(f"\nran 6 test(s); {len(FAILURES)} failure(s)")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
