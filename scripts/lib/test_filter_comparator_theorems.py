#!/usr/bin/env python3
"""Tests for declaration-kind detection across lean4export formats.

Which format you get depends on the lean4export revision comparator pins you to,
and reading only one of them made the filter report every declaration as "kind
unknown" — which, before it became an error, silently dropped real theorems.

Run: python3 scripts/lib/test_filter_comparator_theorems.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from filter_comparator_theorems import (  # noqa: E402
    _kinds_from_json_export,
    _kinds_from_text_export,
)

FAILURES = []


def check(label, got, want):
    if got == want:
        print(f"ok   {label}")
    else:
        print(f"FAIL {label}\n     got  {got}\n     want {want}")
        FAILURES.append(label)


# Shapes taken from real exports: 2.0.0 from lean4export bd93e5e, 3.1.0 from 048394e.
TEXT_EXPORT = """2.0.0
1 #NS 0 SLT
2 #NS 1 CoveringNumber
3 #NS 0 IsENet
4 #NS 0 coveringNumber
5 #NS 0 dudley
#DEF 3 100 101 R 7
#DEF 4 102 103 R 7
#THM 5 200 201
"""

JSON_EXPORT = """{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"Selftest"}}
{"in":2,"str":{"pre":1,"str":"add_comm'"}}
{"in":3,"str":{"pre":1,"str":"helper"}}
{"in":4,"str":{"pre":1,"str":"Tree"}}
{"thm":{"name":2,"levelParams":[],"type":10,"value":11}}
{"def":{"name":3,"hints":"abbrev","type":12,"value":13}}
{"ind":[{"name":4,"type":14},{"name":4,"type":15}]}
"""


check("text: definitions and theorems by marker",
      _kinds_from_text_export(TEXT_EXPORT, ["IsENet", "coveringNumber", "dudley"]),
      {"IsENet": "def", "coveringNumber": "def", "dudley": "thm"})

check("text: dotted names resolve through the name table",
      _kinds_from_text_export(TEXT_EXPORT, ["SLT.CoveringNumber"]),
      {})

check("json: theorem and definition",
      _kinds_from_json_export(JSON_EXPORT, ["Selftest.add_comm'", "Selftest.helper"]),
      {"Selftest.add_comm'": "thm", "Selftest.helper": "def"})

check("json: a mutual block arrives as a list, and must not crash",
      _kinds_from_json_export(JSON_EXPORT, ["Selftest.Tree"]),
      {"Selftest.Tree": "ind"})

check("either format: an unknown name is absent, never guessed",
      _kinds_from_text_export(TEXT_EXPORT, ["nosuchdecl"]),
      {})

print("---")
print(f"ran 5 test(s); {len(FAILURES)} failure(s)")
sys.exit(1 if FAILURES else 0)
