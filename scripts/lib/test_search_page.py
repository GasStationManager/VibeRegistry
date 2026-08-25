#!/usr/bin/env python3
"""The search page is generated — assert the generator emits the logic it needs.

index/search.html is written from a template inside build_search_index.py, so a
fix applied to the generated file is silently reverted by the next build. That
happened: the sign-off scoping and verdict-state display were edited into the
page, the next build overwrote them, and the page went on showing a sign-off for
a rejected review and no warning for a verdict that predates statement binding.

Run: python3 scripts/lib/test_search_page.py
"""

import os
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(os.path.dirname(SCRIPT_DIR))
sys.path.insert(0, os.path.join(PROJECT_DIR, "scripts"))

from build_search_index import SEARCH_HTML  # noqa: E402

FAILURES = []

REQUIRED = [
    # A sign-off counts only when current AND approved.
    (r"function approvedSignoffs", "approvedSignoffs() helper"),
    (r's\.status === "current" && s\.verdict === "approved"',
     "sign-off requires current AND approved"),
    (r'rejected.*verdict === "rejected"|verdict === "rejected"',
     "rejected reviews are recognised"),
    (r"approvedSignoffs\(r\)\.length === 0", "the signed-off filter uses approval"),
    # A verdict that no longer describes the current statement must say so.
    (r"verdict_state", "verdict_state is displayed"),
    (r"stale-statement", "stale-statement is labelled"),
    (r"unbound-verdict", "unbound-verdict is labelled"),
    # Records carry per-declaration sign-offs; never render the entry's whole list.
    (r"r\.signoffs", "reads the per-declaration sign-off list"),
]


def main():
    generated_path = os.path.join(PROJECT_DIR, "index", "search.html")
    for pattern, label in REQUIRED:
        if re.search(pattern, SEARCH_HTML):
            print(f"ok   template: {label}")
        else:
            print(f"FAIL template: {label}")
            FAILURES.append(label)

    # And the checked-in page must be what the template produces, so nobody is
    # reading a page that no longer matches the generator.
    if os.path.isfile(generated_path):
        with open(generated_path) as f:
            generated = f.read()
        if generated.strip() == SEARCH_HTML.strip():
            print("ok   index/search.html matches the template")
        else:
            print("FAIL index/search.html differs from the template — "
                  "run scripts/build_search_index.py")
            FAILURES.append("generated page is stale")

    print(f"\nran {len(REQUIRED) + 1} test(s); {len(FAILURES)} failure(s)")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
