#!/usr/bin/env python3
"""Drive the sign-off processor over the issue bodies GitHub actually produces.

One form now feeds two stores, and picking the wrong one — or binding a sign-off
to the wrong hash — is exactly the class of mistake that makes a sign-off mean
something it should not. So both paths, plus the refusals, are pinned here.

Run: python3 scripts/lib/test_process_signoff.py
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(os.path.dirname(SCRIPT_DIR))
PROCESSOR = os.path.join(PROJECT_DIR, "scripts", "process_signoff.py")

FAILURES = []


def check(label, condition, detail=""):
    if condition:
        print(f"ok   {label}")
    else:
        print(f"FAIL {label}" + (f"\n       {detail}" if detail else ""))
        FAILURES.append(label)


def issue_body(kind, target, reviewed, verdict="Approved", comments="looks right"):
    """The shape GitHub's form renders: '### Header\n\nvalue' sections."""
    return (
        f"### Target kind\n\n{kind}\n\n"
        f"### Target ID\n\n{target}\n\n"
        f"### What you reviewed\n\n{reviewed}\n\n"
        f"### Literature reference\n\nHarper (1966)\n\n"
        f"### Verdict\n\n{verdict}\n\n"
        f"### Comments\n\n{comments}\n"
    )


def run(sandbox, body, author="reviewer", number="42"):
    # The processor resolves the repo from its own location, so running the
    # sandbox's copy is what keeps these tests off the real registry.
    env = dict(os.environ,
               ISSUE_BODY=body, ISSUE_AUTHOR=author, ISSUE_NUMBER=number)
    return subprocess.run([sys.executable, os.path.join(sandbox, "scripts", "process_signoff.py")],
                          capture_output=True, text=True, env=env, cwd=sandbox)


def make_sandbox():
    """A throwaway copy of the repo, so tests never write to the real registry."""
    sandbox = tempfile.mkdtemp(prefix="signoff-test-")
    for path in ("scripts", "entries", "specs", "overlay"):
        shutil.copytree(os.path.join(PROJECT_DIR, path), os.path.join(sandbox, path))
    return sandbox


def main():
    sandbox = make_sandbox()

    # --- overlay record ---------------------------------------------------
    record_path = os.path.join(sandbox, "overlay", "leanpool", "2-coloring-1-round.json")
    record = json.load(open(record_path))
    declaration = record["declarations"][0]

    result = run(sandbox, issue_body("Overlay record: leanpool",
                                     "2-coloring-1-round", declaration))
    check("overlay sign-off is accepted", result.returncode == 0,
          result.stderr[-400:])

    signoffs = open(os.path.join(sandbox, "overlay", "signoffs.toml")).read()
    check("overlay sign-off lands in overlay/signoffs.toml",
          'upstream_id = "2-coloring-1-round"' in signoffs)
    check("it records the declaration it covers, not the whole record",
          f'declarations = ["{declaration}"]' in signoffs)
    check("it binds to the record's statement hash",
          record["statement_hash"] in signoffs,
          "the reviewer must not have to copy hashes by hand")
    check("it records the verdict", 'verdict = "approved"' in signoffs)

    # --- registry entry ---------------------------------------------------
    result = run(sandbox, issue_body("Registry entry", "artificial-theorems",
                                     "Registry/ArtificialTheorems/Opt/SGD.lean"))
    check("registry sign-off is accepted", result.returncode == 0, result.stderr[-400:])
    entry = open(os.path.join(sandbox, "entries", "artificial-theorems.toml")).read()
    check("registry sign-off lands in the entry TOML",
          'spec_files = ["Registry/ArtificialTheorems/Opt/SGD.lean"]' in entry)
    check("registry sign-off records a verdict too", 'verdict = "approved"' in entry)

    # --- rejections are recorded, not discarded ---------------------------
    result = run(sandbox, issue_body("Overlay record: leanpool", "2-coloring-1-round",
                                     "*", verdict="Rejected",
                                     comments="statement omits the boundary case"))
    signoffs = open(os.path.join(sandbox, "overlay", "signoffs.toml")).read()
    check("a rejection is recorded rather than dropped",
          result.returncode == 0 and 'verdict = "rejected"' in signoffs)

    # --- refusals ---------------------------------------------------------
    result = run(sandbox, issue_body("Overlay record: leanpool", "no-such-record", "*"))
    check("unknown overlay id is refused", result.returncode == 1,
          f"rc={result.returncode}")

    result = run(sandbox, issue_body("Overlay record: leanpool", "2-coloring-1-round",
                                     "Nonexistent.declaration"))
    check("a declaration the record does not have is refused",
          result.returncode == 1, f"rc={result.returncode}")

    result = run(sandbox, issue_body("Registry entry", "artificial-theorems",
                                     "Registry/Does/Not/Exist.lean"))
    check("a spec file that does not exist is refused", result.returncode == 1,
          f"rc={result.returncode}")

    # --- the pre-unification form still works -----------------------------
    legacy = ("### Entry ID\n\nartificial-theorems\n\n"
              "### Spec files reviewed\n\nRegistry/ArtificialTheorems/Opt/SGD.lean\n\n"
              "### Literature reference\n\nGadat, lecture notes\n\n"
              "### Verdict\n\nApproved\n\n### Comments\n\n_No response_\n")
    result = run(sandbox, legacy)
    check("an issue from the old form still processes", result.returncode == 0,
          result.stderr[-400:])

    shutil.rmtree(sandbox, ignore_errors=True)
    print(f"\nran 13 test(s); {len(FAILURES)} failure(s)")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
