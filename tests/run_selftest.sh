#!/bin/bash
# End-to-end test of the verification pipeline, without Mathlib.
#
# Builds a throwaway Lean project with two proved theorems, verifies it against
# the spec in specs/selftest/ through the real verify_entry.sh, and asserts that
# comparator AND nanoda both returned pass.
#
# It exists because the failures that matter here do not look like failures.
# Landrun's upgrade to urfave/cli v3 made it swallow the `--` separator that
# comparator uses to pass constants to lean4export; a mismatched
# comparator/lean4export pair breaks the same way; and a filter that cannot read
# declaration kinds used to drop real theorems and report a pass. Every one of
# those is invisible in an entry that has no ground truth. Here there is one:
# these two theorems are true and proved, so anything other than pass is a bug
# in the pipeline.
#
# Usage: tests/run_selftest.sh
# Exit codes: 0 pass, 1 the pipeline did not confirm the fixture, 2 setup error.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
WORK="$PROJECT_DIR/work/selftest-fixture"

echo "=== Materializing the fixture implementation repo ==="
rm -rf "$WORK"
mkdir -p "$WORK"
cp -r "$SCRIPT_DIR/selftest/impl/." "$WORK/"
(
    cd "$WORK"
    git init -q .
    git add -A
    git -c user.email=selftest@vibe.registry -c user.name=selftest commit -qm "self-test fixture"
)
COMMIT=$(cd "$WORK" && git rev-parse HEAD)
echo "Fixture repo: $WORK @ ${COMMIT:0:12}"

ENTRY="$PROJECT_DIR/work/selftest-entry.toml"
sed -e "s|__IMPL_URL__|$WORK|" -e "s|__IMPL_COMMIT__|$COMMIT|" \
    "$SCRIPT_DIR/selftest/entry.toml.template" > "$ENTRY"

echo ""
echo "=== Running the real pipeline ==="
rm -rf "$PROJECT_DIR/work/selftest"
"$PROJECT_DIR/scripts/verify_entry.sh" "$ENTRY" --require-nanoda

echo ""
echo "=== Checking the verdict ==="
python3 - "$PROJECT_DIR/results/selftest/latest.json" "$ENTRY" "$PROJECT_DIR/scripts" \
       "$PROJECT_DIR/specs/selftest" <<'PY'
import json, os, sys

with open(sys.argv[1]) as f:
    result = json.load(f)

problems = []
if result.get("overall") != "pass":
    problems.append(f"overall is {result.get('overall')!r}, expected 'pass'")

expected = {"Selftest.add_comm'", "Selftest.append_nil'"}
seen = {t["name"] for t in result.get("theorems", [])}
if seen != expected:
    problems.append(f"theorems {sorted(seen)} != expected {sorted(expected)}")

for theorem in result.get("theorems", []):
    for check in ("comparator", "nanoda"):
        if theorem.get(check) != "pass":
            problems.append(f"{theorem['name']}: {check} is {theorem.get(check)!r}, expected 'pass'")

tools = result.get("tools", {})
for tool in ("comparator", "lean4export", "nanoda", "landrun"):
    if not tools.get(tool):
        problems.append(f"no revision recorded for {tool}")

# A verdict must be bound to the statement it describes, or a spec can be edited
# under an unchanged name while the old verdict still reads as current.
sys.path.insert(0, os.path.join(sys.argv[3], "lib"))
from parse_toml import load_config
from spec_statement_hash import statement_hashes

current = statement_hashes(load_config(sys.argv[2]), sys.argv[4])
for theorem in result.get("theorems", []):
    recorded = theorem.get("spec_hash", "")
    expected = current.get(theorem["name"], "")
    if not recorded:
        problems.append(f"{theorem['name']}: no spec_hash recorded with the verdict")
    elif recorded != expected:
        problems.append(f"{theorem['name']}: spec_hash {recorded} != current {expected}")

if problems:
    print("SELF-TEST FAILED")
    for problem in problems:
        print(f"  - {problem}")
    sys.exit(1)

print("SELF-TEST PASSED: comparator and nanoda both confirmed both theorems")
print(f"  tools: " + ", ".join(f"{k}={v[:12]}" for k, v in sorted(tools.items()) if v))
PY
