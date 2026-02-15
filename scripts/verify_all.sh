#!/bin/bash
# Verify all registry entries.
#
# Usage: ./scripts/verify_all.sh [--level 1|2]
#
# Iterates over all entry configs in entries/ and runs verify_entry.sh on each.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

LEVEL_ARGS=""
while [[ $# -gt 0 ]]; do
    case "$1" in
        --level)
            LEVEL_ARGS="--level $2"
            shift 2
            ;;
        *)
            echo "Unknown argument: $1"
            exit 2
            ;;
    esac
done

echo "========================================="
echo "VibeRegistry: Verify All Entries"
echo "========================================="
echo ""

TOTAL=0
PASSED=0
FAILED_ENTRIES=()

for config in "$PROJECT_DIR/entries"/*.toml; do
    if [[ -f "$config" ]]; then
        entry_name=$(basename "$config" .toml)
        TOTAL=$((TOTAL + 1))

        echo ""
        echo "========================================="
        echo "Entry: $entry_name"
        echo "========================================="

        if "$SCRIPT_DIR/verify_entry.sh" "$config" $LEVEL_ARGS; then
            PASSED=$((PASSED + 1))
        else
            FAILED_ENTRIES+=("$entry_name")
        fi
    fi
done

echo ""
echo "========================================="
echo "Summary: $PASSED/$TOTAL entries passed"
if [[ ${#FAILED_ENTRIES[@]} -gt 0 ]]; then
    echo "Failed: ${FAILED_ENTRIES[*]}"
    exit 1
else
    echo "All entries verified successfully!"
    exit 0
fi
