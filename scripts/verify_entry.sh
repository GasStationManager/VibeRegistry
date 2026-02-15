#!/bin/bash
# Verify a single registry entry.
#
# Usage: ./scripts/verify_entry.sh entries/<entry>.toml [--level 1|2]
#
# Level 1 (default): lean4checker + SafeVerify
# Level 2: Level 1 + Comparator (sandboxed)
#
# Exit codes:
#   0 - All verifications passed
#   1 - Some verifications failed
#   2 - Configuration or setup error

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
PARSE_TOML="python3 $SCRIPT_DIR/lib/parse_toml.py"

# --- Parse arguments ---
if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <entry_config.toml> [--level 1|2]"
    exit 2
fi

CONFIG_FILE="$1"
LEVEL=1

shift
while [[ $# -gt 0 ]]; do
    case "$1" in
        --level)
            LEVEL="$2"
            shift 2
            ;;
        *)
            echo "Unknown argument: $1"
            exit 2
            ;;
    esac
done

if [[ ! -f "$CONFIG_FILE" ]]; then
    # Try relative to project dir
    CONFIG_FILE="$PROJECT_DIR/$CONFIG_FILE"
    if [[ ! -f "$CONFIG_FILE" ]]; then
        echo "ERROR: Config file not found: $1"
        exit 2
    fi
fi

echo "========================================="
echo "VibeRegistry: Entry Verification"
echo "========================================="
echo "Config: $CONFIG_FILE"
echo "Level: $LEVEL"
echo ""

# --- Parse config ---
ENTRY_ID=$($PARSE_TOML "$CONFIG_FILE" project.id)
REPO_URL=$($PARSE_TOML "$CONFIG_FILE" project.url)
COMMIT=$($PARSE_TOML "$CONFIG_FILE" project.commit)
STRATEGY=$($PARSE_TOML "$CONFIG_FILE" build.strategy)
TOOLCHAIN=$($PARSE_TOML "$CONFIG_FILE" lean.toolchain)
MATHLIB_TAG=$($PARSE_TOML "$CONFIG_FILE" lean.mathlib_tag)
THEOREMS_JSON=$($PARSE_TOML "$CONFIG_FILE" theorems)

# Parse optional tool versions for verification dependencies
export SAFE_VERIFY_REV=$($PARSE_TOML "$CONFIG_FILE" tools.safe_verify_rev 2>/dev/null || echo "")
export LEAN4CHECKER_REV=$($PARSE_TOML "$CONFIG_FILE" tools.lean4checker_rev 2>/dev/null || echo "")

echo "Entry: $ENTRY_ID"
echo "Repo: $REPO_URL"
echo "Commit: ${COMMIT:0:12}..."
echo "Strategy: $STRATEGY"
echo "Toolchain: $TOOLCHAIN"
echo "Mathlib: $MATHLIB_TAG"
echo ""

# --- Setup work directory ---
WORK_DIR="$PROJECT_DIR/work/$ENTRY_ID"
SPEC_DIR="$PROJECT_DIR/specs/$ENTRY_ID"
RESULTS_DIR="$PROJECT_DIR/results/$ENTRY_ID"

mkdir -p "$WORK_DIR" "$RESULTS_DIR"

if [[ ! -d "$SPEC_DIR" ]]; then
    echo "ERROR: Spec directory not found: $SPEC_DIR"
    exit 2
fi

# --- Build ---
echo "========================================="
echo "Step 1: Build"
echo "========================================="

REPO_DIR="$WORK_DIR/repo"

if [[ "$STRATEGY" == "copy" ]]; then
    source "$SCRIPT_DIR/lib/build_copy.sh"
    build_copy "$ENTRY_ID" "$REPO_URL" "$COMMIT" "$WORK_DIR" "$SPEC_DIR"
    REPO_DIR="$WORK_DIR/repo"
else
    echo "ERROR: Build strategy '$STRATEGY' not yet implemented"
    exit 2
fi

# NOTE: We do NOT cd into REPO_DIR to avoid CWD corruption if work/ gets cleaned.
# All lake commands below use subshells: (cd "$REPO_DIR" && lake ...)

# --- Determine olean path ---
# Lake stores oleans under .lake/build/lib/ — find the right subdirectory
BUILD_LIB="$REPO_DIR/.lake/build/lib"
if [[ -d "$BUILD_LIB/lean" ]]; then
    BUILD_LIB="$BUILD_LIB/lean"
fi

echo ""
echo "Build lib path: $BUILD_LIB"

# --- Level 1: lean4checker + SafeVerify ---
echo ""
echo "========================================="
echo "Step 2: Level 1 Verification"
echo "========================================="

FAILED=0
RESULTS=()
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

# Parse theorem groups
NUM_GROUPS=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; print(len(json.loads(sys.stdin.read())))")

for ((i=0; i<NUM_GROUPS; i++)); do
    SPEC_MODULE=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(d[$i]['spec_module'])")
    IMPL_MODULE=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(d[$i]['impl_module'])")
    NAMES_JSON=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(json.dumps(d[$i]['names']))")
    AXIOMS_JSON=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(json.dumps(d[$i].get('permitted_axioms', [])))")

    echo ""
    echo "-----------------------------------------"
    echo "Theorem group: $IMPL_MODULE"
    echo "  Spec: $SPEC_MODULE"
    echo "  Names: $NAMES_JSON"
    echo "-----------------------------------------"

    # Convert module name to olean path
    IMPL_OLEAN="$BUILD_LIB/$(echo "$IMPL_MODULE" | tr '.' '/').olean"
    SPEC_OLEAN="$BUILD_LIB/$(echo "$SPEC_MODULE" | tr '.' '/').olean"

    CHECKER_RESULT="skip"
    SAFE_VERIFY_RESULT="skip"
    COMPARATOR_RESULT="skip"

    # 2a. lean4checker on impl module
    echo "  Running lean4checker on $IMPL_MODULE..."
    if [[ -f "$IMPL_OLEAN" ]]; then
        if (cd "$REPO_DIR" && lake exe lean4checker "$IMPL_MODULE") 2>&1; then
            CHECKER_RESULT="pass"
            echo "  lean4checker: PASS"
        else
            CHECKER_RESULT="fail"
            echo "  lean4checker: FAIL"
            FAILED=1
        fi
    else
        echo "  WARNING: Impl olean not found: $IMPL_OLEAN"
        CHECKER_RESULT="fail"
        FAILED=1
    fi

    # 2b. SafeVerify on spec/impl pair
    echo "  Running safe_verify..."
    if [[ -f "$SPEC_OLEAN" ]] && [[ -f "$IMPL_OLEAN" ]]; then
        if (cd "$REPO_DIR" && lake exe safe_verify "$SPEC_OLEAN" "$IMPL_OLEAN") 2>&1; then
            SAFE_VERIFY_RESULT="pass"
            echo "  safe_verify: PASS"
        else
            SAFE_VERIFY_RESULT="fail"
            echo "  safe_verify: FAIL"
            FAILED=1
        fi
    else
        if [[ ! -f "$SPEC_OLEAN" ]]; then
            echo "  WARNING: Spec olean not found: $SPEC_OLEAN"
        fi
        if [[ ! -f "$IMPL_OLEAN" ]]; then
            echo "  WARNING: Impl olean not found: $IMPL_OLEAN"
        fi
        SAFE_VERIFY_RESULT="fail"
        FAILED=1
    fi

    # Build per-theorem results
    NAMES_COUNT=$(echo "$NAMES_JSON" | python3 -c "import sys,json; print(len(json.loads(sys.stdin.read())))")
    for ((j=0; j<NAMES_COUNT; j++)); do
        NAME=$(echo "$NAMES_JSON" | python3 -c "import sys,json; print(json.loads(sys.stdin.read())[$j])")
        RESULTS+=("{\"name\":\"$NAME\",\"spec_module\":\"$SPEC_MODULE\",\"impl_module\":\"$IMPL_MODULE\",\"lean4checker\":\"$CHECKER_RESULT\",\"safe_verify\":\"$SAFE_VERIFY_RESULT\",\"comparator\":\"$COMPARATOR_RESULT\"}")
    done
done

# --- Level 2: Comparator (if requested) ---
if [[ "$LEVEL" -ge 2 ]]; then
    echo ""
    echo "========================================="
    echo "Step 3: Level 2 Verification (Comparator)"
    echo "========================================="

    # Generate comparator configs
    COMP_CONFIG_DIR="$WORK_DIR/comparator_configs"
    python3 "$SCRIPT_DIR/generate_comparator_configs.py" "$CONFIG_FILE" "$COMP_CONFIG_DIR"

    # Find comparator binary
    COMPARATOR="${COMPARATOR_BIN:-}"
    if [[ -z "$COMPARATOR" ]] && command -v comparator &> /dev/null; then
        COMPARATOR="comparator"
    fi

    if [[ -z "$COMPARATOR" ]]; then
        echo "WARNING: Comparator binary not found. Skipping Level 2."
        echo "Set COMPARATOR_BIN or install comparator in PATH."
    else
        for config in "$COMP_CONFIG_DIR"/*.json; do
            if [[ -f "$config" ]]; then
                name=$(basename "$config" .json)
                echo ""
                echo "  Comparator: $name"
                if (cd "$REPO_DIR" && lake env "$COMPARATOR" "$config") 2>&1; then
                    echo "  Comparator $name: PASS"
                else
                    echo "  Comparator $name: FAIL"
                    FAILED=1
                fi
            fi
        done
    fi
fi

# --- Write results ---
echo ""
echo "========================================="
echo "Writing results..."
echo "========================================="

THEOREMS_ARRAY=$(printf '%s\n' "${RESULTS[@]}" | paste -sd ',' -)

OVERALL="pass"
if [[ $FAILED -ne 0 ]]; then
    OVERALL="fail"
fi

RESULT_JSON=$(cat <<EOF
{
  "entry_id": "$ENTRY_ID",
  "timestamp": "$TIMESTAMP",
  "commit": "$COMMIT",
  "lean_toolchain": "$TOOLCHAIN",
  "mathlib_tag": "$MATHLIB_TAG",
  "verification_level": $LEVEL,
  "build_strategy": "$STRATEGY",
  "theorems": [$THEOREMS_ARRAY],
  "overall": "$OVERALL"
}
EOF
)

echo "$RESULT_JSON" > "$RESULTS_DIR/latest.json"
mkdir -p "$RESULTS_DIR/history"
cp "$RESULTS_DIR/latest.json" "$RESULTS_DIR/history/$(date -u +%Y%m%d_%H%M%S).json"

echo "Results written to: $RESULTS_DIR/latest.json"

echo ""
echo "========================================="
if [[ $FAILED -eq 0 ]]; then
    echo "VERIFICATION PASSED"
    exit 0
else
    echo "VERIFICATION FAILED"
    exit 1
fi
