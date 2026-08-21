#!/bin/bash
# Verify a single registry entry.
#
# Usage: ./scripts/verify_entry.sh entries/<entry>.toml [check flags]
#
# Checks (comparator-primary model):
#   comparator    PRIMARY. Sandboxed rebuild + kernel-level proof export and
#                 statement/proof comparison. On by default.
#   nanoda        Replay comparator's exported proof through the independent
#                 nanoda kernel as a second checker. Opt-in.
#   safe_verify   OPTIONAL. Legacy olean-level spec/impl check.
#   lean4checker  OPTIONAL. Legacy kernel re-check of the impl module.
#
# Check flags:
#   --checks comparator,nanoda   Run exactly this set
#   --with-nanoda / --no-nanoda  Toggle one check (same for the other names,
#                                e.g. --with-safe-verify, --no-comparator)
#   --require-nanoda             Fail (rather than warn) if nanoda is missing
#   --level 1|2 / --skip-level-1 Deprecated aliases, kept for old CI callers
#
# Per-entry defaults come from the entry TOML's [checks] table; flags win.
#
# Environment variables (optional):
#   COMPARATOR_BIN   Path to comparator binary (auto-installed if missing)
#   LEAN4EXPORT_BIN  Path to lean4export binary (auto-installed if missing)
#   LANDRUN_BIN      Path to landrun binary (optional sandboxing)
#   NANODA_BIN       Path to nanoda_bin binary (auto-installed if missing)
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
    echo "Usage: $0 <entry_config.toml> [--checks comparator,nanoda] [--with-X|--no-X]"
    exit 2
fi

CONFIG_FILE="$1"
REQUIRE_NANODA=0
RESOLVE_ARGS=()

shift
while [[ $# -gt 0 ]]; do
    case "$1" in
        --level)
            RESOLVE_ARGS+=(--level "$2")
            shift 2
            ;;
        --skip-level-1)
            RESOLVE_ARGS+=(--skip-level-1)
            shift
            ;;
        --checks)
            RESOLVE_ARGS+=(--checks "$2")
            shift 2
            ;;
        --require-nanoda)
            REQUIRE_NANODA=1
            RESOLVE_ARGS+=(--with-nanoda)
            shift
            ;;
        --with-comparator|--no-comparator|--with-nanoda|--no-nanoda|\
        --with-safe-verify|--no-safe-verify|--with-lean4checker|--no-lean4checker)
            RESOLVE_ARGS+=("$1")
            shift
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

# --- Resolve which checks to run ---
CHECK_PLAN=$(python3 "$SCRIPT_DIR/lib/resolve_checks.py" "$CONFIG_FILE" "${RESOLVE_ARGS[@]+"${RESOLVE_ARGS[@]}"}")
eval "$CHECK_PLAN"

# NOTE: plain `[[ cond ]] && arr+=(x)` would abort the script under `set -e`
# whenever cond is false, so each append gets its own `if`.
ENABLED_CHECKS=()
if [[ "$CHECK_COMPARATOR" -eq 1 ]]; then ENABLED_CHECKS+=("comparator"); fi
if [[ "$CHECK_NANODA" -eq 1 ]]; then ENABLED_CHECKS+=("nanoda"); fi
if [[ "$CHECK_DEFINITIONS" -eq 1 ]]; then ENABLED_CHECKS+=("definitions"); fi
if [[ "$CHECK_SAFE_VERIFY" -eq 1 ]]; then ENABLED_CHECKS+=("safe_verify"); fi
if [[ "$CHECK_LEAN4CHECKER" -eq 1 ]]; then ENABLED_CHECKS+=("lean4checker"); fi

echo "========================================="
echo "VibeRegistry: Entry Verification"
echo "========================================="
echo "Config: $CONFIG_FILE"
echo "Checks: ${ENABLED_CHECKS[*]}"
echo ""

# --- Parse config ---
ENTRY_ID=$($PARSE_TOML "$CONFIG_FILE" project.id)
REPO_URL=$($PARSE_TOML "$CONFIG_FILE" project.url)
COMMIT=$($PARSE_TOML "$CONFIG_FILE" project.commit)
STRATEGY=$($PARSE_TOML "$CONFIG_FILE" build.strategy)
TOOLCHAIN=$($PARSE_TOML "$CONFIG_FILE" lean.toolchain)
MATHLIB_TAG=$($PARSE_TOML "$CONFIG_FILE" lean.mathlib_tag 2>/dev/null || echo "")
THEOREMS_JSON=$($PARSE_TOML "$CONFIG_FILE" theorems)

# Parse optional tool versions for verification dependencies.
# These are only injected into the impl repo's lakefile when the corresponding
# optional check is enabled — an unused dependency is one more way to break a
# build that comparator does not need.
if [[ "$CHECK_SAFE_VERIFY" -eq 1 ]]; then
    export SAFE_VERIFY_REV=$($PARSE_TOML "$CONFIG_FILE" tools.safe_verify_rev 2>/dev/null || echo "")
else
    export SAFE_VERIFY_REV=""
fi
if [[ "$CHECK_LEAN4CHECKER" -eq 1 ]]; then
    export LEAN4CHECKER_REV=$($PARSE_TOML "$CONFIG_FILE" tools.lean4checker_rev 2>/dev/null || echo "")
else
    export LEAN4CHECKER_REV=""
fi

# Optional pins for the comparator toolchain. Unset, the installer picks the
# revision of each tool whose lean-toolchain matches this entry's.
export COMPARATOR_REV=$($PARSE_TOML "$CONFIG_FILE" tools.comparator_rev 2>/dev/null || echo "")
export LEAN4EXPORT_REV=$($PARSE_TOML "$CONFIG_FILE" tools.lean4export_rev 2>/dev/null || echo "")
export NANODA_REV=$($PARSE_TOML "$CONFIG_FILE" tools.nanoda_rev 2>/dev/null || echo "")
export BUILD_TARGETS=$($PARSE_TOML "$CONFIG_FILE" build.targets 2>/dev/null || echo "")

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

# INVALIDATE: a result file describes one run. If this run dies before writing a
# new one, the old verdict must not be left behind looking current, so retire it
# now and restore nothing. History is kept under results/<entry>/history/.
if [[ -f "$RESULTS_DIR/latest.json" ]]; then
    mv "$RESULTS_DIR/latest.json" "$RESULTS_DIR/.latest.superseded.json"
fi

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

FAILED=0
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

# Must match sanitize_name() in generate_comparator_configs.py: the full impl
# module, dots to underscores, lowercased.
config_name_for() {
    echo "$1" | tr '.' '_' | tr '[:upper:]' '[:lower:]'
}

# A verdict is only as meaningful as the tool that produced it, so record which
# revision of each tool ran. Works whether the tool was auto-installed here or
# pointed at by *_BIN, by asking the binary's own checkout.
tool_revision() {
    local bin="$1"
    if [[ -z "$bin" ]] || [[ ! -e "$bin" ]]; then
        echo ""
        return
    fi
    (cd "$(dirname "$bin")" && git rev-parse HEAD 2>/dev/null) || echo ""
}

# Parse theorem groups into arrays for per-group result tracking
NUM_GROUPS=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; print(len(json.loads(sys.stdin.read())))")

declare -a GROUP_SPEC_MODULES GROUP_IMPL_MODULES GROUP_NAMES_JSON
declare -a GROUP_CHECKER GROUP_SAFEVERIFY GROUP_COMPARATOR GROUP_NANODA

for ((i=0; i<NUM_GROUPS; i++)); do
    GROUP_SPEC_MODULES[$i]=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(d[$i]['spec_module'])")
    GROUP_IMPL_MODULES[$i]=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(d[$i]['impl_module'])")
    GROUP_NAMES_JSON[$i]=$(echo "$THEOREMS_JSON" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(json.dumps(d[$i]['names']))")
    GROUP_CHECKER[$i]="skip"
    GROUP_SAFEVERIFY[$i]="skip"
    GROUP_COMPARATOR[$i]="skip"
    GROUP_NANODA[$i]="skip"
done

# --- Optional checks: lean4checker + SafeVerify ---
if [[ "$CHECK_LEAN4CHECKER" -eq 1 ]] || [[ "$CHECK_SAFE_VERIFY" -eq 1 ]]; then
echo ""
echo "========================================="
echo "Step 2: Optional checks (lean4checker / SafeVerify)"
echo "========================================="

for ((i=0; i<NUM_GROUPS; i++)); do
    SPEC_MODULE="${GROUP_SPEC_MODULES[$i]}"
    IMPL_MODULE="${GROUP_IMPL_MODULES[$i]}"
    NAMES_JSON="${GROUP_NAMES_JSON[$i]}"

    echo ""
    echo "-----------------------------------------"
    echo "Theorem group: $IMPL_MODULE"
    echo "  Spec: $SPEC_MODULE"
    echo "  Names: $NAMES_JSON"
    echo "-----------------------------------------"

    # Convert module name to olean path
    IMPL_OLEAN="$BUILD_LIB/$(echo "$IMPL_MODULE" | tr '.' '/').olean"
    SPEC_OLEAN="$BUILD_LIB/$(echo "$SPEC_MODULE" | tr '.' '/').olean"

    # 2a. lean4checker on impl module (optional)
    if [[ "$CHECK_LEAN4CHECKER" -eq 1 ]]; then
    echo "  Running lean4checker on $IMPL_MODULE..."
    if [[ -f "$IMPL_OLEAN" ]]; then
        if (cd "$REPO_DIR" && lake exe lean4checker "$IMPL_MODULE") 2>&1; then
            GROUP_CHECKER[$i]="pass"
            echo "  lean4checker: PASS"
        else
            GROUP_CHECKER[$i]="fail"
            echo "  lean4checker: FAIL"
            FAILED=1
        fi
    else
        echo "  WARNING: Impl olean not found: $IMPL_OLEAN"
        GROUP_CHECKER[$i]="fail"
        FAILED=1
    fi
    fi

    # 2b. SafeVerify on spec/impl pair (optional)
    if [[ "$CHECK_SAFE_VERIFY" -eq 1 ]]; then
    echo "  Running safe_verify..."
    if [[ -f "$SPEC_OLEAN" ]] && [[ -f "$IMPL_OLEAN" ]]; then
        if (cd "$REPO_DIR" && lake exe safe_verify "$SPEC_OLEAN" "$IMPL_OLEAN") 2>&1; then
            GROUP_SAFEVERIFY[$i]="pass"
            echo "  safe_verify: PASS"
        else
            GROUP_SAFEVERIFY[$i]="fail"
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
        GROUP_SAFEVERIFY[$i]="fail"
        FAILED=1
    fi
    fi
done

else
    echo ""
    echo "========================================="
    echo "No optional checks enabled (comparator-only run)"
    echo "========================================="
fi

# --- Primary check: Comparator (+ optional nanoda second kernel) ---
if [[ "$CHECK_COMPARATOR" -eq 1 ]]; then
    echo ""
    echo "========================================="
    echo "Step 3: Comparator (primary check)"
    echo "========================================="

    # Auto-install tools if not available
    COMPARATOR="${COMPARATOR_BIN:-}"
    if [[ -z "$COMPARATOR" ]] && command -v comparator &> /dev/null; then
        COMPARATOR="comparator"
    fi

    if [[ -z "$COMPARATOR" ]]; then
        echo "Comparator not found, attempting auto-install..."
        source "$SCRIPT_DIR/lib/install_comparator_tools.sh"
        TOOLS_DIR="$PROJECT_DIR/work/tools"
        if install_comparator_tools "$SPEC_DIR/lean-toolchain" "$TOOLS_DIR"; then
            COMPARATOR="$COMPARATOR_BIN"
        else
            echo "WARNING: Auto-install failed. Skipping comparator."
        fi
    fi

    # --- Resolve nanoda (comparator's optional second kernel) ---
    # comparator finds nanoda on PATH, or via COMPARATOR_NANODA. We only turn
    # the second kernel on in the generated configs when we actually have the
    # binary, so a missing nanoda degrades to a comparator-only run instead of
    # silently reporting a second-kernel check that never ran.
    NANODA_ENABLED=0
    if [[ "$CHECK_NANODA" -eq 1 ]]; then
        NANODA="${NANODA_BIN:-}"
        if [[ -z "$NANODA" ]] && command -v nanoda_bin &> /dev/null; then
            NANODA="$(command -v nanoda_bin)"
        fi
        if [[ -z "$NANODA" ]]; then
            echo "nanoda not found, attempting auto-install..."
            source "$SCRIPT_DIR/lib/install_comparator_tools.sh"
            if install_nanoda "$PROJECT_DIR/work/tools"; then
                NANODA="$NANODA_BIN"
            fi
        fi
        if [[ -n "$NANODA" ]] && [[ -x "$NANODA" ]]; then
            NANODA_ENABLED=1
            export COMPARATOR_NANODA="$NANODA"
            export PATH="$(dirname "$NANODA"):$PATH"
            echo "nanoda second kernel: $NANODA"
        else
            echo "WARNING: nanoda requested but not available."
            if [[ "$REQUIRE_NANODA" -eq 1 ]]; then
                echo "ERROR: --require-nanoda was given; refusing to continue."
                exit 2
            fi
            for ((i=0; i<NUM_GROUPS; i++)); do
                GROUP_NANODA[$i]="unavailable"
            done
        fi
    fi

    if [[ -n "$COMPARATOR" ]]; then
        # --- Convert verification tool deps to path type ---
        # build_copy.sh injects lean4checker and SafeVerify as git dependencies.
        # Inside landrun's Landlock sandbox, network is blocked, so Lake's
        # `git fetch` on these packages fails fatally. Converting to path deps
        # prevents Lake from running git operations on them.
        echo ""
        echo "Converting verification tool deps to path type..."
        python3 -c "
import json, sys

# Update lake-manifest.json
manifest_path = sys.argv[1] + '/lake-manifest.json'
with open(manifest_path) as f:
    m = json.load(f)
changed = False
for p in m['packages']:
    if p['name'] in ('lean4checker', 'SafeVerify') and p.get('type') == 'git':
        p['type'] = 'path'
        p['dir'] = '.lake/packages/' + p['name']
        for key in ('url', 'rev', 'inputRev', 'subDir'):
            p.pop(key, None)
        changed = True
        print(f\"  Manifest: converted {p['name']} to path type\")
if changed:
    with open(manifest_path, 'w') as f:
        json.dump(m, f, indent=2)
        f.write('\n')

# Update lakefile
for ext in ('lakefile.lean', 'lakefile.toml'):
    lf_path = sys.argv[1] + '/' + ext
    try:
        with open(lf_path) as f:
            content = f.read()
    except FileNotFoundError:
        continue

    import re
    original = content
    # .lean format: require X from git \"url\" @ \"rev\"
    for pkg in ('SafeVerify', 'lean4checker'):
        old = rf'require {pkg} from git\s*\n\s*\"[^\"]+\"\s*@\s*\"[^\"]+\"'
        new = f'require {pkg} from \".lake/packages/{pkg}\"'
        content_new = re.sub(old, new, content)
        if content_new != content:
            print(f'  Lakefile: converted {pkg} to path type')
            content = content_new
    # .toml format: [[require]]\nname = \"X\"\nscope...\nsource.type = \"git\"
    # (less common, skip for now)
    # Only write when content changed; an unconditional write bumps mtime
    # and can invalidate Lake's compiled-config cache for later lake calls.
    if content != original:
        with open(lf_path, 'w') as f:
            f.write(content)
" "$REPO_DIR"

        # --- Generate comparator configs ---
        COMP_CONFIG_DIR="$WORK_DIR/comparator_configs"
        rm -rf "$COMP_CONFIG_DIR"
        GEN_ARGS=()
        if [[ "$NANODA_ENABLED" -eq 1 ]]; then
            GEN_ARGS+=(--enable-nanoda)
        fi
        python3 "$SCRIPT_DIR/generate_comparator_configs.py" "$CONFIG_FILE" "$COMP_CONFIG_DIR" \
            "${GEN_ARGS[@]+"${GEN_ARGS[@]}"}"

        # --- Filter configs to theorem-only names ---
        # Comparator only accepts thmInfo/axiomInfo constants. Helper defs
        # (def, structure, etc.) cause "constant kind don't match" errors.
        # Use lean4export to detect and remove non-theorem names from configs.
        LEAN4EXPORT_FOR_FILTER="${LEAN4EXPORT_BIN:-}"
        if [[ -z "$LEAN4EXPORT_FOR_FILTER" ]]; then
            # lean4export may not be in env yet; find it from tools
            if [[ -f "$PROJECT_DIR/work/tools/lean4export/.lake/build/bin/lean4export" ]]; then
                LEAN4EXPORT_FOR_FILTER="$PROJECT_DIR/work/tools/lean4export/.lake/build/bin/lean4export"
            fi
        fi
        if [[ -n "$LEAN4EXPORT_FOR_FILTER" ]]; then
            echo ""
            echo "Filtering comparator configs to theorem-only names..."
            DEFINITIONS_MODE="drop"
            if [[ "$CHECK_DEFINITIONS" -eq 1 ]]; then
                DEFINITIONS_MODE="compare"
            fi
            FILTER_RC=0
            python3 "$SCRIPT_DIR/lib/filter_comparator_theorems.py" \
                "$REPO_DIR" "$LEAN4EXPORT_FOR_FILTER" "$COMP_CONFIG_DIR" \
                --definitions-mode "$DEFINITIONS_MODE" || FILTER_RC=$?

            if [[ "$FILTER_RC" -ne 0 ]]; then
                echo ""
                echo "ERROR: the theorem filter could not establish what it was"
                echo "       looking at (lean4export failed to report declaration"
                echo "       kinds). Refusing to treat these groups as checked."
                FAILED=1
            fi

            # A group may be recorded as not-applicable ONLY when the filter
            # positively established there is nothing here for comparator (a
            # definition-only group while `definitions` is off). A missing config
            # for any other reason is a failure, not a pass: dropping names
            # because a tool broke is exactly how unchecked theorems get reported
            # as checked.
            FILTER_REPORT="$COMP_CONFIG_DIR/_filter_report.json"
            for ((i=0; i<NUM_GROUPS; i++)); do
                CONFIG_KEY="$(config_name_for "${GROUP_IMPL_MODULES[$i]}")"
                EXPECTED_CONFIG="$COMP_CONFIG_DIR/$CONFIG_KEY.json"
                if [[ -f "$EXPECTED_CONFIG" ]]; then
                    continue
                fi
                STATUS=$(python3 -c "
import json, sys
try:
    report = json.load(open(sys.argv[1]))
except Exception:
    print('missing'); raise SystemExit
print(report.get('configs', {}).get(sys.argv[2], {}).get('status', 'missing'))
" "$FILTER_REPORT" "$CONFIG_KEY" 2>/dev/null || echo "missing")
                if [[ "$STATUS" == "removed" ]]; then
                    GROUP_COMPARATOR[$i]="not-applicable"
                else
                    echo "ERROR: no comparator config for ${GROUP_IMPL_MODULES[$i]} (filter status: $STATUS)"
                    GROUP_COMPARATOR[$i]="fail"
                    FAILED=1
                fi
            done
        else
            echo "WARNING: lean4export not available, skipping theorem filtering"
        fi

        # --- Security-critical: Remove impl oleans before comparator ---
        # Comparator re-exports and independently verifies proofs.
        # Impl oleans must be removed so the build re-compiles from source
        # under comparator's supervision.
        #
        # IMPORTANT: this must happen after theorem filtering above, because
        # the filter uses lean4export on the challenge module. Cleaning the
        # impl tree first can delete transitive imports needed just to load the
        # challenge module, causing the filter to drop configs and silently skip
        # comparator verification.
        echo ""
        echo "Cleaning impl oleans (security-critical)..."
        declare -A CLEAN_DIRS
        for ((i=0; i<NUM_GROUPS; i++)); do
            IMPL_MODULE="${GROUP_IMPL_MODULES[$i]}"
            # Extract top-level directory: ArtificialTheorems.Opt.SGD -> ArtificialTheorems
            TOP_DIR=$(echo "$IMPL_MODULE" | cut -d'.' -f1)
            CLEAN_DIRS["$TOP_DIR"]=1
        done

        for dir in "${!CLEAN_DIRS[@]}"; do
            local_path="$BUILD_LIB/$dir"
            if [[ -d "$local_path" ]]; then
                echo "  Removing: $local_path"
                rm -rf "$local_path"
            else
                echo "  Not found (already clean): $local_path"
            fi
        done
        echo "Impl olean cleanup complete."

        # --- Build mapping: config filename -> group index ---
        # generate_comparator_configs.py names files by last part of impl_module, lowercased
        # e.g., ArtificialTheorems.Opt.SGD -> sgd.json
        declare -A CONFIG_TO_GROUP
        for ((i=0; i<NUM_GROUPS; i++)); do
            CONFIG_TO_GROUP["$(config_name_for "${GROUP_IMPL_MODULES[$i]}")"]=$i
        done

        # --- Ensure tools are in PATH for comparator ---
        # Comparator internally invokes landrun (for sandboxed builds/exports)
        # and lean4export (for kernel-level proof export). Both must be in PATH.
        #
        # CRITICAL: We also prepend the actual toolchain bin/ to PATH so that
        # `lake` resolves to the real binary, not elan's proxy. Elan's proxy
        # fails inside landrun's Landlock sandbox because it tries to exec
        # the real binary from the toolchain, which requires execute permission
        # that landrun can't grant through the proxy indirection.
        LEAN_PREFIX=$(cd "$REPO_DIR" && lean --print-prefix)
        if [[ -d "$LEAN_PREFIX/bin" ]]; then
            export PATH="$LEAN_PREFIX/bin:$PATH"
            echo "Toolchain bin added to PATH: $LEAN_PREFIX/bin"
        fi

        LANDRUN="${LANDRUN_BIN:-}"
        if [[ -n "$LANDRUN" ]] && [[ -f "$LANDRUN" ]]; then
            LANDRUN_DIR=$(dirname "$LANDRUN")
            export PATH="$LANDRUN_DIR:$PATH"
            echo "landrun added to PATH: $LANDRUN_DIR"
        else
            echo "WARNING: landrun not available — comparator will fail without it"
        fi

        LEAN4EXPORT="${LEAN4EXPORT_BIN:-}"
        if [[ -n "$LEAN4EXPORT" ]] && [[ -f "$LEAN4EXPORT" ]]; then
            LEAN4EXPORT_DIR=$(dirname "$LEAN4EXPORT")
            export PATH="$LEAN4EXPORT_DIR:$PATH"
            echo "lean4export added to PATH: $LEAN4EXPORT_DIR"
        else
            echo "WARNING: lean4export not available — comparator will fail without it"
        fi

        # --- Run comparator per config ---
        for config in "$COMP_CONFIG_DIR"/*.json; do
            if [[ ! -f "$config" ]]; then
                continue
            fi

            config_name=$(basename "$config" .json)
            # Not a comparator config — the filter's own outcome report.
            if [[ "$config_name" == "_filter_report" ]]; then
                continue
            fi
            echo ""
            echo "-----------------------------------------"
            echo "Comparator: $config_name"
            echo "-----------------------------------------"

            # Find the group index for this config
            group_idx="${CONFIG_TO_GROUP[$config_name]:-}"
            if [[ -z "$group_idx" ]]; then
                echo "  WARNING: Cannot match config '$config_name' to a theorem group"
                echo "  Running comparator anyway..."
            fi

            # Run comparator via lake env (sets up LEAN_PATH)
            # Comparator internally uses landrun for sandboxing
            COMPARATOR_LOG=$(mktemp)
            if (cd "$REPO_DIR" && lake env "$COMPARATOR" "$config") 2>&1 | tee "$COMPARATOR_LOG"; then
                echo "  Comparator $config_name: PASS"
                if [[ -n "$group_idx" ]]; then
                    GROUP_COMPARATOR[$group_idx]="pass"
                    if [[ "$NANODA_ENABLED" -eq 1 ]]; then
                        GROUP_NANODA[$group_idx]="pass"
                    fi
                fi
            else
                echo "  Comparator $config_name: FAIL"
                if [[ -n "$group_idx" ]]; then
                    GROUP_COMPARATOR[$group_idx]="fail"
                    if [[ "$NANODA_ENABLED" -eq 1 ]]; then
                        # The second kernel only has a verdict if the run got as
                        # far as replaying the export through it. A comparator
                        # failure earlier than that (a build error, say) is not a
                        # nanoda rejection, and recording one would be a lie.
                        if grep -qi "noda" "$COMPARATOR_LOG"; then
                            GROUP_NANODA[$group_idx]="fail"
                        else
                            GROUP_NANODA[$group_idx]="not-reached"
                        fi
                    fi
                fi
                FAILED=1

                # Diagnostic: if the failure was a const mismatch, dump both
                # exports so we can see exactly what diverged at the kernel level.
                # `|| true` matters: under `set -e` a non-matching grep here
                # aborted the whole script, so a comparator failure of any other
                # kind never reached the results write — and the stale results
                # file from the previous run, saying "pass", stayed on disk.
                FAILING_CONST=$(grep -oP "Const does not match between challenge and target '\K[^']+" "$COMPARATOR_LOG" | head -1 || true)
                if [[ -n "$FAILING_CONST" ]] && [[ -n "$LEAN4EXPORT" ]] && [[ -f "$LEAN4EXPORT" ]]; then
                    echo ""
                    echo "=== DIAGNOSTIC: export diff for $FAILING_CONST ==="
                    CHALLENGE_MODULE=$(python3 -c "import json; print(json.load(open('$config'))['challenge_module'])" 2>/dev/null || true)
                    SOLUTION_MODULE=$(python3 -c "import json; print(json.load(open('$config'))['solution_module'])" 2>/dev/null || true)
                    SPEC_OUT=$(mktemp)
                    IMPL_OUT=$(mktemp)
                    (cd "$REPO_DIR" && lake env "$LEAN4EXPORT" "$CHALLENGE_MODULE" -- "$FAILING_CONST" > "$SPEC_OUT" 2>&1) || echo "  (spec export failed)"
                    (cd "$REPO_DIR" && lake env "$LEAN4EXPORT" "$SOLUTION_MODULE" -- "$FAILING_CONST" > "$IMPL_OUT" 2>&1) || echo "  (impl export failed)"
                    echo "--- Spec export size: $(wc -l < "$SPEC_OUT") lines, Impl export size: $(wc -l < "$IMPL_OUT") lines ---"
                    echo "--- canonical form comparison (names resolved, index noise removed) ---"
                    python3 "$PROJECT_DIR/scripts/lib/canonical_const_diff.py" \
                        "$FAILING_CONST" "$SPEC_OUT" "$IMPL_OUT" 2>&1 | head -3000 || true
                    echo "=== END DIAGNOSTIC ==="
                    rm -f "$SPEC_OUT" "$IMPL_OUT"
                fi
            fi
            rm -f "$COMPARATOR_LOG"
        done
    fi
fi

# --- Build per-theorem results from per-group arrays ---
RESULTS=()
for ((i=0; i<NUM_GROUPS; i++)); do
    SPEC_MODULE="${GROUP_SPEC_MODULES[$i]}"
    IMPL_MODULE="${GROUP_IMPL_MODULES[$i]}"
    NAMES_JSON="${GROUP_NAMES_JSON[$i]}"
    CHECKER_RESULT="${GROUP_CHECKER[$i]}"
    SAFE_VERIFY_RESULT="${GROUP_SAFEVERIFY[$i]}"
    COMPARATOR_RESULT="${GROUP_COMPARATOR[$i]}"
    NANODA_RESULT="${GROUP_NANODA[$i]}"

    NAMES_COUNT=$(echo "$NAMES_JSON" | python3 -c "import sys,json; print(len(json.loads(sys.stdin.read())))")
    for ((j=0; j<NAMES_COUNT; j++)); do
        NAME=$(echo "$NAMES_JSON" | python3 -c "import sys,json; print(json.loads(sys.stdin.read())[$j])")
        RESULTS+=("{\"name\":\"$NAME\",\"spec_module\":\"$SPEC_MODULE\",\"impl_module\":\"$IMPL_MODULE\",\"comparator\":\"$COMPARATOR_RESULT\",\"nanoda\":\"$NANODA_RESULT\",\"safe_verify\":\"$SAFE_VERIFY_RESULT\",\"lean4checker\":\"$CHECKER_RESULT\"}")
    done
done

# --- Guard: the primary check must actually produce a verdict ---
# (A run that dies before this point leaves no new result file; the stale one
#  from the previous run is invalidated at startup, see INVALIDATE below.)
# A run where comparator was requested but never reported on a group is not a
# pass. "not-applicable" is fine (the group holds nothing comparator checks);
# "skip" means the check was asked for and silently did not happen.
if [[ "$CHECK_COMPARATOR" -eq 1 ]]; then
    for ((i=0; i<NUM_GROUPS; i++)); do
        if [[ "${GROUP_COMPARATOR[$i]}" == "skip" ]]; then
            echo ""
            echo "ERROR: comparator produced no verdict for ${GROUP_IMPL_MODULES[$i]}."
            echo "       The primary check was enabled but did not run for this group."
            FAILED=1
        fi
    done
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
  "verification_level": $LEGACY_LEVEL,
  "primary_check": "comparator",
  "checks": {
    "comparator": $([[ "$CHECK_COMPARATOR" -eq 1 ]] && echo true || echo false),
    "nanoda": $([[ "${NANODA_ENABLED:-0}" -eq 1 ]] && echo true || echo false),
    "definitions": $([[ "$CHECK_DEFINITIONS" -eq 1 ]] && echo true || echo false),
    "safe_verify": $([[ "$CHECK_SAFE_VERIFY" -eq 1 ]] && echo true || echo false),
    "lean4checker": $([[ "$CHECK_LEAN4CHECKER" -eq 1 ]] && echo true || echo false)
  },
  "build_strategy": "$STRATEGY",
  "tools": {
    "comparator": "$(tool_revision "${COMPARATOR:-}")",
    "lean4export": "$(tool_revision "${LEAN4EXPORT:-${LEAN4EXPORT_BIN:-}}")",
    "nanoda": "$(tool_revision "${NANODA:-}")",
    "landrun": "$(tool_revision "${LANDRUN:-}")"
  },
  "theorems": [$THEOREMS_ARRAY],
  "overall": "$OVERALL"
}
EOF
)

echo "$RESULT_JSON" > "$RESULTS_DIR/latest.json"
# This run produced a verdict, so the retired one is no longer needed.
rm -f "$RESULTS_DIR/.latest.superseded.json"
mkdir -p "$RESULTS_DIR/history"
cp "$RESULTS_DIR/latest.json" "$RESULTS_DIR/history/$(date -u +%Y%m%d_%H%M%S).json"

# Enrich results with sign-off data (if any signoffs exist in the entry TOML)
python3 "$SCRIPT_DIR/lib/enrich_results_with_signoffs.py" "$RESULTS_DIR/latest.json" "$CONFIG_FILE" 2>/dev/null || true

echo "Results written to: $RESULTS_DIR/latest.json"

echo ""
echo "========================================="
if [[ $FAILED -eq 0 ]]; then
    echo "VERIFICATION PASSED (checks: ${ENABLED_CHECKS[*]})"
    exit 0
else
    echo "VERIFICATION FAILED"
    exit 1
fi
