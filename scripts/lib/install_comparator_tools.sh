#!/bin/bash
# Install comparator verification tools (lean4export, comparator, optionally
# landrun and nanoda).
#
# Usage: source scripts/lib/install_comparator_tools.sh
#        install_comparator_tools <toolchain_file> <tools_dir>
#        install_nanoda <tools_dir>
#
# Arguments:
#   toolchain_file  Path to lean-toolchain file (determines tool build version)
#   tools_dir       Directory to install tools into
#
# After calling, the following variables are exported:
#   LEAN4EXPORT_BIN  Path to lean4export binary
#   COMPARATOR_BIN   Path to comparator binary
#   LANDRUN_BIN      Path to landrun binary (empty if Go not available)
#   NANODA_BIN       Path to nanoda_bin (install_nanoda only; empty without cargo)
#   COMPARATOR_TOOL_REV / LEAN4EXPORT_TOOL_REV / NANODA_TOOL_REV
#                    Resolved tool revisions, recorded with the results
#
# Optional inputs: COMPARATOR_REV, LEAN4EXPORT_REV, NANODA_REV pin a revision
# explicitly; otherwise the newest revision whose lean-toolchain matches the
# entry's is used.
#
# Caching: if tools_dir already has tools built with matching toolchain, skip rebuild.
#
# IMPORTANT: This script NEVER changes the parent shell's CWD.
# All directory-sensitive operations use subshells.

# Pick the newest revision of a cloned tool whose lean-toolchain matches the one
# we need. These tools are Lean programs that load the target project's oleans,
# so they have to be built against the target's Lean version — and their default
# branch tracks whatever Lean release is current, which is usually a different
# one. Forcing our toolchain onto the default branch is what produced the
# "Invalid field `replay`" style build failures.
#
# Usage: _checkout_matching_toolchain <dir> <toolchain> [explicit_rev]
# Echoes "<revision> <how>" where <how> is exact, series, or pinned;
# returns 1 if no matching revision exists.
_checkout_matching_toolchain() {
    local dir="$1"
    local want="$2"
    local explicit="${3:-}"

    if [[ -n "$explicit" ]]; then
        (cd "$dir" && git checkout -q "$explicit") || return 1
        echo "$explicit pinned"
        return 0
    fi

    local head_tc
    head_tc=$(cd "$dir" && git show HEAD:lean-toolchain 2>/dev/null | tr -d '[:space:]')
    if [[ "$head_tc" == "$want" ]]; then
        echo "$(cd "$dir" && git rev-parse HEAD) exact"
        return 0
    fi

    # Series, e.g. leanprover/lean4:v4.29.1 -> v4.29. Tools pin release versions
    # and often skip patch releases (comparator pins v4.29.0, never v4.29.1), so
    # an exact match is not always available. Source within one minor series is
    # compatible, so the newest same-series revision built against our exact
    # toolchain is the right second choice.
    local want_series="${want%.*}"

    local match="" series_match="" commit
    while read -r commit; do
        local tc
        tc=$(cd "$dir" && git show "$commit:lean-toolchain" 2>/dev/null | tr -d '[:space:]')
        if [[ "$tc" == "$want" ]]; then
            match="$commit"
            break
        fi
        if [[ -z "$series_match" ]] && [[ "${tc%.*}" == "$want_series" ]]; then
            series_match="$commit"
        fi
    done < <(cd "$dir" && git log --format=%H --max-count=2000)

    if [[ -n "$match" ]]; then
        (cd "$dir" && git checkout -q "$match") || return 1
        echo "$match exact"
        return 0
    fi

    if [[ -n "$series_match" ]]; then
        (cd "$dir" && git checkout -q "$series_match") || return 1
        # Same series, different patch/rc: build it against our exact toolchain.
        echo "$want" > "$dir/lean-toolchain"
        echo "$series_match series"
        return 0
    fi

    return 1
}

# Log how a tool revision was chosen, without overstating the match.
_describe_rev() {
    local tool="$1" toolchain="$2" rev="$3" how="$4"
    case "$how" in
        exact)  echo "$tool revision: ${rev:0:12} (pins $toolchain)" ;;
        series) echo "$tool revision: ${rev:0:12} (nearest ${toolchain%.*} revision, rebuilt against $toolchain)" ;;
        *)      echo "$tool revision: ${rev:0:12} (pinned explicitly)" ;;
    esac
}

# Which export format version a comparator build can parse.
#
# comparator reads lean4export's output and rejects a format it does not know
# ("Version invalid" / "unsupported version"). The two tools are versioned
# independently, so a toolchain match is not enough: for v4.27.0-rc1 there are
# lean4export revisions emitting format 2.0.0 and others emitting 3.0.0, and
# only one of them pairs with a given comparator. Echoes e.g. "2.0.0", or
# nothing when the source does not state it (newer comparators negotiate).
_comparator_export_format() {
    local dir="$1"
    local parser="$dir/Comparator/Parser.lean"
    [[ -f "$parser" ]] || return 0
    grep -oE 'version != \(([0-9]+), *([0-9]+), *([0-9]+)\)' "$parser" \
        | head -1 \
        | grep -oE '[0-9]+, *[0-9]+, *[0-9]+' \
        | tr -d ' ' \
        | tr ',' '.'
}

# The export format a lean4export revision emits, as declared in its Main.lean.
_lean4export_format() {
    local dir="$1"
    local rev="$2"
    (cd "$dir" && git show "$rev:Main.lean" 2>/dev/null) \
        | grep -oE '"[0-9]+\.[0-9]+\.[0-9]+"' \
        | head -1 \
        | tr -d '"'
}

# Pick a lean4export revision that both builds against our Lean and emits the
# export format this comparator can read.
_checkout_lean4export() {
    local dir="$1" want_tc="$2" want_format="$3" explicit="${4:-}"

    if [[ -n "$explicit" ]]; then
        (cd "$dir" && git checkout -q "$explicit") || return 1
        echo "$explicit pinned"
        return 0
    fi

    if [[ -z "$want_format" ]]; then
        _checkout_matching_toolchain "$dir" "$want_tc"
        return $?
    fi

    local want_series="${want_tc%.*}"
    local best="" best_series="" commit
    while read -r commit; do
        local format
        format=$(_lean4export_format "$dir" "$commit")
        [[ "$format" == "$want_format" ]] || continue
        local tc
        tc=$(cd "$dir" && git show "$commit:lean-toolchain" 2>/dev/null | tr -d '[:space:]')
        if [[ "$tc" == "$want_tc" ]]; then
            best="$commit"
            break
        fi
        if [[ -z "$best_series" ]] && [[ "${tc%.*}" == "$want_series" ]]; then
            best_series="$commit"
        fi
    done < <(cd "$dir" && git log --format=%H --max-count=2000)

    if [[ -n "$best" ]]; then
        (cd "$dir" && git checkout -q "$best") || return 1
        echo "$best exact"
        return 0
    fi
    if [[ -n "$best_series" ]]; then
        (cd "$dir" && git checkout -q "$best_series") || return 1
        echo "$want_tc" > "$dir/lean-toolchain"
        echo "$best_series series"
        return 0
    fi
    return 1
}

# Build a cloned Lake project. Prefers its committed lake-manifest.json over
# `lake update`: re-resolving would un-pin the dependency revisions of a tool
# whose whole job is reproducible verification, and it forces a Reservoir lookup
# that a restricted network may not allow.
_lake_build_tool() {
    local dir="$1"
    if [[ -f "$dir/lake-manifest.json" ]]; then
        echo "  using committed lake-manifest.json (no lake update)"
        (cd "$dir" && lake build) || return 1
    else
        (cd "$dir" && lake update && lake build) || return 1
    fi
    return 0
}

# comparator passes constants to lean4export after a `--` separator. Some landrun
# builds consume it, which turns every comparator run into an unrelated-looking
# failure, so check before we rely on it.
landrun_preserves_separator() {
    local landrun_bin="$1"
    local out
    out=$("$landrun_bin" --best-effort --rox / /bin/echo a -- b 2>/dev/null || true)
    if [[ "$out" == *"a -- b"* ]]; then
        return 0
    fi
    return 1
}

install_comparator_tools() {
    local toolchain_file="$1"
    local tools_dir="$2"

    if [[ ! -f "$toolchain_file" ]]; then
        echo "ERROR: Toolchain file not found: $toolchain_file"
        return 1
    fi

    local toolchain
    toolchain=$(cat "$toolchain_file" | tr -d '[:space:]')
    echo "Installing comparator tools for toolchain: $toolchain"
    echo "Tools directory: $tools_dir"

    mkdir -p "$tools_dir"

    # Record current toolchain for cache invalidation
    local tc_cache="$tools_dir/.toolchain"
    local cached_tc=""
    if [[ -f "$tc_cache" ]]; then
        cached_tc=$(cat "$tc_cache" | tr -d '[:space:]')
    fi

    local need_rebuild=false
    if [[ "$cached_tc" != "$toolchain" ]]; then
        echo "Toolchain changed ($cached_tc -> $toolchain), rebuilding tools..."
        need_rebuild=true
    fi

    # --- 1. landrun (optional, requires Go) ---
    #
    # Pinned, and not to the default branch. comparator invokes
    # `lean4export <module> -- <constants>` through landrun; since landrun's
    # upgrade from urfave/cli v2 to v3 (e53db14, released in v0.1.16) landrun
    # swallows the `--`, so lean4export reads the constant names as module names
    # and every comparator run dies with "unknown module prefix 'Nat'". Nothing
    # in our pipeline reports that as anything but a comparator failure, so an
    # unpinned landrun is a way for the primary check to stop working quietly.
    # 5283024 is the commit before that upgrade. Override with tools.landrun_rev.
    export LANDRUN_BIN=""
    local landrun_rev="${LANDRUN_REV:-5283024a2f49b28046c3b4a06d7d775c058d4d80}"
    if command -v go &> /dev/null; then
        local landrun_dir="$tools_dir/landrun"
        if [[ "$need_rebuild" == true ]] || [[ ! -f "$landrun_dir/landrun" ]]; then
            echo ""
            echo "--- Installing landrun (${landrun_rev:0:12}) ---"
            rm -rf "$landrun_dir"
            git clone https://github.com/Zouuup/landrun.git "$landrun_dir"
            (cd "$landrun_dir" && git checkout -q "$landrun_rev" && go build -o landrun ./cmd/landrun)
            echo "landrun built: $landrun_dir/landrun"
        else
            echo "landrun: using cached build"
        fi
        if [[ -f "$landrun_dir/landrun" ]]; then
            LANDRUN_BIN="$landrun_dir/landrun"
            export LANDRUN_BIN
            export LANDRUN_TOOL_REV=$(cd "$landrun_dir" && git rev-parse HEAD)
            if ! landrun_preserves_separator "$LANDRUN_BIN"; then
                echo "ERROR: this landrun build drops the '--' separator, which"
                echo "       comparator needs to pass constant names to lean4export."
                echo "       Pin a working revision with tools.landrun_rev."
                return 1
            fi
        fi
    else
        echo "NOTE: Go not found, skipping landrun (sandboxing unavailable)"
    fi

    # --- 2. comparator (resolve its revision first) ---
    #
    # comparator drives lean4export, and the two speak a private protocol that
    # changes between revisions: pairing mismatched builds fails with things like
    # "unknown module prefix 'Nat'". comparator's own lake-manifest.json names the
    # lean4export revision it was developed against, so take the pair from there
    # rather than building each tool independently.
    local comparator_dir="$tools_dir/comparator"
    export COMPARATOR_BIN=""
    local comparator_needs_build=false
    if [[ "$need_rebuild" == true ]] || [[ ! -f "$comparator_dir/.lake/build/bin/comparator" ]]; then
        comparator_needs_build=true
        echo ""
        echo "--- Installing comparator ---"
        rm -rf "$comparator_dir"
        git clone https://github.com/leanprover/comparator.git "$comparator_dir"
        local comparator_rev
        if comparator_rev=$(_checkout_matching_toolchain "$comparator_dir" "$toolchain" "${COMPARATOR_REV:-}"); then
            _describe_rev "comparator" "$toolchain" $comparator_rev
        else
            echo "WARNING: no comparator revision pins $toolchain; building its default branch"
            echo "         against our toolchain. Pin tools.comparator_rev if this fails."
            cp "$toolchain_file" "$comparator_dir/lean-toolchain"
        fi
        export COMPARATOR_TOOL_REV=$(cd "$comparator_dir" && git rev-parse HEAD)
    else
        echo "comparator: using cached build"
        export COMPARATOR_TOOL_REV=$(cd "$comparator_dir" && git rev-parse HEAD)
    fi

    # --- 3. lean4export, at the revision comparator expects ---
    local lean4export_dir="$tools_dir/lean4export"
    export LEAN4EXPORT_BIN=""
    if [[ "$need_rebuild" == true ]] || [[ ! -f "$lean4export_dir/.lake/build/bin/lean4export" ]]; then
        echo ""
        echo "--- Installing lean4export ---"

        # What this comparator can read decides which lean4export we need.
        local want_format
        want_format=$(_comparator_export_format "$comparator_dir")
        if [[ -n "$want_format" ]]; then
            echo "  comparator reads export format $want_format"
        fi

        local pinned_export_rev="${LEAN4EXPORT_REV:-}"
        if [[ -z "$pinned_export_rev" ]] && [[ -f "$comparator_dir/lake-manifest.json" ]]; then
            pinned_export_rev=$(python3 -c "
import json, sys
try:
    manifest = json.load(open(sys.argv[1]))
except Exception:
    raise SystemExit
for package in manifest.get('packages', []):
    if package.get('name', '').lower() == 'lean4export':
        print(package.get('rev', ''))
        break
" "$comparator_dir/lake-manifest.json" 2>/dev/null || echo "")
            if [[ -n "$pinned_export_rev" ]]; then
                echo "  comparator pins lean4export ${pinned_export_rev:0:12}"
            fi
        fi

        rm -rf "$lean4export_dir"
        git clone https://github.com/leanprover/lean4export.git "$lean4export_dir"
        local lean4export_rev
        if lean4export_rev=$(_checkout_lean4export "$lean4export_dir" "$toolchain" "$want_format" "$pinned_export_rev"); then
            _describe_rev "lean4export" "$toolchain" $lean4export_rev
            if [[ -n "$want_format" ]]; then
                echo "  emits export format $(_lean4export_format "$lean4export_dir" HEAD)"
            fi
        else
            echo "ERROR: no lean4export revision both targets $toolchain and emits"
            echo "       export format ${want_format:-<unconstrained>}, which this comparator"
            echo "       requires. Pin one with tools.lean4export_rev."
            return 1
        fi
        # Whatever revision we took, it has to build against this entry's Lean.
        echo "$toolchain" > "$lean4export_dir/lean-toolchain"
        export LEAN4EXPORT_TOOL_REV=$(cd "$lean4export_dir" && git rev-parse HEAD)
        if ! _lake_build_tool "$lean4export_dir"; then
            echo "ERROR: lean4export build failed"
            return 1
        fi
        echo "lean4export built"
    else
        echo "lean4export: using cached build"
        export LEAN4EXPORT_TOOL_REV=$(cd "$lean4export_dir" && git rev-parse HEAD)
    fi
    if [[ -f "$lean4export_dir/.lake/build/bin/lean4export" ]]; then
        LEAN4EXPORT_BIN="$lean4export_dir/.lake/build/bin/lean4export"
        export LEAN4EXPORT_BIN
    fi

    # --- 4. build comparator ---
    if [[ "$comparator_needs_build" == true ]]; then
        if ! _lake_build_tool "$comparator_dir"; then
            echo "ERROR: comparator build failed"
            echo "       comparator must be built against the entry's Lean version"
            echo "       ($toolchain). Pin a compatible revision with tools.comparator_rev."
            return 1
        fi
        echo "comparator built"
    fi
    if [[ -f "$comparator_dir/.lake/build/bin/comparator" ]]; then
        COMPARATOR_BIN="$comparator_dir/.lake/build/bin/comparator"
        export COMPARATOR_BIN
    fi

    # --- Summary ---
    echo ""
    echo "--- Tool installation summary ---"
    echo "  LEAN4EXPORT_BIN: ${LEAN4EXPORT_BIN:-not installed}"
    echo "  COMPARATOR_BIN:  ${COMPARATOR_BIN:-not installed}"
    echo "  LANDRUN_BIN:     ${LANDRUN_BIN:-not installed (no Go)}"

    if [[ -z "$COMPARATOR_BIN" ]]; then
        echo "ERROR: comparator failed to build"
        return 1
    fi
    if [[ -z "$LEAN4EXPORT_BIN" ]]; then
        echo "ERROR: lean4export failed to build"
        return 1
    fi

    # Stamp the cache only now that both binaries exist. Stamping earlier meant a
    # failed build was remembered as a successful one, and the next run skipped
    # the rebuild and reported "using cached build" for a tool that was not there.
    echo "$toolchain" > "$tc_cache"

    return 0
}


# --- nanoda: independent Lean kernel used as comparator's second checker ---
#
# nanoda is a separate Rust implementation of the Lean 4 kernel. Comparator
# hands it the same exported proof it gives Lean's own kernel, so a proof only
# passes if two independently written kernels both accept it. That is the point
# of the check: a soundness bug in one kernel is unlikely to be shared by the
# other.
#
# Usage: install_nanoda <tools_dir>
# Exports NANODA_BIN (empty if cargo is unavailable or the build fails).
install_nanoda() {
    local tools_dir="$1"

    export NANODA_BIN=""

    if ! command -v cargo &> /dev/null; then
        echo "NOTE: cargo not found, skipping nanoda (second kernel unavailable)"
        return 1
    fi

    mkdir -p "$tools_dir"
    local nanoda_dir="$tools_dir/nanoda"
    local nanoda_rev="${NANODA_REV:-master}"

    if [[ ! -f "$nanoda_dir/target/release/nanoda_bin" ]]; then
        echo ""
        echo "--- Installing nanoda ($nanoda_rev) ---"
        rm -rf "$nanoda_dir"
        git clone https://github.com/ammkrn/nanoda_lib.git "$nanoda_dir"
        (cd "$nanoda_dir" && git checkout "$nanoda_rev" && cargo build --release)
        echo "nanoda built"
    else
        echo "nanoda: using cached build"
    fi

    if [[ -f "$nanoda_dir/target/release/nanoda_bin" ]]; then
        export NANODA_TOOL_REV=$(cd "$nanoda_dir" && git rev-parse HEAD)
        NANODA_BIN="$nanoda_dir/target/release/nanoda_bin"
        export NANODA_BIN
        echo "  NANODA_BIN: $NANODA_BIN"
        return 0
    fi

    echo "WARNING: nanoda build produced no binary"
    return 1
}
