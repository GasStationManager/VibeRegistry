#!/bin/bash
# Install comparator verification tools (lean4export, comparator, optionally landrun).
#
# Usage: source scripts/lib/install_comparator_tools.sh
#        install_comparator_tools <toolchain_file> <tools_dir>
#
# Arguments:
#   toolchain_file  Path to lean-toolchain file (determines tool build version)
#   tools_dir       Directory to install tools into
#
# After calling, the following variables are exported:
#   LEAN4EXPORT_BIN  Path to lean4export binary
#   COMPARATOR_BIN   Path to comparator binary
#   LANDRUN_BIN      Path to landrun binary (empty if Go not available)
#
# Caching: if tools_dir already has tools built with matching toolchain, skip rebuild.
#
# IMPORTANT: This script NEVER changes the parent shell's CWD.
# All directory-sensitive operations use subshells.

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
    export LANDRUN_BIN=""
    if command -v go &> /dev/null; then
        local landrun_dir="$tools_dir/landrun"
        if [[ "$need_rebuild" == true ]] || [[ ! -f "$landrun_dir/landrun" ]]; then
            echo ""
            echo "--- Installing landrun ---"
            rm -rf "$landrun_dir"
            git clone --depth 1 https://github.com/Zouuup/landrun.git "$landrun_dir"
            (cd "$landrun_dir" && go build -o landrun .)
            echo "landrun built: $landrun_dir/landrun"
        else
            echo "landrun: using cached build"
        fi
        if [[ -f "$landrun_dir/landrun" ]]; then
            LANDRUN_BIN="$landrun_dir/landrun"
            export LANDRUN_BIN
        fi
    else
        echo "NOTE: Go not found, skipping landrun (sandboxing unavailable)"
    fi

    # --- 2. lean4export ---
    local lean4export_dir="$tools_dir/lean4export"
    export LEAN4EXPORT_BIN=""
    if [[ "$need_rebuild" == true ]] || [[ ! -f "$lean4export_dir/.lake/build/bin/lean4export" ]]; then
        echo ""
        echo "--- Installing lean4export ---"
        rm -rf "$lean4export_dir"
        git clone --depth 1 https://github.com/leanprover/lean4export.git "$lean4export_dir"
        cp "$toolchain_file" "$lean4export_dir/lean-toolchain"
        (cd "$lean4export_dir" && lake update && lake build)
        echo "lean4export built"
    else
        echo "lean4export: using cached build"
    fi
    if [[ -f "$lean4export_dir/.lake/build/bin/lean4export" ]]; then
        LEAN4EXPORT_BIN="$lean4export_dir/.lake/build/bin/lean4export"
        export LEAN4EXPORT_BIN
    fi

    # --- 3. comparator ---
    local comparator_dir="$tools_dir/comparator"
    export COMPARATOR_BIN=""
    if [[ "$need_rebuild" == true ]] || [[ ! -f "$comparator_dir/.lake/build/bin/comparator" ]]; then
        echo ""
        echo "--- Installing comparator ---"
        rm -rf "$comparator_dir"
        git clone --depth 1 https://github.com/leanprover/comparator.git "$comparator_dir"
        cp "$toolchain_file" "$comparator_dir/lean-toolchain"
        (cd "$comparator_dir" && lake update && lake build)
        echo "comparator built"
    else
        echo "comparator: using cached build"
    fi
    if [[ -f "$comparator_dir/.lake/build/bin/comparator" ]]; then
        COMPARATOR_BIN="$comparator_dir/.lake/build/bin/comparator"
        export COMPARATOR_BIN
    fi

    # Save toolchain for cache invalidation
    echo "$toolchain" > "$tc_cache"

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

    return 0
}
