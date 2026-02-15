#!/bin/bash
# Build strategy: Copy specs into external repo
#
# Usage: source scripts/lib/build_copy.sh
#        build_copy <entry_id> <repo_url> <commit> <work_dir> <spec_dir>
#
# This script:
# 1. Clones the external repo at the pinned commit
# 2. Copies registry spec files into the cloned repo
# 3. Patches the repo's lakefile to include the Registry lean_lib
# 4. Builds everything with `lake build`

build_copy() {
    local entry_id="$1"
    local repo_url="$2"
    local commit="$3"
    local work_dir="$4"
    local spec_dir="$5"

    echo "Build strategy: copy"
    echo "  Entry: $entry_id"
    echo "  Repo: $repo_url"
    echo "  Commit: $commit"
    echo "  Work dir: $work_dir"
    echo "  Spec dir: $spec_dir"

    # 1. Clone external repo at pinned commit
    local repo_dir="$work_dir/repo"
    if [[ -d "$repo_dir" ]]; then
        echo "Repo directory already exists, reusing: $repo_dir"
        cd "$repo_dir"
        git fetch origin
        git checkout "$commit"
    else
        echo "Cloning $repo_url at $commit..."
        git clone "$repo_url" "$repo_dir"
        cd "$repo_dir"
        git checkout "$commit"
    fi

    # 2. Copy spec files into the cloned repo
    echo "Copying spec files..."
    if [[ -d "$spec_dir/Registry" ]]; then
        cp -r "$spec_dir/Registry" "$repo_dir/"
        echo "  Copied Registry/ directory"
    fi
    if [[ -f "$spec_dir/Registry.lean" ]]; then
        cp "$spec_dir/Registry.lean" "$repo_dir/"
        echo "  Copied Registry.lean"
    fi

    # 3. Patch lakefile to add Registry lean_lib
    echo "Patching lakefile..."
    if [[ -f "$repo_dir/lakefile.toml" ]]; then
        # TOML format: append lean_lib entry
        if ! grep -q 'name = "Registry"' "$repo_dir/lakefile.toml"; then
            echo '' >> "$repo_dir/lakefile.toml"
            echo '# REGISTRY: auto-generated spec library' >> "$repo_dir/lakefile.toml"
            echo '[[lean_lib]]' >> "$repo_dir/lakefile.toml"
            echo 'name = "Registry"' >> "$repo_dir/lakefile.toml"
            echo "  Patched lakefile.toml"
        else
            echo "  lakefile.toml already has Registry lib"
        fi
    elif [[ -f "$repo_dir/lakefile.lean" ]]; then
        # Lean format: append lean_lib declaration
        if ! grep -q 'lean_lib.*Registry' "$repo_dir/lakefile.lean"; then
            echo '' >> "$repo_dir/lakefile.lean"
            echo '-- REGISTRY: auto-generated spec library' >> "$repo_dir/lakefile.lean"
            echo 'lean_lib «Registry» where' >> "$repo_dir/lakefile.lean"
            echo '  srcDir := "."' >> "$repo_dir/lakefile.lean"
            echo "  Patched lakefile.lean"
        else
            echo "  lakefile.lean already has Registry lib"
        fi
    else
        echo "ERROR: No lakefile.toml or lakefile.lean found in $repo_dir"
        return 1
    fi

    # 4. Validate lean-toolchain matches
    local repo_toolchain
    repo_toolchain=$(cat "$repo_dir/lean-toolchain" | tr -d '[:space:]')
    local spec_toolchain
    spec_toolchain=$(cat "$spec_dir/lean-toolchain" | tr -d '[:space:]')
    if [[ "$repo_toolchain" != "$spec_toolchain" ]]; then
        echo "WARNING: Toolchain mismatch!"
        echo "  Repo: $repo_toolchain"
        echo "  Spec: $spec_toolchain"
    fi

    # 5. Fetch Mathlib cache and build
    echo "Fetching Mathlib cache..."
    cd "$repo_dir"
    lake exe cache get || echo "WARNING: cache get failed, building from source"

    echo "Building impl (default targets)..."
    lake build
    echo "Building Registry specs..."
    lake build Registry
    echo "Build complete."

    # Return the repo directory for downstream use
    echo "REPO_DIR=$repo_dir"
}
