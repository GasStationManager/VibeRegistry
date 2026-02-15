#!/bin/bash
# Build strategy: Copy specs into external repo
#
# Usage: source scripts/lib/build_copy.sh
#        build_copy <entry_id> <repo_url> <commit> <work_dir> <spec_dir>
#
# Environment variables (optional):
#   SAFE_VERIFY_REV  - SafeVerify git rev/tag (e.g., "v4.27.0")
#   LEAN4CHECKER_REV - lean4checker git rev/tag (e.g., "v4.27.0")
#
# IMPORTANT: This script NEVER changes the parent shell's CWD.
# All directory-sensitive operations use subshells or --dir flags.

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
        (cd "$repo_dir" && git fetch origin && git checkout "$commit")
    else
        echo "Cloning $repo_url at $commit..."
        git clone "$repo_url" "$repo_dir"
        (cd "$repo_dir" && git checkout "$commit")
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
            echo "  Patched lakefile.toml: added Registry lib"
        else
            echo "  lakefile.toml already has Registry lib"
        fi

        # 3b. Add SafeVerify dependency if not present and rev is specified
        if [[ -n "${SAFE_VERIFY_REV:-}" ]] && ! grep -q 'name = "SafeVerify"' "$repo_dir/lakefile.toml"; then
            echo '' >> "$repo_dir/lakefile.toml"
            echo '# REGISTRY: verification dependency' >> "$repo_dir/lakefile.toml"
            echo '[[require]]' >> "$repo_dir/lakefile.toml"
            echo 'name = "SafeVerify"' >> "$repo_dir/lakefile.toml"
            echo "git = \"https://github.com/GasStationManager/SafeVerify.git\"" >> "$repo_dir/lakefile.toml"
            echo "rev = \"$SAFE_VERIFY_REV\"" >> "$repo_dir/lakefile.toml"
            echo "  Patched lakefile.toml: added SafeVerify @ $SAFE_VERIFY_REV"
        fi

        # 3c. Add lean4checker dependency if not present and rev is specified
        if [[ -n "${LEAN4CHECKER_REV:-}" ]] && ! grep -q 'name = "lean4checker"' "$repo_dir/lakefile.toml"; then
            echo '' >> "$repo_dir/lakefile.toml"
            echo '# REGISTRY: verification dependency' >> "$repo_dir/lakefile.toml"
            echo '[[require]]' >> "$repo_dir/lakefile.toml"
            echo 'name = "lean4checker"' >> "$repo_dir/lakefile.toml"
            echo "git = \"https://github.com/leanprover/lean4checker.git\"" >> "$repo_dir/lakefile.toml"
            echo "rev = \"$LEAN4CHECKER_REV\"" >> "$repo_dir/lakefile.toml"
            echo "  Patched lakefile.toml: added lean4checker @ $LEAN4CHECKER_REV"
        fi

    elif [[ -f "$repo_dir/lakefile.lean" ]]; then
        # Lean format: append lean_lib declaration
        if ! grep -q 'lean_lib.*Registry' "$repo_dir/lakefile.lean"; then
            echo '' >> "$repo_dir/lakefile.lean"
            echo '-- REGISTRY: auto-generated spec library' >> "$repo_dir/lakefile.lean"
            echo 'lean_lib «Registry» where' >> "$repo_dir/lakefile.lean"
            echo '  srcDir := "."' >> "$repo_dir/lakefile.lean"
            echo "  Patched lakefile.lean: added Registry lib"
        else
            echo "  lakefile.lean already has Registry lib"
        fi

        # 3b. Add SafeVerify dependency if not present and rev is specified
        if [[ -n "${SAFE_VERIFY_REV:-}" ]] && ! grep -q 'SafeVerify' "$repo_dir/lakefile.lean"; then
            echo '' >> "$repo_dir/lakefile.lean"
            echo '-- REGISTRY: verification dependency' >> "$repo_dir/lakefile.lean"
            echo 'require SafeVerify from git' >> "$repo_dir/lakefile.lean"
            echo "  \"https://github.com/GasStationManager/SafeVerify.git\" @ \"$SAFE_VERIFY_REV\"" >> "$repo_dir/lakefile.lean"
            echo "  Patched lakefile.lean: added SafeVerify @ $SAFE_VERIFY_REV"
        fi

        # 3c. Add lean4checker dependency if not present and rev is specified
        if [[ -n "${LEAN4CHECKER_REV:-}" ]] && ! grep -q 'lean4checker' "$repo_dir/lakefile.lean"; then
            echo '' >> "$repo_dir/lakefile.lean"
            echo '-- REGISTRY: verification dependency' >> "$repo_dir/lakefile.lean"
            echo 'require lean4checker from git' >> "$repo_dir/lakefile.lean"
            echo "  \"https://github.com/leanprover/lean4checker.git\" @ \"$LEAN4CHECKER_REV\"" >> "$repo_dir/lakefile.lean"
            echo "  Patched lakefile.lean: added lean4checker @ $LEAN4CHECKER_REV"
        fi

    else
        echo "ERROR: No lakefile.toml or lakefile.lean found in $repo_dir"
        return 1
    fi

    # 3d. Add verification tool entries to lake-manifest.json if present
    if [[ -f "$repo_dir/lake-manifest.json" ]] && [[ -n "${SAFE_VERIFY_REV:-}" || -n "${LEAN4CHECKER_REV:-}" ]]; then
        echo "Updating lake-manifest.json with verification tool entries..."
        python3 - "$repo_dir/lake-manifest.json" "${SAFE_VERIFY_REV:-}" "${LEAN4CHECKER_REV:-}" << 'PYEOF'
import json, sys

manifest_path = sys.argv[1]
sv_rev = sys.argv[2] if len(sys.argv) > 2 else ""
lc_rev = sys.argv[3] if len(sys.argv) > 3 else ""

with open(manifest_path) as f:
    manifest = json.load(f)

# Fix manifest name if it contains hyphens (not a valid Lean Name)
if isinstance(manifest.get("name"), str) and "-" in manifest["name"]:
    manifest["name"] = manifest["name"].replace("-", "_")

names = [p["name"] for p in manifest.get("packages", [])]

if sv_rev and "SafeVerify" not in names:
    manifest["packages"].append({
        "type": "git",
        "subDir": None,
        "scope": "",
        "rev": sv_rev,
        "name": "SafeVerify",
        "manifestFile": "lake-manifest.json",
        "inputRev": sv_rev,
        "inherited": False,
        "configFile": "lakefile.lean",
        "url": "https://github.com/GasStationManager/SafeVerify.git"
    })
    print(f"  Added SafeVerify @ {sv_rev}")

if lc_rev and "lean4checker" not in names:
    manifest["packages"].append({
        "type": "git",
        "subDir": None,
        "scope": "",
        "rev": lc_rev,
        "name": "lean4checker",
        "manifestFile": "lake-manifest.json",
        "inputRev": lc_rev,
        "inherited": False,
        "configFile": "lakefile.toml",
        "url": "https://github.com/leanprover/lean4checker.git"
    })
    print(f"  Added lean4checker @ {lc_rev}")

with open(manifest_path, "w") as f:
    json.dump(manifest, f, indent=2)
    f.write("\n")
PYEOF
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
    # IMPORTANT: Use subshell for cd to avoid corrupting parent shell CWD
    echo "Fetching Mathlib cache..."
    (cd "$repo_dir" && lake exe cache get) || echo "WARNING: cache get failed, building from source"

    echo "Building impl (default targets)..."
    (cd "$repo_dir" && lake build)
    echo "Building Registry specs..."
    # Build each spec module individually rather than the combined Registry target.
    # Spec modules may import impl (SLT) modules, which can cause name conflicts when
    # the root Registry.lean tries to import all spec modules together.
    local spec_modules
    spec_modules=$(find "$repo_dir/Registry" -name "*.lean" \
        | sed "s|^$repo_dir/||; s|\.lean$||; s|/|.|g" \
        | sort)
    for mod in $spec_modules; do
        echo "  Building $mod..."
        (cd "$repo_dir" && lake build "$mod")
    done
    echo "Build complete."

    # Return the repo directory for downstream use
    echo "REPO_DIR=$repo_dir"
}
