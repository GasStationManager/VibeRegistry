#!/bin/bash
# Archive current spec version before a Mathlib bump.
#
# Usage: ./scripts/archive_spec_version.sh <entry_id> <version_label>
#
# Example: ./scripts/archive_spec_version.sh artificial-theorems v1_mathlib-v4.27.0
#
# This creates a snapshot of the current spec files in:
#   specs/<entry>/spec_versions/<version_label>/
# along with a VERSION.toml recording metadata and file hashes.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

if [[ $# -lt 2 ]]; then
    echo "Usage: $0 <entry_id> <version_label>"
    echo "Example: $0 artificial-theorems v1_mathlib-v4.27.0"
    exit 1
fi

ENTRY_ID="$1"
VERSION_LABEL="$2"
SPEC_DIR="$PROJECT_DIR/specs/$ENTRY_ID"
VERSION_DIR="$SPEC_DIR/spec_versions/$VERSION_LABEL"

if [[ ! -d "$SPEC_DIR" ]]; then
    echo "ERROR: Spec directory not found: $SPEC_DIR"
    exit 1
fi

if [[ -d "$VERSION_DIR" ]]; then
    echo "ERROR: Version already exists: $VERSION_DIR"
    exit 1
fi

# Read current metadata
TOOLCHAIN=$(cat "$SPEC_DIR/lean-toolchain" | tr -d '[:space:]')

# Find Mathlib tag from lakefile
MATHLIB_TAG=$(grep -oP '@\s*"\K[^"]+' "$SPEC_DIR/lakefile.lean" 2>/dev/null || echo "unknown")

echo "Archiving spec version for $ENTRY_ID"
echo "  Version: $VERSION_LABEL"
echo "  Toolchain: $TOOLCHAIN"
echo "  Mathlib: $MATHLIB_TAG"

# Create version directory
mkdir -p "$VERSION_DIR"

# Copy spec .lean files (preserving directory structure)
cd "$SPEC_DIR"
find Registry -name "*.lean" | while read -r file; do
    mkdir -p "$VERSION_DIR/$(dirname "$file")"
    cp "$file" "$VERSION_DIR/$file"
done

# Generate VERSION.toml with file hashes
{
    echo "mathlib_tag = \"$MATHLIB_TAG\""
    echo "lean_toolchain = \"$TOOLCHAIN\""
    echo "created = \"$(date -u +%Y-%m-%d)\""
    echo ""
    echo "[file_hashes]"
    find Registry -name "*.lean" | sort | while read -r file; do
        hash=$(sha256sum "$file" | cut -d' ' -f1)
        # Use just the filename relative to Registry/
        echo "\"$file\" = \"sha256:$hash\""
    done
} > "$VERSION_DIR/VERSION.toml"

echo ""
echo "Archived to: $VERSION_DIR"
echo "VERSION.toml:"
cat "$VERSION_DIR/VERSION.toml"
