#!/usr/bin/env python3
"""
Check sign-off staleness by comparing current spec file hashes against stored hashes.

Usage:
    python3 check_signoff_staleness.py <entry.toml>

Reports:
    CURRENT  - hash matches, sign-off is still valid
    STALE    - hash differs, same mathlib_tag — spec changed since sign-off
    OK (mechanical port) - hash differs, different mathlib_tag — expected after Mathlib upgrade

Exit codes:
    0 - All sign-offs current (or no sign-offs)
    1 - At least one sign-off is stale
"""

import hashlib
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config, get_field


def compute_spec_hash(spec_dir, spec_files):
    """Compute SHA256 hash of spec files (sorted, combined)."""
    file_hashes = []
    for f in sorted(spec_files):
        path = os.path.join(spec_dir, f)
        if not os.path.isfile(path):
            print(f"  WARNING: Spec file missing: {f}", file=sys.stderr)
            return None
        with open(path, "rb") as fh:
            file_hashes.append(hashlib.sha256(fh.read()).hexdigest())
    combined = hashlib.sha256("".join(file_hashes).encode()).hexdigest()
    return f"sha256:{combined}"


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <entry.toml>", file=sys.stderr)
        sys.exit(2)

    entry_toml = sys.argv[1]
    if not os.path.isfile(entry_toml):
        # Try relative to project dir
        entry_toml = os.path.join(PROJECT_DIR, entry_toml)
    if not os.path.isfile(entry_toml):
        print(f"ERROR: Entry config not found: {sys.argv[1]}", file=sys.stderr)
        sys.exit(2)

    config = load_config(entry_toml)
    entry_id = get_field(config, "project.id")
    current_mathlib_tag = get_field(config, "lean.mathlib_tag")
    signoffs = config.get("signoffs", [])

    if not signoffs:
        print(f"No sign-offs found for {entry_id}.")
        sys.exit(0)

    spec_dir = os.path.join(PROJECT_DIR, "specs", entry_id)
    has_stale = False

    for i, so in enumerate(signoffs):
        if so.get("status") != "current":
            continue

        user = so.get("github_user", "unknown")
        issue = so.get("issue", "?")
        spec_files = so.get("spec_files", [])
        stored_hash = so.get("spec_hash", "")

        # Extract mathlib tag from spec_version (e.g., v1_mathlib-v4.27.0 -> v4.27.0)
        spec_version = so.get("spec_version", "")
        signoff_mathlib_tag = ""
        if "_mathlib-" in spec_version:
            signoff_mathlib_tag = spec_version.split("_mathlib-", 1)[1]

        current_hash = compute_spec_hash(spec_dir, spec_files)
        if current_hash is None:
            print(f"  [{i+1}] @{user} (#{issue}): UNKNOWN — spec file(s) missing")
            has_stale = True
            continue

        if current_hash == stored_hash:
            print(f"  [{i+1}] @{user} (#{issue}): CURRENT")
        elif signoff_mathlib_tag and signoff_mathlib_tag != current_mathlib_tag:
            print(f"  [{i+1}] @{user} (#{issue}): OK (mechanical port — mathlib {signoff_mathlib_tag} -> {current_mathlib_tag})")
        else:
            print(f"  [{i+1}] @{user} (#{issue}): STALE — spec files changed since sign-off")
            has_stale = True

    if has_stale:
        sys.exit(1)
    else:
        print(f"All sign-offs for {entry_id} are current.")
        sys.exit(0)


if __name__ == "__main__":
    main()
