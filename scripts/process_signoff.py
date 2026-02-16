#!/usr/bin/env python3
"""
Process a GitHub sign-off issue and append a [[signoffs]] block to the entry TOML.

Reads environment variables:
    ISSUE_NUMBER  - GitHub issue number
    ISSUE_AUTHOR  - GitHub username of issue author
    ISSUE_BODY    - Full issue body text

GitHub form issues produce bodies with "### Header\n\nvalue" sections.

Exit codes:
    0 - Success
    1 - Validation error (bad entry, missing files, rejected verdict)
    2 - Parse error (malformed issue body)
"""

import os
import sys
import hashlib
from datetime import date

# Add lib/ to path for parse_toml
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config, get_field


def parse_issue_body(body):
    """Parse GitHub form issue body into a dict of header -> value."""
    sections = {}
    parts = body.split("### ")
    for part in parts[1:]:  # skip preamble before first ###
        lines = part.strip().split("\n", 1)
        header = lines[0].strip()
        value = lines[1].strip() if len(lines) > 1 else ""
        # GitHub forms sometimes wrap values in blank lines
        value = value.strip()
        # Remove "_No response_" placeholder
        if value == "_No response_":
            value = ""
        sections[header] = value
    return sections


def compute_spec_hash(spec_dir, spec_files):
    """Compute SHA256 hash of spec files (sorted, combined)."""
    file_hashes = []
    for f in sorted(spec_files):
        path = os.path.join(spec_dir, f)
        with open(path, "rb") as fh:
            file_hashes.append(hashlib.sha256(fh.read()).hexdigest())
    combined = hashlib.sha256("".join(file_hashes).encode()).hexdigest()
    return f"sha256:{combined}"


def main():
    # Read env vars
    issue_number = os.environ.get("ISSUE_NUMBER", "")
    issue_author = os.environ.get("ISSUE_AUTHOR", "")
    issue_body = os.environ.get("ISSUE_BODY", "")

    if not issue_number or not issue_author or not issue_body:
        print("ERROR: ISSUE_NUMBER, ISSUE_AUTHOR, and ISSUE_BODY must be set", file=sys.stderr)
        sys.exit(2)

    # Parse issue body
    sections = parse_issue_body(issue_body)
    if not sections:
        print("ERROR: Could not parse issue body — no ### sections found", file=sys.stderr)
        sys.exit(2)

    entry_id = sections.get("Entry ID", "").strip()
    spec_files_raw = sections.get("Spec files reviewed", "").strip()
    literature_ref = sections.get("Literature reference", "").strip()
    verdict = sections.get("Verdict", "").strip()
    comments = sections.get("Comments", "").strip()

    # Validate required fields
    if not entry_id:
        print("ERROR: Entry ID is required", file=sys.stderr)
        sys.exit(2)

    if not spec_files_raw:
        print("ERROR: Spec files reviewed is required", file=sys.stderr)
        sys.exit(2)

    if not verdict:
        print("ERROR: Verdict is required", file=sys.stderr)
        sys.exit(2)

    # Validate verdict
    if verdict != "Approved":
        print(f"ERROR: Only 'Approved' verdicts are recorded. Got: '{verdict}'", file=sys.stderr)
        sys.exit(1)

    # Parse spec files list
    spec_files = [line.strip() for line in spec_files_raw.splitlines() if line.strip()]
    if not spec_files:
        print("ERROR: No spec files listed", file=sys.stderr)
        sys.exit(1)

    # Validate entry exists
    entry_toml = os.path.join(PROJECT_DIR, "entries", f"{entry_id}.toml")
    if not os.path.isfile(entry_toml):
        print(f"ERROR: Entry config not found: entries/{entry_id}.toml", file=sys.stderr)
        sys.exit(1)

    # Load entry config
    config = load_config(entry_toml)
    mathlib_tag = get_field(config, "lean.mathlib_tag")
    if not mathlib_tag:
        print(f"ERROR: lean.mathlib_tag not found in {entry_toml}", file=sys.stderr)
        sys.exit(1)

    # Validate spec files exist
    spec_dir = os.path.join(PROJECT_DIR, "specs", entry_id)
    for f in spec_files:
        full_path = os.path.join(spec_dir, f)
        if not os.path.isfile(full_path):
            print(f"ERROR: Spec file not found: specs/{entry_id}/{f}", file=sys.stderr)
            sys.exit(1)

    # Compute spec hash
    spec_hash = compute_spec_hash(spec_dir, spec_files)

    # Determine spec version
    spec_version = f"v1_mathlib-{mathlib_tag}"

    # Build comment string (combine literature ref + comments)
    comment_parts = []
    if literature_ref:
        comment_parts.append(literature_ref)
    if comments:
        comment_parts.append(comments)
    comment = "; ".join(comment_parts) if comment_parts else ""

    # Format spec_files as TOML array
    spec_files_toml = "[" + ", ".join(f'"{f}"' for f in spec_files) + "]"

    # Build TOML block
    today = date.today().isoformat()
    signoff_block = f"""
[[signoffs]]
github_user = "{issue_author}"
spec_files = {spec_files_toml}
spec_version = "{spec_version}"
date = "{today}"
issue = {issue_number}
status = "current"
spec_hash = "{spec_hash}"
comment = "{comment}"
"""

    # Append to entry TOML
    with open(entry_toml, "a") as f:
        f.write(signoff_block)

    print(f"Sign-off recorded for {entry_id}:")
    print(f"  User: {issue_author}")
    print(f"  Files: {spec_files}")
    print(f"  Version: {spec_version}")
    print(f"  Hash: {spec_hash}")
    print(f"  Issue: #{issue_number}")


if __name__ == "__main__":
    main()
