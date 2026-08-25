#!/usr/bin/env python3
"""
Record a sign-off submitted through the issue form.

One interface, two stores. A sign-off on a registry entry is appended to
entries/<id>.toml; a sign-off on an overlaid upstream record is appended to
overlay/signoffs.toml. The reviewer answers the same questions either way, and
this script works out where the answer belongs.

The hashes that make a sign-off go stale are filled in here, from the record as
it stands right now — asking a reviewer to copy a sha256 out of a JSON file by
hand is asking for a sign-off bound to the wrong thing.

Reads environment variables:
    ISSUE_NUMBER  - GitHub issue number
    ISSUE_AUTHOR  - GitHub username of issue author
    ISSUE_BODY    - Full issue body text

GitHub form issues produce bodies with "### Header\n\nvalue" sections.

Exit codes:
    0 - Success
    1 - Validation error (unknown target, missing files or declarations)
    2 - Parse error (malformed issue body)
"""

import glob
import hashlib
import json
import os
import sys
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


def toml_escape(value):
    """Escape a string for a TOML basic string."""
    return str(value).replace("\\", "\\\\").replace('"', '\\"').replace("\n", " ").strip()


def find_overlay_record(source, upstream_id):
    """Locate a mirrored record by its upstream id.

    Matches the file the importer wrote (its name is a sanitized upstream id),
    then confirms by reading the record, so a near-miss id fails loudly instead
    of attaching a sign-off to a neighbouring record.
    """
    overlay_dir = os.path.join(PROJECT_DIR, "overlay", source)
    if not os.path.isdir(overlay_dir):
        return None, None
    for path in sorted(glob.glob(os.path.join(overlay_dir, "*.json"))):
        with open(path) as f:
            record = json.load(f)
        if str(record.get("upstream_id", "")) == upstream_id:
            return path, record
    return None, None


def record_overlay_signoff(source, upstream_id, declarations, author, issue_number,
                           verdict, comment):
    """Append a [[signoff]] block to overlay/signoffs.toml."""
    path, record = find_overlay_record(source, upstream_id)
    if record is None:
        print(f"ERROR: no {source} record with upstream id '{upstream_id}'. "
              f"Run scripts/import_upstream.py --source {source} first, or check the id.",
              file=sys.stderr)
        sys.exit(1)

    known = set(record.get("declarations") or [])
    if declarations != ["*"]:
        unknown = [d for d in declarations if d not in known]
        if unknown:
            print(f"ERROR: {source}:{upstream_id} has no declaration(s): "
                  f"{', '.join(unknown)}", file=sys.stderr)
            print(f"       It declares: {', '.join(sorted(known)) or '(none)'}",
                  file=sys.stderr)
            sys.exit(1)

    # Bind the sign-off to what is being reviewed right now. The Lean source hash
    # is what lets a LeanPool sign-off go stale when a theorem's type changes
    # under an unchanged name, so fetch it if the record has not got one yet.
    statement_hash = record.get("statement_hash", "")
    lean_source_hash = record.get("lean_source_hash", "")
    if not lean_source_hash and source == "leanpool":
        sys.path.insert(0, SCRIPT_DIR)
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location(
                "import_upstream", os.path.join(SCRIPT_DIR, "import_upstream.py"))
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            lean_source_hash = module.fetch_lean_source_hash(record)
        except Exception as exc:  # noqa: BLE001 - network is best-effort here
            print(f"  WARNING: could not hash the Lean source ({exc}); the sign-off "
                  f"will rest on the metadata hash alone", file=sys.stderr)

    declarations_toml = "[" + ", ".join(f'"{toml_escape(d)}"' for d in declarations) + "]"
    block = f'''
[[signoff]]
source = "{source}"
upstream_id = "{toml_escape(upstream_id)}"
declarations = {declarations_toml}
github_user = "{toml_escape(author)}"
date = "{date.today().isoformat()}"
issue = {issue_number}
verdict = "{verdict}"
statement_hash = "{statement_hash}"
lean_source_hash = "{lean_source_hash}"
comment = "{toml_escape(comment)}"
'''

    signoffs_path = os.path.join(PROJECT_DIR, "overlay", "signoffs.toml")
    with open(signoffs_path, "a") as f:
        f.write(block)

    print(f"Sign-off recorded for {source}:{upstream_id}")
    print(f"  User: {author}")
    print(f"  Declarations: {declarations}")
    print(f"  Verdict: {verdict}")
    print(f"  statement_hash: {statement_hash[:24]}...")
    print(f"  lean_source_hash: {(lean_source_hash or '(none)')[:24]}")
    print(f"  Issue: #{issue_number}")


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

    # Field labels: the current form, falling back to the pre-unification one so
    # an issue opened from the old template still processes.
    target_kind = sections.get("Target kind", "").strip()
    target_id = (sections.get("Target ID", "")
                 or sections.get("Entry ID", "")).strip()
    reviewed_raw = (sections.get("What you reviewed", "")
                    or sections.get("Spec files reviewed", "")).strip()
    literature_ref = sections.get("Literature reference", "").strip()
    verdict_raw = sections.get("Verdict", "").strip()
    comments = sections.get("Comments", "").strip()

    if not target_id:
        print("ERROR: Target ID is required", file=sys.stderr)
        sys.exit(2)
    if not reviewed_raw:
        print("ERROR: 'What you reviewed' is required", file=sys.stderr)
        sys.exit(2)
    if not verdict_raw:
        print("ERROR: Verdict is required", file=sys.stderr)
        sys.exit(2)

    verdict = verdict_raw.strip().lower()
    if verdict not in ("approved", "rejected"):
        print(f"ERROR: Verdict must be Approved or Rejected. Got: '{verdict_raw}'",
              file=sys.stderr)
        sys.exit(1)

    reviewed = [line.strip() for line in reviewed_raw.splitlines() if line.strip()]
    if not reviewed:
        print("ERROR: nothing listed under 'What you reviewed'", file=sys.stderr)
        sys.exit(1)

    comment_parts = [p for p in (literature_ref, comments) if p]
    comment = "; ".join(comment_parts)

    # --- Overlay record ---------------------------------------------------
    # "Overlay record: leanpool" -> leanpool
    if target_kind.lower().startswith("overlay record"):
        source = target_kind.split(":", 1)[1].strip().lower() if ":" in target_kind else ""
        if source not in ("palomar", "leanpool"):
            print(f"ERROR: unknown overlay source in target kind '{target_kind}'",
                  file=sys.stderr)
            sys.exit(1)
        record_overlay_signoff(source, target_id, reviewed, issue_author,
                               issue_number, verdict, comment)
        return

    # --- Registry entry ---------------------------------------------------
    entry_id = target_id
    spec_files = reviewed

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
verdict = "{verdict}"
spec_hash = "{spec_hash}"
comment = "{toml_escape(comment)}"
"""

    # Append to entry TOML
    with open(entry_toml, "a") as f:
        f.write(signoff_block)

    print(f"Sign-off recorded for registry entry {entry_id}:")
    print(f"  User: {issue_author}")
    print(f"  Files: {spec_files}")
    print(f"  Version: {spec_version}")
    print(f"  Verdict: {verdict}")
    print(f"  Hash: {spec_hash}")
    print(f"  Issue: #{issue_number}")


if __name__ == "__main__":
    main()
