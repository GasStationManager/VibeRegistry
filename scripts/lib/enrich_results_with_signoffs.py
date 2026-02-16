#!/usr/bin/env python3
"""
Enrich verification results JSON with sign-off data from the entry TOML.

Usage:
    python3 enrich_results_with_signoffs.py <results.json> <entry.toml>

Modifies results.json in-place, adding:
  - Per-theorem "signoffs" array
  - Top-level "signoff_summary" object
"""

import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPT_DIR)

from parse_toml import load_config


def spec_module_to_path(spec_module):
    """Convert a spec module name to a file path relative to specs/<entry>/.

    e.g. Registry.StatLearning.Dudley -> Registry/StatLearning/Dudley.lean
    """
    return spec_module.replace(".", "/") + ".lean"


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <results.json> <entry.toml>", file=sys.stderr)
        sys.exit(1)

    results_path = sys.argv[1]
    entry_toml_path = sys.argv[2]

    with open(results_path) as f:
        results = json.load(f)

    config = load_config(entry_toml_path)
    signoffs = config.get("signoffs", [])

    if not signoffs:
        # No signoffs — add empty summary and exit
        results["signoff_summary"] = {"total": 0, "current": 0, "stale": 0}
        with open(results_path, "w") as f:
            json.dump(results, f, indent=2)
            f.write("\n")
        return

    # Build mapping: spec file path -> list of signoffs covering that file
    file_to_signoffs = {}
    for so in signoffs:
        for spec_file in so.get("spec_files", []):
            file_to_signoffs.setdefault(spec_file, []).append(so)

    # Enrich each theorem with matching signoffs
    total_signoffs = 0
    current_count = 0
    stale_count = 0
    seen_signoff_ids = set()

    for theorem in results.get("theorems", []):
        spec_module = theorem.get("spec_module", "")
        spec_path = spec_module_to_path(spec_module)

        matching = file_to_signoffs.get(spec_path, [])
        theorem["signoffs"] = [
            {
                "github_user": so["github_user"],
                "date": so["date"],
                "issue": so["issue"],
                "status": so["status"],
            }
            for so in matching
        ]

        # Count unique signoffs for summary
        for so in matching:
            so_id = (so["github_user"], so["date"], so["issue"])
            if so_id not in seen_signoff_ids:
                seen_signoff_ids.add(so_id)
                total_signoffs += 1
                if so.get("status") == "current":
                    current_count += 1
                else:
                    stale_count += 1

    results["signoff_summary"] = {
        "total": total_signoffs,
        "current": current_count,
        "stale": stale_count,
    }

    with open(results_path, "w") as f:
        json.dump(results, f, indent=2)
        f.write("\n")

    print(f"Enriched results with {total_signoffs} sign-off(s) ({current_count} current, {stale_count} stale)")


if __name__ == "__main__":
    main()
