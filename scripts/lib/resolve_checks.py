#!/usr/bin/env python3
"""Resolve which checks run for an entry.

VibeRegistry's checker model is *comparator-primary*: comparator (with an
optional second kernel, nanoda) is the check that establishes an entry, and
SafeVerify / lean4checker are optional extras.

Precedence, lowest to highest:
  1. built-in defaults (comparator on, everything else off)
  2. the entry's [checks] table
  3. the legacy --level alias (see below)
  4. explicit --with-X / --no-X / --checks flags

Legacy aliases, kept so old CI invocations keep working:
  --level 1  -> lean4checker + safe_verify, no comparator
  --level 2  -> comparator + lean4checker + safe_verify
  --skip-level-1 clears lean4checker + safe_verify

Usage:
    resolve_checks.py <entry.toml> [--level N] [--skip-level-1]
                      [--checks a,b,c] [--with-X] [--no-X] [--format sh|json]

With --format sh (the default) it prints shell assignments to eval:

    CHECK_COMPARATOR=1
    CHECK_NANODA=0
    CHECK_SAFE_VERIFY=0
    CHECK_LEAN4CHECKER=0
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from parse_toml import load_config

CHECKS = ("comparator", "nanoda", "definitions", "safe_verify", "lean4checker")

# Comparator is the primary checker. SafeVerify and lean4checker are optional:
# comparator subsumes what they establish (kernel-level re-verification of the
# proof, statement/proof separation, axiom allowlisting) and does it against an
# independently exported proof term.
DEFAULTS = {
    "comparator": True,
    "nanoda": False,
    # Definition groups (spec `def`s rather than theorems) used to be covered
    # only by SafeVerify. With SafeVerify optional they would go unchecked, so
    # comparator can compare them too via its definition_names mechanism.
    # Opt-in per entry: it is a stricter check than SafeVerify's.
    "definitions": False,
    "safe_verify": False,
    "lean4checker": False,
}

LEVEL_ALIASES = {
    1: {"comparator": False, "lean4checker": True, "safe_verify": True},
    2: {"comparator": True, "lean4checker": True, "safe_verify": True},
}


def _as_bool(value, field):
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        low = value.strip().lower()
        if low in ("true", "yes", "1", "on"):
            return True
        if low in ("false", "no", "0", "off"):
            return False
    raise SystemExit(f"ERROR: [checks].{field} must be a boolean, got {value!r}")


def resolve(config, level=None, skip_level_1=False, checks_list=None, overrides=None):
    """Return a dict check-name -> bool."""
    plan = dict(DEFAULTS)

    entry_checks = config.get("checks") or {}
    if not isinstance(entry_checks, dict):
        raise SystemExit("ERROR: [checks] must be a table")
    for name, value in entry_checks.items():
        if name not in CHECKS:
            raise SystemExit(
                f"ERROR: unknown check '{name}' in [checks]; known checks: {', '.join(CHECKS)}"
            )
        plan[name] = _as_bool(value, name)

    if level is not None:
        if level not in LEVEL_ALIASES:
            raise SystemExit(f"ERROR: unknown --level {level} (use 1 or 2)")
        plan.update(LEVEL_ALIASES[level])
        # nanoda/definitions stay as configured: they are comparator options,
        # not levels.
        if not plan["comparator"]:
            plan["nanoda"] = False
            plan["definitions"] = False

    if skip_level_1:
        plan["lean4checker"] = False
        plan["safe_verify"] = False

    if checks_list:
        requested = [c.strip() for c in checks_list.split(",") if c.strip()]
        for name in requested:
            if name not in CHECKS:
                raise SystemExit(
                    f"ERROR: unknown check '{name}' in --checks; known checks: {', '.join(CHECKS)}"
                )
        plan = {name: name in requested for name in CHECKS}

    for name, value in (overrides or {}).items():
        plan[name] = value

    for rider in ("nanoda", "definitions"):
        if plan[rider] and not plan["comparator"]:
            print(
                f"WARNING: {rider} is a comparator option; enabling comparator too.",
                file=sys.stderr,
            )
            plan["comparator"] = True

    if not any(plan.values()):
        raise SystemExit("ERROR: no checks selected — nothing to verify")

    return plan


def legacy_level(plan):
    """Map a plan back onto the old level number, for result-file compatibility."""
    if plan["comparator"]:
        return 2
    return 1


def main():
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("config")
    ap.add_argument("--level", type=int, default=None)
    ap.add_argument("--skip-level-1", action="store_true")
    ap.add_argument("--checks", default=None)
    ap.add_argument("--format", choices=("sh", "json"), default="sh")
    for name in CHECKS:
        flag = name.replace("_", "-")
        ap.add_argument(f"--with-{flag}", dest=f"with_{name}", action="store_true")
        ap.add_argument(f"--no-{flag}", dest=f"no_{name}", action="store_true")
    args = ap.parse_args()

    overrides = {}
    for name in CHECKS:
        if getattr(args, f"with_{name}"):
            overrides[name] = True
        if getattr(args, f"no_{name}"):
            if name in overrides:
                raise SystemExit(f"ERROR: both --with-{name} and --no-{name} given")
            overrides[name] = False

    config = load_config(args.config)
    plan = resolve(
        config,
        level=args.level,
        skip_level_1=args.skip_level_1,
        checks_list=args.checks,
        overrides=overrides,
    )

    if args.format == "json":
        print(json.dumps(plan, indent=2))
        return

    for name in CHECKS:
        print(f"CHECK_{name.upper()}={1 if plan[name] else 0}")
    print(f"LEGACY_LEVEL={legacy_level(plan)}")


if __name__ == "__main__":
    main()
