#!/usr/bin/env python3
"""Build a review packet for a human sign-off.

Sign-off is the one thing VibeRegistry has that the automated registries do not,
so the cost of giving one should be low. This assembles everything a reviewer
needs into a single markdown file: for each registered declaration, the informal
statement (adopted from the project's blueprint or metadata by
fetch_blueprint_statements.py) sitting directly above the Lean statement the
registry actually verified, plus the machine checks that ran and the current
sign-off state.

The reviewer reads one file and answers one question per declaration: does the
Lean say what the mathematics says?

Usage:
    generate_signoff_packet.py entries/<id>.toml [--out PATH] [--stdout]
    generate_signoff_packet.py --all
    generate_signoff_packet.py --overlay leanpool:2-coloring-1-round

An overlaid upstream record gets the same packet, from what upstream publishes:
its declarations, the informal statement for each, what the upstream registry
itself checked, and the hashes the sign-off will be bound to. We hold no spec of
our own for those, so the packet links to the statement upstream rather than
quoting Lean we did not write.
"""

from __future__ import annotations

import argparse
import datetime as dt
import glob
import hashlib
import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config  # noqa: E402
from lean_decls import find_declaration  # noqa: E402

REPO_SLUG = "GasStationManager/VibeRegistry"

# Shared by both kinds of target: these are about the statement itself.
CHECKLIST_COMMON = """\
- [ ] The Lean statement says what the informal statement says — same hypotheses,
      same conclusion, same quantifier order.
- [ ] No hypothesis is stronger than it looks (watch for `Nonempty`, finiteness,
      measurability, and typeclass assumptions that quietly rule out the hard case).
- [ ] No conclusion is weaker than it looks (existentials that are trivially
      satisfiable, bounds that hold vacuously).
- [ ] Every definition the statement leans on means what its name claims.
"""

# Only meaningful where we hold the spec: an overlay record has no spec of ours.
CHECKLIST_REGISTRY = """\
- [ ] Definitions replicated from the impl do not shadow a Mathlib definition of
      the same name with different content (`scripts/check_mathlib_conflicts.py`
      reports suspected collisions).
- [ ] Universe variables and implicit binders match the impl.
- [ ] The statement is `sorry`-ed: the spec asserts, it does not prove.
"""

# Only meaningful upstream: there the proof and the statement live together.
CHECKLIST_OVERLAY = """\
- [ ] The statement upstream is the one the record names — same declaration, same
      module, at the revision this packet pins.
- [ ] Nothing in the surrounding upstream file weakens it (a local `axiom`, an
      opaque definition, a hypothesis bundled into a typeclass).
- [ ] What the upstream registry checked (above) is what you are relying on; this
      registry did not re-verify the proof.
"""


def spec_path(entry_id, spec_module):
    return os.path.join(PROJECT_DIR, "specs", entry_id, spec_module.replace(".", "/") + ".lean")


def file_hash(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def load_informal(entry_id):
    path = os.path.join(PROJECT_DIR, "informal", f"{entry_id}.json")
    if not os.path.isfile(path):
        return {}, None
    with open(path) as f:
        doc = json.load(f)
    return doc.get("statements", {}), doc.get("source", {})


def load_results(entry_id):
    path = os.path.join(PROJECT_DIR, "results", entry_id, "latest.json")
    if not os.path.isfile(path):
        return None
    with open(path) as f:
        return json.load(f)


def signoff_state(config, spec_file_rel):
    """Sign-offs covering a given spec file, newest first."""
    out = []
    for s in config.get("signoffs", []):
        if spec_file_rel in (s.get("spec_files") or []):
            out.append(s)
    return sorted(out, key=lambda s: str(s.get("date", "")), reverse=True)


def checks_line(results):
    if not results:
        return "no verification results yet"
    checks = results.get("checks")
    if isinstance(checks, dict):
        ran = [name for name, on in checks.items() if on]
        ran_str = ", ".join(ran) if ran else "none"
    else:
        ran_str = f"level {results.get('verification_level', '?')} (pre-checks-model result)"
    return f"{ran_str} — overall **{results.get('overall', 'unknown')}** at {results.get('timestamp', '?')}"


def verdict_for(results, name):
    if not results:
        return "—"
    for t in results.get("theorems", []):
        if t.get("name") == name:
            bits = []
            for key in ("comparator", "nanoda", "safe_verify", "lean4checker"):
                value = t.get(key)
                if value and value not in ("skip",):
                    bits.append(f"{key}: {value}")
            return ", ".join(bits) if bits else "not checked"
    return "—"


def build_packet(entry_path):
    config = load_config(entry_path)
    project = config["project"]
    entry_id = project["id"]
    informal, informal_source = load_informal(entry_id)
    results = load_results(entry_id)

    lines = []
    add = lines.append

    add(f"# Sign-off packet — {project.get('name', entry_id)}")
    add("")
    add(f"*Generated {dt.datetime.now(dt.timezone.utc).strftime('%Y-%m-%d %H:%M UTC')} "
        f"by `scripts/generate_signoff_packet.py`. Do not edit by hand.*")
    add("")
    add(f"- **Entry**: `{entry_id}`")
    add(f"- **Upstream**: {project.get('url', '?')} @ `{project.get('commit', '?')[:12]}`")
    add(f"- **Lean**: {config.get('lean', {}).get('toolchain', '?')}")
    add(f"- **Machine checks**: {checks_line(results)}")
    if informal_source and informal_source.get("files"):
        add(f"- **Informal statements adopted from**: "
            f"{', '.join(informal_source['files'])} "
            f"(`{informal_source.get('mode', 'auto')}`)")
    else:
        add("- **Informal statements**: none adopted yet — run "
            f"`python3 scripts/fetch_blueprint_statements.py {os.path.relpath(entry_path, PROJECT_DIR)}`")
    add("")
    add("## What you are attesting")
    add("")
    add("The machine checks below establish that the *implementation proves the "
        "spec*. They say nothing about whether the spec is the right statement. "
        "That is what your sign-off adds, and it is the only part no tool here "
        "can do for you.")
    add("")
    add("Sign-off is optional: an entry whose comparator check passes stands on "
        "its own as a verified Lean statement. A sign-off says a human read the "
        "statement and vouches for it meaning what it claims.")
    add("")
    add("### Checklist")
    add("")
    add(CHECKLIST_COMMON + CHECKLIST_REGISTRY)

    missing_informal = []

    for group in config.get("theorems", []):
        spec_module = group.get("spec_module", "")
        impl_module = group.get("impl_module", "")
        path = spec_path(entry_id, spec_module)
        rel_spec = spec_module.replace(".", "/") + ".lean"

        add("")
        add("---")
        add("")
        add(f"## `{spec_module}`")
        add("")
        add(f"- Spec file: [`specs/{entry_id}/{rel_spec}`](../specs/{entry_id}/{rel_spec})")
        add(f"- Implementation module: `{impl_module}`")
        if os.path.isfile(path):
            add(f"- Spec file sha256: `{file_hash(path)[:16]}…`")
        existing = signoff_state(config, rel_spec)
        if existing:
            for s in existing:
                add(f"- Existing sign-off: **{s.get('status', '?')}** by "
                    f"@{s.get('github_user', '?')} on {s.get('date', '?')}"
                    + (f" (issue #{s['issue']})" if s.get("issue") else ""))
        else:
            add("- Existing sign-off: **none**")

        if not os.path.isfile(path):
            add("")
            add(f"> **Spec file not found** at `{path}` — cannot render statements.")
            continue

        with open(path) as f:
            spec_text = f.read()

        for name in group.get("names", []):
            add("")
            add(f"### `{name}`")
            add("")
            add(f"*Machine checks: {verdict_for(results, name)}*")
            add("")

            record = informal.get(name)
            if record:
                title = f" — {record['title']}" if record.get("title") else ""
                add(f"**Informal statement** ({record.get('kind', 'statement')}{title}, "
                    f"from `{record.get('source_file', '?')}`):")
                add("")
                for para in record.get("statement", "").split("\n"):
                    add("> " + para if para.strip() else ">")
                add("")
            else:
                missing_informal.append(name)
                add("**Informal statement**: _none adopted_ — the reviewer must supply "
                    "the intended mathematics from the literature.")
                add("")

            decl = find_declaration(spec_text, name)
            if decl is None:
                add(f"> **Could not locate `{name}` in the spec file.** "
                    "Check that the name in the entry TOML matches the spec.")
                continue

            if decl.doc:
                add("**Spec docstring**:")
                add("")
                for para in decl.doc.split("\n"):
                    add("> " + para if para.strip() else ">")
                add("")

            add(f"**Lean statement** (`{rel_spec}` lines {decl.start_line}–{decl.end_line}):")
            add("")
            add("```lean")
            add(decl.source)
            add("```")

    add("")
    add("---")
    add("")
    add("## Submitting")
    add("")
    add(f"Open a [sign-off issue](https://github.com/{REPO_SLUG}/issues/new?template=spec-signoff.yml) "
        f"for `{entry_id}`, listing the spec files you reviewed. A GitHub Action "
        "records the sign-off in the entry TOML and marks it stale automatically "
        "if the spec files change afterwards.")
    if missing_informal:
        add("")
        add(f"> {len(missing_informal)} declaration(s) have no informal statement adopted: "
            f"{', '.join(f'`{n}`' for n in missing_informal)}.")

    return "\n".join(lines) + "\n"


def build_overlay_packet(source, upstream_id):
    """The same packet, for a record mirrored from an upstream registry."""
    index_path = os.path.join(PROJECT_DIR, "overlay", "index.json")
    if not os.path.isfile(index_path):
        raise SystemExit(
            "ERROR: no overlay/index.json. Run: python3 scripts/import_upstream.py --all"
        )
    with open(index_path) as f:
        index = json.load(f)
    record = next(
        (r for r in index.get("records", [])
         if r.get("source") == source and str(r.get("upstream_id")) == upstream_id),
        None,
    )
    if record is None:
        raise SystemExit(
            f"ERROR: no {source} record with upstream id '{upstream_id}'. "
            f"Run: python3 scripts/import_upstream.py --source {source}"
        )

    checks = record.get("upstream_checks", {})
    lines = []
    add = lines.append

    add(f"# Sign-off packet — {record.get('title', upstream_id)}")
    add("")
    add(f"*Generated {dt.datetime.now(dt.timezone.utc).strftime('%Y-%m-%d %H:%M UTC')} "
        f"by `scripts/generate_signoff_packet.py`. Do not edit by hand.*")
    add("")
    add(f"- **Overlay record**: `{source}:{upstream_id}`")
    add(f"- **Upstream**: {record.get('upstream_url', '')}")
    add(f"- **Source repository**: {record.get('repository', '(none published)')}"
        + (f" @ `{record['commit'][:12]}`" if record.get("commit") else ""))
    if record.get("snapshot_commit"):
        add(f"- **Read at snapshot**: `{record['snapshot_commit'][:12]}`")
    add(f"- **Upstream checked**: comparator={checks.get('comparator', False)}, "
        f"kernels={'+'.join(checks.get('kernels', [])) or 'unknown'}, "
        f"llm_review={checks.get('llm_review', False)}, "
        f"human_signoff={checks.get('human_signoff', False)}")
    existing = record.get("signoffs", [])
    if existing:
        for signoff in existing:
            add(f"- **Existing sign-off**: {signoff.get('verdict', '?')} / "
                f"{signoff.get('status', '?')} by @{signoff.get('github_user', '?')} "
                f"covering {', '.join(signoff.get('declarations', []))}")
    else:
        add("- **Existing sign-off**: **none**")
    add("")
    add("## What you are attesting")
    add("")
    add("This registry did not verify this result — the upstream registry did, "
        "with the checks listed above. What it did not do is have a person read "
        "the statement and vouch for what it says. That is what your sign-off "
        "adds, and it is the whole reason this record is mirrored here.")
    add("")
    add("### Checklist")
    add("")
    add(CHECKLIST_COMMON + CHECKLIST_OVERLAY)

    if record.get("abstract"):
        add("")
        add("## Abstract (upstream)")
        add("")
        for para in record["abstract"].split("\n"):
            add("> " + para if para.strip() else ">")

    informal = record.get("informal", {}) or {}
    for name in record.get("declarations", []):
        add("")
        add("---")
        add("")
        add(f"## `{name}`")
        add("")
        text = informal.get(name)
        if text:
            add("**Informal statement** (upstream):")
            add("")
            for para in str(text).split("\n"):
                add("> " + para if para.strip() else ">")
        else:
            add("**Informal statement**: _none published per declaration_ — "
                "read the abstract above and the upstream source.")
        add("")
        add(f"**Lean statement**: not held here. Read it in the upstream source: "
            f"{record.get('upstream_url', '')}")

    add("")
    add("---")
    add("")
    add("## Submitting")
    add("")
    add(f"Open a [sign-off issue](https://github.com/{REPO_SLUG}/issues/new?template=spec-signoff.yml), "
        f"choose **Overlay record: {source}**, enter `{upstream_id}` as the Target ID, "
        f"and list the declarations you reviewed (or `*` for all of them). The "
        f"Action records it in `overlay/signoffs.toml` and binds it to the hashes "
        f"below, so it goes stale by itself when upstream moves.")
    add("")
    add(f"- `statement_hash`: `{record.get('statement_hash', '(none)')}`")
    add(f"- `lean_source_hash`: `{record.get('lean_source_hash', '(not fetched yet)')}`")

    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("entry", nargs="?", help="entries/<id>.toml")
    ap.add_argument("--overlay", metavar="SOURCE:ID",
                    help="packet for a mirrored record, e.g. leanpool:2-coloring-1-round")
    ap.add_argument("--all", action="store_true", help="generate for every entry")
    ap.add_argument("--out", help="output path (single entry only)")
    ap.add_argument("--stdout", action="store_true")
    args = ap.parse_args()

    if args.overlay:
        if ":" not in args.overlay:
            ap.error("--overlay takes SOURCE:ID, e.g. leanpool:2-coloring-1-round")
        source, upstream_id = args.overlay.split(":", 1)
        text = build_overlay_packet(source.strip(), upstream_id.strip())
        if args.stdout:
            print(text, end="")
        else:
            out = args.out or os.path.join(PROJECT_DIR, "signoff_packets",
                                           f"{source.strip()}-{upstream_id.strip()}.md")
            os.makedirs(os.path.dirname(out), exist_ok=True)
            with open(out, "w") as f:
                f.write(text)
            print(f"Wrote {out}")
        return

    if not args.entry and not args.all:
        ap.error("give an entry TOML, --overlay SOURCE:ID, or --all")

    entries = (
        sorted(glob.glob(os.path.join(PROJECT_DIR, "entries", "*.toml")))
        if args.all
        else [args.entry]
    )

    for entry_path in entries:
        text = build_packet(entry_path)
        if args.stdout:
            print(text, end="")
            continue
        entry_id = load_config(entry_path)["project"]["id"]
        out = args.out or os.path.join(PROJECT_DIR, "signoff_packets", f"{entry_id}.md")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out, "w") as f:
            f.write(text)
        print(f"Wrote {out}")


if __name__ == "__main__":
    main()
