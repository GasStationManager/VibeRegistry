#!/usr/bin/env python3
"""Build a searchable index of every Lean statement the registry knows about.

Sign-off is optional. A statement whose comparator check passed stands on its
own: the proof was re-checked from an independent export against exactly that
statement. So the registry is useful as a *search surface* over verified Lean
statements — signed-off or not — as long as each record carries, plainly, what
was checked and by whom.

Sources:
  entries/     our own entries: the human-vetted spec statement, its checks,
               and its sign-offs
  overlay/     mirrored upstream registries (Palomar, LeanPool), which carry the
               upstream declaration names and informal statements but no spec
               source of ours

Every record is annotated with any Mathlib name collision found by
check_mathlib_conflicts.py, because a statement that redefines a Mathlib name
does not mean what a searcher will read it to mean.

Output:
    index/statements.json   the records
    index/meta.json         counts and provenance
    index/search.html       dependency-free static search page over the above

Usage:
    build_search_index.py [--no-html] [--names-file PATH]
"""

from __future__ import annotations

import argparse
import datetime as dt
import glob
import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_DIR = os.path.dirname(SCRIPT_DIR)
sys.path.insert(0, os.path.join(SCRIPT_DIR, "lib"))

from parse_toml import load_config  # noqa: E402
from lean_decls import find_declaration  # noqa: E402

INDEX_DIR = os.path.join(PROJECT_DIR, "index")

sys.path.insert(0, SCRIPT_DIR)


def load_json(path, default=None):
    if not os.path.isfile(path):
        return default
    with open(path) as f:
        return json.load(f)


def mathlib_conflicts_by_file():
    """Run the collision check if the name list is present; return file -> [conflict]."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "check_mathlib_conflicts", os.path.join(SCRIPT_DIR, "check_mathlib_conflicts.py")
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    mathlib = module.load_mathlib_names(module.DEFAULT_NAMES)
    if mathlib is None:
        print("  NOTE: no Mathlib name list; records will not carry collision data. "
              "Run scripts/fetch_mathlib_names.py to enable it.", file=sys.stderr)
        return None

    by_name = {}
    for entry_path in sorted(glob.glob(os.path.join(PROJECT_DIR, "entries", "*.toml"))):
        report = module.check_entry(entry_path, mathlib)
        for conflict in report["conflicts"]:
            by_name.setdefault(conflict["name"], []).append(conflict)
    return by_name


def checks_for(results, name):
    if not results:
        return {}
    for theorem in results.get("theorems", []):
        if theorem.get("name") == name:
            return {
                key: theorem[key]
                for key in ("comparator", "nanoda", "safe_verify", "lean4checker")
                if theorem.get(key) and theorem[key] != "skip"
            }
    return {}


def signoffs_for(config, spec_module):
    rel = spec_module.replace(".", "/") + ".lean"
    out = []
    for s in config.get("signoffs", []):
        if rel in (s.get("spec_files") or []):
            out.append({
                "github_user": s.get("github_user", ""),
                "date": s.get("date", ""),
                "status": s.get("status", ""),
                "issue": s.get("issue"),
            })
    return out


def build_registry_records(conflicts_by_name):
    records = []
    registry = load_config(os.path.join(PROJECT_DIR, "registry.toml"))
    for item in registry.get("entries", []):
        entry_id = item["id"]
        config = load_config(os.path.join(PROJECT_DIR, item["config"]))
        project = config["project"]
        results = load_json(os.path.join(PROJECT_DIR, "results", entry_id, "latest.json"))
        informal_doc = load_json(os.path.join(PROJECT_DIR, "informal", f"{entry_id}.json"), {})
        informal = (informal_doc or {}).get("statements", {})
        commit = project.get("commit", "")
        repo = project.get("url", "")

        for group in config.get("theorems", []):
            spec_module = group.get("spec_module", "")
            impl_module = group.get("impl_module", "")
            rel_spec = spec_module.replace(".", "/") + ".lean"
            spec_path = os.path.join(PROJECT_DIR, "specs", entry_id, rel_spec)
            spec_text = ""
            if os.path.isfile(spec_path):
                with open(spec_path, errors="replace") as f:
                    spec_text = f.read()

            for name in group.get("names", []):
                decl = find_declaration(spec_text, name) if spec_text else None
                record_informal = informal.get(name, {})
                records.append({
                    "id": f"{entry_id}:{name}",
                    "name": name,
                    "kind": decl.kind if decl else "",
                    "origin": "registry",
                    "entry": entry_id,
                    "entry_name": project.get("name", entry_id),
                    "repository": repo,
                    "commit": commit,
                    "lean": config.get("lean", {}).get("toolchain", ""),
                    "spec_file": f"specs/{entry_id}/{rel_spec}",
                    "impl_module": impl_module,
                    "lines": [decl.start_line, decl.end_line] if decl else None,
                    "statement": decl.source if decl else "",
                    "doc": decl.doc if decl else "",
                    "informal": record_informal.get("statement", ""),
                    "informal_source": record_informal.get("source_file", ""),
                    "checks": checks_for(results, name),
                    "signoffs": signoffs_for(config, spec_module),
                    "mathlib_conflicts": (conflicts_by_name or {}).get(name, []),
                    "url": f"{repo}/blob/{commit}" if repo and commit else repo,
                })
    return records


def build_overlay_records():
    records = []
    index = load_json(os.path.join(PROJECT_DIR, "overlay", "index.json"))
    if not index:
        return records
    for entry in index.get("records", []):
        source = entry.get("source", "")
        repo = entry.get("repository", "")
        commit = entry.get("commit", "")
        signoffs = entry.get("signoffs", [])
        declarations = entry.get("declarations") or []
        if not declarations:
            declarations = [""]
        for name in declarations:
            records.append({
                "id": f"{source}:{entry.get('upstream_id', '')}:{name}",
                "name": name,
                "kind": "",
                "origin": f"overlay:{source}",
                "entry": entry.get("upstream_id", ""),
                "entry_name": entry.get("title", ""),
                "repository": repo,
                "commit": commit,
                "lean": "",
                "spec_file": "",
                "impl_module": entry.get("entry_module", ""),
                "lines": None,
                # We hold no spec of our own for an overlaid entry: the statement
                # lives upstream, and the record links to it.
                "statement": "",
                "doc": entry.get("abstract", ""),
                "informal": (entry.get("informal") or {}).get(name, ""),
                "informal_source": f"{source} metadata",
                "checks": {"upstream": source},
                "upstream_checks": entry.get("upstream_checks", {}),
                "signoffs": signoffs,
                "mathlib_conflicts": [],
                "url": entry.get("upstream_url", "") or repo,
                "classification": entry.get("classification", {}),
            })
    return records


SEARCH_HTML = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>VibeRegistry — statement search</title>
<style>
  :root {
    color-scheme: light dark;
    --bg: #ffffff; --fg: #16181d; --muted: #5c6370; --line: #e2e5ea;
    --card: #f7f8fa; --accent: #2f5fd0; --warn: #a1421f; --ok: #1d6f42;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg: #14161a; --fg: #e6e8ec; --muted: #9aa1ac; --line: #2a2e36;
      --card: #1b1e24; --accent: #7aa2f7; --warn: #e0875f; --ok: #7bc496;
    }
  }
  * { box-sizing: border-box; }
  body { margin: 0; background: var(--bg); color: var(--fg); font: 15px/1.5
    ui-sans-serif, system-ui, -apple-system, "Segoe UI", sans-serif; }
  header { padding: 1.5rem 1rem 0.5rem; max-width: 60rem; margin: 0 auto; }
  h1 { font-size: 1.25rem; margin: 0 0 0.25rem; }
  .sub { color: var(--muted); font-size: 0.9rem; margin: 0 0 1rem; }
  main { max-width: 60rem; margin: 0 auto; padding: 0 1rem 4rem; }
  input[type=search] { width: 100%; padding: 0.6rem 0.7rem; font-size: 1rem;
    border: 1px solid var(--line); border-radius: 6px; background: var(--bg); color: var(--fg); }
  .filters { display: flex; flex-wrap: wrap; gap: 0.75rem; margin: 0.75rem 0 1rem;
    font-size: 0.85rem; color: var(--muted); align-items: center; }
  .filters label { display: inline-flex; gap: 0.3rem; align-items: center; }
  .count { margin: 0.5rem 0 1rem; color: var(--muted); font-size: 0.85rem; }
  .card { border: 1px solid var(--line); background: var(--card); border-radius: 8px;
    padding: 0.9rem 1rem; margin-bottom: 0.85rem; }
  .name { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 0.95rem;
    font-weight: 600; word-break: break-all; }
  .meta { color: var(--muted); font-size: 0.8rem; margin-top: 0.2rem; }
  .tags { margin-top: 0.5rem; display: flex; flex-wrap: wrap; gap: 0.35rem; }
  .tag { font-size: 0.72rem; padding: 0.1rem 0.45rem; border-radius: 999px;
    border: 1px solid var(--line); color: var(--muted); }
  .tag.ok { color: var(--ok); border-color: var(--ok); }
  .tag.warn { color: var(--warn); border-color: var(--warn); }
  .informal { margin-top: 0.6rem; font-size: 0.9rem; }
  pre { overflow-x: auto; background: var(--bg); border: 1px solid var(--line);
    border-radius: 6px; padding: 0.6rem; font-size: 0.8rem; margin: 0.6rem 0 0; }
  a { color: var(--accent); }
  details summary { cursor: pointer; color: var(--muted); font-size: 0.85rem; margin-top: 0.5rem; }
</style>
</head>
<body>
<header>
  <h1>VibeRegistry — statement search</h1>
  <p class="sub">Lean statements this registry has checked, plus mirrored entries
  from upstream registries. A machine check says the proof establishes the
  statement; a sign-off says a human read the statement.</p>
</header>
<main>
  <input type="search" id="q" placeholder="Search names, statements, informal text…" autofocus>
  <div class="filters">
    <label><input type="checkbox" id="f-registry" checked> registry</label>
    <label><input type="checkbox" id="f-overlay" checked> overlay</label>
    <label><input type="checkbox" id="f-signed"> signed off only</label>
    <label><input type="checkbox" id="f-informal"> has informal statement</label>
    <span id="gen"></span>
  </div>
  <div class="count" id="count">Loading…</div>
  <div id="results"></div>
</main>
<script>
const state = { records: [], meta: null };

function esc(s) {
  return String(s == null ? "" : s).replace(/[&<>"]/g, c => (
    { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]
  ));
}

function tagsFor(r) {
  const tags = [];
  const current = (r.signoffs || []).filter(s => s.status === "current");
  if (current.length) {
    tags.push(`<span class="tag ok">signed off by @${esc(current[0].github_user)}</span>`);
  } else if ((r.signoffs || []).length) {
    tags.push('<span class="tag warn">sign-off stale</span>');
  } else {
    tags.push('<span class="tag">no sign-off</span>');
  }
  for (const [k, v] of Object.entries(r.checks || {})) {
    const cls = v === "pass" ? "ok" : v === "fail" ? "warn" : "";
    tags.push(`<span class="tag ${cls}">${esc(k)}: ${esc(v)}</span>`);
  }
  if (r.upstream_checks && r.upstream_checks.kernels) {
    tags.push(`<span class="tag">upstream kernels: ${esc(r.upstream_checks.kernels.join("+"))}</span>`);
  }
  for (const c of r.mathlib_conflicts || []) {
    tags.push(`<span class="tag warn">shadows Mathlib ${esc(c.mathlib_kind)}</span>`);
  }
  return tags.join(" ");
}

function render(list) {
  const results = document.getElementById("results");
  document.getElementById("count").textContent =
    `${list.length} of ${state.records.length} statements`;
  results.innerHTML = list.slice(0, 300).map(r => `
    <div class="card">
      <div class="name">${esc(r.name || "(entry)")}</div>
      <div class="meta">
        ${esc(r.origin)} · ${esc(r.entry_name || r.entry)}
        ${r.url ? ` · <a href="${esc(r.url)}" rel="noreferrer noopener">source</a>` : ""}
        ${r.lean ? ` · ${esc(r.lean)}` : ""}
      </div>
      <div class="tags">${tagsFor(r)}</div>
      ${r.informal ? `<div class="informal">${esc(r.informal)}</div>` : ""}
      ${r.statement ? `<details><summary>Lean statement</summary><pre>${esc(r.statement)}</pre></details>` : ""}
    </div>`).join("");
  if (list.length > 300) {
    results.innerHTML += `<div class="count">Showing the first 300 matches — narrow the query.</div>`;
  }
}

function apply() {
  const q = document.getElementById("q").value.toLowerCase().trim();
  const wantRegistry = document.getElementById("f-registry").checked;
  const wantOverlay = document.getElementById("f-overlay").checked;
  const signedOnly = document.getElementById("f-signed").checked;
  const informalOnly = document.getElementById("f-informal").checked;
  const terms = q.split(/\\s+/).filter(Boolean);

  render(state.records.filter(r => {
    const isRegistry = r.origin === "registry";
    if (isRegistry && !wantRegistry) return false;
    if (!isRegistry && !wantOverlay) return false;
    if (signedOnly && !(r.signoffs || []).some(s => s.status === "current")) return false;
    if (informalOnly && !r.informal) return false;
    if (!terms.length) return true;
    const hay = [r.name, r.entry, r.entry_name, r.informal, r.statement, r.doc]
      .join(" ").toLowerCase();
    return terms.every(t => hay.includes(t));
  }));
}

fetch("statements.json")
  .then(r => r.json())
  .then(data => {
    state.records = data.records || data;
    state.meta = data.meta || null;
    if (state.meta && state.meta.generated_at) {
      document.getElementById("gen").textContent = "generated " + state.meta.generated_at;
    }
    for (const id of ["f-registry", "f-overlay", "f-signed", "f-informal"]) {
      document.getElementById(id).addEventListener("change", apply);
    }
    document.getElementById("q").addEventListener("input", apply);
    apply();
  })
  .catch(err => {
    document.getElementById("count").textContent =
      "Could not load statements.json — run scripts/build_search_index.py. " + err;
  });
</script>
</body>
</html>
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-html", action="store_true")
    args = ap.parse_args()

    print("Checking Mathlib name collisions...")
    conflicts_by_name = mathlib_conflicts_by_file()

    registry_records = build_registry_records(conflicts_by_name)
    overlay_records = build_overlay_records()
    records = registry_records + overlay_records

    meta = {
        "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "counts": {
            "total": len(records),
            "registry": len(registry_records),
            "overlay": len(overlay_records),
            "with_informal": sum(1 for r in records if r.get("informal")),
            "signed_off": sum(
                1 for r in records
                if any(s.get("status") == "current" for s in (r.get("signoffs") or []))
            ),
            "mathlib_conflicts": sum(1 for r in records if r.get("mathlib_conflicts")),
        },
        "mathlib_names": load_json(
            os.path.join(PROJECT_DIR, "data", "mathlib-names.meta.json"), {}
        ),
    }

    os.makedirs(INDEX_DIR, exist_ok=True)
    with open(os.path.join(INDEX_DIR, "statements.json"), "w") as f:
        json.dump({"meta": meta, "records": records}, f, indent=1, ensure_ascii=False)
        f.write("\n")
    with open(os.path.join(INDEX_DIR, "meta.json"), "w") as f:
        json.dump(meta, f, indent=2, ensure_ascii=False)
        f.write("\n")
    if not args.no_html:
        with open(os.path.join(INDEX_DIR, "search.html"), "w") as f:
            f.write(SEARCH_HTML)

    print(f"Wrote index/statements.json: {meta['counts']['total']} statements "
          f"({meta['counts']['registry']} registry, {meta['counts']['overlay']} overlay)")
    print(f"  with informal statement: {meta['counts']['with_informal']}")
    print(f"  with a current sign-off: {meta['counts']['signed_off']}")
    print(f"  shadowing a Mathlib name: {meta['counts']['mathlib_conflicts']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
