# Statement search

Because sign-off is optional, the registry is also useful as a plain search
surface over Lean statements that something has actually checked — ours and the
upstream registries we mirror.

```bash
python3 scripts/fetch_mathlib_names.py     # once, and whenever Mathlib moves
python3 scripts/build_search_index.py
python3 -m http.server 8000 --directory index   # then open /search.html
```

Outputs:

- `index/statements.json` — one record per declaration: name, origin (`registry`
  or `overlay:<source>`), entry, repository and commit, the Lean statement source
  (for our entries), the informal statement where we have one, which checks ran
  and their verdicts, sign-offs, and any Mathlib name collision.
- `index/meta.json` — counts and provenance.
- `index/search.html` — a dependency-free page over that JSON: text search across
  names, statements and informal text, with filters for origin, sign-off, and
  whether an informal statement exists.

Every record says what was checked and by whom, so an unsigned record is
searchable without being misread as vetted.

## Names must not conflict with Mathlib's

A search surface is only readable if names mean what they normally mean. Spec
files legitimately replicate implementation definitions so a statement can stand
alone — but a replicated definition landing on a name Mathlib already owns makes
the statement read as Mathlib's notion while meaning the spec's, and no reader
catches that by eye.

```bash
python3 scripts/check_mathlib_conflicts.py --all
```

- **conflict** — a spec declares a fully-qualified name that exists in Mathlib.
- **warning** — a spec sets an `attribute` on a Mathlib declaration, or `export`s
  a namespace, either of which can change how existing declarations elaborate.

Exit code 1 on any conflict, so it can gate CI. Every index record carries its
conflicts, and the search page tags them.

Deliberate exceptions go in the entry TOML with a reason:

```toml
[[mathlib_conflict_exemptions]]
name = "Polynomial.myVariant"
reason = "Mathlib added this name after the revision this entry pins."
```

The name list comes from Mathlib's own doc-gen4 declaration data (~421k
declarations), so no Lean toolchain or Mathlib build is needed. It tracks current
Mathlib rather than each entry's pinned revision: a name it reports is real, a
name it misses may still exist in an older revision. `data/mathlib-names.meta.json`
records exactly which snapshot was used.
