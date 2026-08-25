# Overlay: mirroring upstream registries

Two other public registries check Lean formalizations, and neither has a human
sign-off step:

| Registry | Machine checks | Statement fidelity judged by |
|----------|----------------|------------------------------|
| [Palomar](https://palomar-registry.org/) | comparator, Lean + NanoDa kernels, axiom allowlist | a language model |
| [LeanPool](https://github.com/Vilin97/lean-pool) | builds warning-free, Mathlib linters, `sorry`-free, axiom limits | a language model |

Both are careful about the part a machine can settle, and explicit that the part
a machine cannot settle — *does this Lean statement say what the mathematics
says?* — is left to an automated judge. That is the layer VibeRegistry adds.

So we mirror rather than compete: import their records, keep our sign-offs
separate, and let a reader see both at once. It is the relation an overlay
journal has to arXiv.

## Importing

```bash
python3 scripts/import_upstream.py --all          # palomar + leanpool
python3 scripts/import_upstream.py --source palomar --limit 20
python3 scripts/import_upstream.py --reindex      # rebuild overlay/index.json
```

Layout:

```
overlay/palomar/<PALOMAR-ID>.json   normalized record, one per upstream entry
overlay/leanpool/<slug>.json
overlay/signoffs.toml               OUR sign-offs (hand-maintained)
overlay/index.json                  merged view, sign-offs attached
```

A record carries the upstream id and URL, repository and pinned commit where the
upstream publishes one, the declaration names, per-declaration informal
statements where upstream publishes them (LeanPool does; Palomar's feed carries a
per-entry abstract instead), classification, licence, and what the upstream
registry itself checked.

`import_upstream.py` never writes `overlay/signoffs.toml`. Re-importing cannot
clobber human review.

## Signing off on an overlaid entry

Add a block to `overlay/signoffs.toml` (via PR) naming what you reviewed:

```toml
[[signoff]]
source = "leanpool"
upstream_id = "boolean-isoperimetry"
declarations = ["BooleanIsoperimetry.harper_theorem"]   # or ["*"]
github_user = "your-handle"
date = "2026-08-21"
verdict = "approved"
statement_hash = "sha256:…"    # copy from overlay/leanpool/boolean-isoperimetry.json
comment = "Harper (1966); initial-segment ordering matches the informal statement."
```

`statement_hash` is what makes the sign-off honest over time: it hashes the
declaration names, informal statements, pinned commit and upstream snapshot that
were reviewed. When upstream publishes a new version the hash stops matching and
`import_upstream.py --reindex` reports the sign-off as **stale** instead of
carrying it forward.

Metadata alone is not enough for LeanPool, which publishes no per-project commit
and vendors its projects at mutable `main`: a theorem's *type* could change while
its name and informal text stay put. So every LeanPool record pins the
`snapshot_commit` it was read from, and a signed-off record also carries
`lean_source_hash` — the hash of the Lean file its statements live in, fetched at
that snapshot:

```bash
python3 scripts/import_upstream.py --reindex --fetch-sources
```

A sign-off goes stale if either hash moves, and the record says which.

A sign-off covers exactly the declarations it names. Listing
`declarations = ["Foo.bar"]` signs `Foo.bar` and nothing else — the search index
attaches it only to that declaration, and only a current, approved sign-off reads
as one.

A full sync (no `--limit`) also removes mirrored records the source no longer
publishes; a partial import never prunes, since it says nothing about what
upstream still has.

Sign-offs on our own entries still go through the
[sign-off issue form](../.github/ISSUE_TEMPLATE/spec-signoff.yml); extending that
Action to cover overlay records is not done yet.

## Promoting an overlay record to a full entry

Mirroring records what upstream checked. To have *our* pipeline check it, the
entry needs spec files we write and vet — that is a human step, not an import.
Add `entries/<id>.toml` and `specs/<id>/` as for any other entry, and note the
upstream id in the entry description so the two records can be connected.
