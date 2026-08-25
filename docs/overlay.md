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

## Signing off on an overlaid record

Same interface as a registry entry: the
[sign-off issue form](../.github/ISSUE_TEMPLATE/spec-signoff.yml), choosing
**Overlay record: palomar** or **Overlay record: leanpool** as the target kind,
the upstream id as the Target ID, and the declarations you reviewed (or `*` for
all of them). The Action appends a `[[signoff]]` block to `overlay/signoffs.toml`
and opens a PR, exactly as it appends `[[signoffs]]` to an entry TOML.

Read the packet first — it is the same artifact, built from what upstream publishes:

```bash
python3 scripts/generate_signoff_packet.py --overlay leanpool:2-coloring-1-round
```

The Action fills in the hashes that make the sign-off go stale, from the record
as it stands when you sign:

```toml
[[signoff]]
source = "leanpool"
upstream_id = "2-coloring-1-round"
declarations = ["Distributed2Coloring.pStar_ge_23879"]   # or ["*"]
github_user = "your-handle"
date = "2026-08-25"
issue = 42
verdict = "approved"                                      # approved | rejected
statement_hash = "sha256:…"
lean_source_hash = "sha256:…"
comment = "Harper (1966); initial-segment ordering matches the informal statement."
```

Nobody copies a hash by hand: a sign-off bound to a hash the reviewer transcribed
is a sign-off bound to whatever they happened to paste. `statement_hash` covers
the declarations, informal text, pinned commit and upstream snapshot;
`lean_source_hash` covers the Lean file the statements live in, which is what
catches a theorem's *type* changing under an unchanged name. Either moving marks
the sign-off **stale**.

A rejection is recorded too, with `verdict = "rejected"`. It is information the
next reader needs, and the search index renders it as a rejection — never as a
sign-off, and never as absence of one.

`import_upstream.py` never writes `overlay/signoffs.toml`, so re-importing cannot
clobber review.

## Promoting an overlay record to a full entry

Mirroring records what upstream checked. To have *our* pipeline check it, the
entry needs spec files we write and vet — that is a human step, not an import.
Add `entries/<id>.toml` and `specs/<id>/` as for any other entry, and note the
upstream id in the entry description so the two records can be connected.
