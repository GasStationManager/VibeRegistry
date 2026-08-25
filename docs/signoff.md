# Sign-off

Machine checks establish that the implementation proves the spec. They say
nothing about whether the spec is the *right statement*. A sign-off is a named
human saying: I read this statement, and it means what it claims.

Sign-off has always been optional, and stays optional. An entry whose comparator
check passes stands on its own as a verified Lean statement — the registry
publishes it, and `index/search.html` will find it, sign-off or not. What a
sign-off adds is a person's name against the reading of the statement.

## Making it cheap to give

The work in a sign-off is comparing an informal statement with a Lean one. Two
scripts do the fetching and assembling so the reviewer only does the comparing.

### 1. Adopt the project's own informal statements

Most serious projects already wrote the mathematics down. `leanblueprint` even
ties prose to declarations with `\lean{Foo.bar}`:

```bash
python3 scripts/fetch_blueprint_statements.py entries/<id>.toml
```

Sources, in order of preference:

- `blueprint/src/**/*.tex` — leanblueprint LaTeX. Theorem/lemma/definition
  environments carrying `\lean{...}` are matched to the declarations they name;
  `\leanok`, `\uses{}` and friends are stripped.
- `formalization.yaml` — the Mathlib Initiative standard (also what Palomar
  submissions carry), or LeanPool's `projects.yml`. Any results list pairing a
  declaration name with an informal text is picked up.

Output is `informal/<entry-id>.json`, which records what was found, where it came
from, and which registered declarations are still uncovered.

### 2. Generate the review packet

```bash
python3 scripts/generate_signoff_packet.py entries/<id>.toml     # or --all
```

`signoff_packets/<entry-id>.md` puts, for each registered declaration: the
informal statement, the spec docstring, the exact Lean statement lifted from the
spec file with line numbers, the machine checks that ran, and any existing
sign-off — plus a checklist of the ways a statement usually goes wrong (a
hypothesis stronger than it looks, a vacuous conclusion, a definition shadowing
Mathlib, a mismatched universe).

Nothing in the packet is authoritative on its own; it is the spec files that are
signed off. The packet just means the reviewer does not have to assemble the
context by hand.

### 3. Submit

Open a [sign-off issue](../.github/ISSUE_TEMPLATE/spec-signoff.yml). One form
covers both kinds of target:

| Target kind | Target ID | What you reviewed | Recorded in |
|---|---|---|---|
| Registry entry | entry id | spec file paths | `entries/<id>.toml` |
| Overlay record: palomar | `PALOMAR-…` | declaration names, or `*` | `overlay/signoffs.toml` |
| Overlay record: leanpool | slug | declaration names, or `*` | `overlay/signoffs.toml` |

The Action parses the issue, works out which store the sign-off belongs in, binds
it to a hash of what you actually reviewed, and opens a PR. If the reviewed spec
files change later the sign-off is marked stale automatically
(`scripts/check_signoff_staleness.py`); for overlay records the equivalent check
runs on re-import (see [overlay.md](overlay.md)).

Rejections are recorded as well as approvals. A rejected review renders as a
rejection in the search index — the next reader learns more from "someone looked
and said no" than from silence.

## What a reviewer should watch for

- The Lean statement says what the informal statement says: same hypotheses, same
  conclusion, same quantifier order.
- No hypothesis is stronger than it looks — `Nonempty`, finiteness, measurability
  and typeclass assumptions can quietly exclude the hard case.
- No conclusion is weaker than it looks — trivially satisfiable existentials,
  vacuous bounds.
- Replicated definitions mean what their names claim. Specs replicate impl
  definitions on purpose; a replicated definition that lands on a name Mathlib
  already owns reads as Mathlib's notion and means something else.
  `scripts/check_mathlib_conflicts.py` flags those.
- Universe variables and implicit binders match the impl.
- The statement is `sorry`-ed: a spec asserts, it does not prove.
