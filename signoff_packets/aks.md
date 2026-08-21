# Sign-off packet — AKS Sorting Networks

*Generated 2026-08-21 17:41 UTC by `scripts/generate_signoff_packet.py`. Do not edit by hand.*

- **Entry**: `aks`
- **Upstream**: https://github.com/girving/aks @ `f172ac6c2e46`
- **Lean**: leanprover/lean4:v4.29.0-rc4
- **Machine checks**: level 2 (pre-checks-model result) — overall **pass** at 2026-08-09T03:46:56Z
- **Informal statements**: none adopted yet — run `python3 scripts/fetch_blueprint_statements.py entries/aks.toml`

## What you are attesting

The machine checks below establish that the *implementation proves the spec*. They say nothing about whether the spec is the right statement. That is what your sign-off adds, and it is the only part no tool here can do for you.

Sign-off is optional: an entry whose comparator check passes stands on its own as a verified Lean statement. A sign-off says a human read the statement and vouches for it meaning what it claims.

### Checklist

- [ ] The Lean statement says what the informal statement says — same hypotheses,
      same conclusion, same quantifier order.
- [ ] No hypothesis is stronger than it looks (watch for `Nonempty`, finiteness,
      measurability, and typeclass assumptions that quietly rule out the hard case).
- [ ] No conclusion is weaker than it looks (existentials that are trivially
      satisfiable, bounds that hold vacuously).
- [ ] Definitions replicated from the impl mean what their names claim, and do not
      shadow a Mathlib definition of the same name with different content
      (`scripts/check_mathlib_conflicts.py` reports suspected collisions).
- [ ] Universe variables and implicit binders match the impl.
- [ ] The statement is `sorry`-ed: the spec asserts, it does not prove.


---

## `Registry.AKS.Challenge`

- Spec file: [`specs/aks/Registry/AKS/Challenge.lean`](../specs/aks/Registry/AKS/Challenge.lean)
- Implementation module: `AKS.Seiferas`
- Spec file sha256: `a048cb6f5dc6b549…`
- Existing sign-off: **none**

### `networks_exist`

*Machine checks: comparator: pass*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Efficient networks exist

**Lean statement** (`Registry/AKS/Challenge.lean` lines 64–66):

```lean
theorem networks_exist (n : ℕ) : ∃ net : ComparatorNetwork n, net.Sorts ∧
    net.depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n ∧
    net.size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n := by sorry
```

---

## Submitting

Open a [sign-off issue](https://github.com/GasStationManager/VibeRegistry/issues/new?template=spec-signoff.yml) for `aks`, listing the spec files you reviewed. A GitHub Action records the sign-off in the entry TOML and marks it stale automatically if the spec files change afterwards.

> 1 declaration(s) have no informal statement adopted: `networks_exist`.
