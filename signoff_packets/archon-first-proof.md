# Sign-off packet — Archon FirstProof Results

*Generated 2026-08-25 17:19 UTC by `scripts/generate_signoff_packet.py`. Do not edit by hand.*

- **Entry**: `archon-first-proof`
- **Upstream**: https://github.com/frenzymath/Archon-FirstProof-Results @ `35550f2bc0a5`
- **Lean**: leanprover/lean4:v4.28.0
- **Machine checks**: level 2 (pre-checks-model result) — overall **pass** at 2026-08-23T03:07:54Z
- **Informal statements**: none adopted yet — run `python3 scripts/fetch_blueprint_statements.py entries/archon-first-proof.toml`

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
- [ ] Every definition the statement leans on means what its name claims.
- [ ] Definitions replicated from the impl do not shadow a Mathlib definition of
      the same name with different content (`scripts/check_mathlib_conflicts.py`
      reports suspected collisions).
- [ ] Universe variables and implicit binders match the impl.
- [ ] The statement is `sorry`-ed: the spec asserts, it does not prove.


---

## `Registry.ArchonFirstProof.Problem4`

- Spec file: [`specs/archon-first-proof/Registry/ArchonFirstProof/Problem4.lean`](../specs/archon-first-proof/Registry/ArchonFirstProof/Problem4.lean)
- Implementation module: `FirstProof.FirstProof4.Problem4`
- Spec file sha256: `5f5c9cc8eaeb02b3…`
- Existing sign-off: **none**

### `Problem4.harmonic_mean_inequality_full`

*Machine checks: comparator: pass*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> **Main Theorem (Problem 4)**: Harmonic-mean inequality for Φₙ under box-plus
>     convolution. For monic real-rooted polynomials p, q of degree n ≥ 2:
>     1/Φₙ(p ⊞ₙ q) ≥ 1/Φₙ(p) + 1/Φₙ(q)

**Lean statement** (`Registry/ArchonFirstProof/Problem4.lean` lines 133–139):

```lean
theorem harmonic_mean_inequality_full
    (n : ℕ) (hn : 2 ≤ n) (p q : ℝ[X])
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_real : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0)
    (hq_real : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0) :
    invPhiN_poly n (polyBoxPlus n p q) ≥ invPhiN_poly n p + invPhiN_poly n q := by sorry
```

---

## `Registry.ArchonFirstProof.Problem6`

- Spec file: [`specs/archon-first-proof/Registry/ArchonFirstProof/Problem6.lean`](../specs/archon-first-proof/Registry/ArchonFirstProof/Problem6.lean)
- Implementation module: `FirstProof.FirstProof6.Problem6`
- Spec file sha256: `f3a00cbc2115e869…`
- Existing sign-off: **none**

### `Problem6.exists_eps_light_subset`

*Machine checks: comparator: pass*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> **Main Theorem (Problem 6)**: For every simple graph G on a finite vertex set V
>     and every ε ∈ (0, 1], there exists an ε-light subset S with |S| ≥ ε/256 · |V|.

**Lean statement** (`Registry/ArchonFirstProof/Problem6.lean` lines 47–52):

```lean
theorem exists_eps_light_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∃ S : Finset V, IsEpsLight G ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤
      (S.card : ℝ) := by sorry
```

---

## Submitting

Open a [sign-off issue](https://github.com/GasStationManager/VibeRegistry/issues/new?template=spec-signoff.yml) for `archon-first-proof`, listing the spec files you reviewed. A GitHub Action records the sign-off in the entry TOML and marks it stale automatically if the spec files change afterwards.

> 2 declaration(s) have no informal statement adopted: `Problem4.harmonic_mean_inequality_full`, `Problem6.exists_eps_light_subset`.
