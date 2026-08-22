# Sign-off packet — Lean Statistical Learning Theory

*Generated 2026-08-22 01:23 UTC by `scripts/generate_signoff_packet.py`. Do not edit by hand.*

- **Entry**: `stat-learning`
- **Upstream**: https://github.com/YuanheZ/lean-stat-learning-theory @ `7b82b1323c80`
- **Lean**: leanprover/lean4:v4.27.0-rc1
- **Machine checks**: comparator — overall **pass** at 2026-08-22T01:01:09Z
- **Informal statements**: none adopted yet — run `python3 scripts/fetch_blueprint_statements.py entries/stat-learning.toml`

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

## `Registry.StatLearning.GaussianMeasure`

- Spec file: [`specs/stat-learning/Registry/StatLearning/GaussianMeasure.lean`](../specs/stat-learning/Registry/StatLearning/GaussianMeasure.lean)
- Implementation module: `SLT.GaussianMeasure`
- Spec file sha256: `d4ebcad7b14c6c93…`
- Existing sign-off: **none**

### `GaussianMeasure.stdGaussianPi`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Standard Gaussian product measure: the product of n independent standard Gaussians N(0,1)

**Lean statement** (`Registry/StatLearning/GaussianMeasure.lean` lines 14–15):

```lean
noncomputable def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1
```

### `GaussianMeasure.stdGaussianE`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> The standard Gaussian on EuclideanSpace as pushforward of stdGaussianPi via the equivalence.

**Lean statement** (`Registry/StatLearning/GaussianMeasure.lean` lines 18–19):

```lean
noncomputable def stdGaussianE (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (EuclideanSpace.equiv (Fin n) ℝ).symm (stdGaussianPi n)
```

---

## `Registry.StatLearning.CoveringNumber`

- Spec file: [`specs/stat-learning/Registry/StatLearning/CoveringNumber.lean`](../specs/stat-learning/Registry/StatLearning/CoveringNumber.lean)
- Implementation module: `SLT.CoveringNumber`
- Spec file sha256: `80a9420d27f3cb9e…`
- Existing sign-off: **none**

### `IsENet`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> `t` is an `eps`-net for `s` if every point of `s` lies in a closed ball of radius `eps`
> centered at some element of `t`.

**Lean statement** (`Registry/StatLearning/CoveringNumber.lean` lines 13–14):

```lean
def IsENet {A : Type*} [PseudoMetricSpace A] (t : Finset A) (eps : ℝ) (s : Set A) : Prop :=
  s ⊆ ⋃ x ∈ t, closedBall x eps
```

### `coveringNumber`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Covering number: the minimal cardinality of a finite `eps`-net, as `WithTop Nat`.

**Lean statement** (`Registry/StatLearning/CoveringNumber.lean` lines 17–18):

```lean
noncomputable def coveringNumber {A : Type*} [PseudoMetricSpace A] (eps : ℝ) (s : Set A) : WithTop Nat :=
  sInf {n : WithTop Nat | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop Nat) = n}
```

---

## `Registry.StatLearning.MetricEntropy`

- Spec file: [`specs/stat-learning/Registry/StatLearning/MetricEntropy.lean`](../specs/stat-learning/Registry/StatLearning/MetricEntropy.lean)
- Implementation module: `SLT.MetricEntropy`
- Spec file sha256: `115cefd63b212ac0…`
- Existing sign-off: **none**

### `metricEntropyOfNat`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Helper to compute metric entropy given a natural number.

**Lean statement** (`Registry/StatLearning/MetricEntropy.lean` lines 32–33):

```lean
def metricEntropyOfNat (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else Real.log n
```

### `metricEntropy`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Metric entropy: log of covering number.

**Lean statement** (`Registry/StatLearning/MetricEntropy.lean` lines 36–39):

```lean
def metricEntropy (eps : ℝ) (s : Set A) : ℝ :=
  match _h : coveringNumber eps s with
  | ⊤ => 0
  | (n : ℕ) => metricEntropyOfNat n
```

### `sqrtEntropy`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Square root of metric entropy.

**Lean statement** (`Registry/StatLearning/MetricEntropy.lean` lines 42–43):

```lean
def sqrtEntropy (eps : ℝ) (s : Set A) : ℝ :=
  Real.sqrt (metricEntropy eps s)
```

### `dudleyIntegrand`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Dudley integrand: √(log N(ε, s)) as ENNReal.

**Lean statement** (`Registry/StatLearning/MetricEntropy.lean` lines 46–47):

```lean
def dudleyIntegrand (eps : ℝ) (s : Set A) : ℝ≥0∞ :=
  ENNReal.ofReal (sqrtEntropy eps s)
```

### `entropyIntegralENNReal`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Entropy integral (ENNReal): ∫₀^D √(log N(ε, s)) dε.

**Lean statement** (`Registry/StatLearning/MetricEntropy.lean` lines 50–51):

```lean
def entropyIntegralENNReal (s : Set A) (D : ℝ) : ℝ≥0∞ :=
  ∫⁻ eps in Set.Ioc (0 : ℝ) D, dudleyIntegrand eps s
```

### `entropyIntegral`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> Entropy integral (real-valued wrapper).

**Lean statement** (`Registry/StatLearning/MetricEntropy.lean` lines 54–55):

```lean
def entropyIntegral (s : Set A) (D : ℝ) : ℝ :=
  (entropyIntegralENNReal s D).toReal
```

---

## `Registry.StatLearning.SubGaussian`

- Spec file: [`specs/stat-learning/Registry/StatLearning/SubGaussian.lean`](../specs/stat-learning/Registry/StatLearning/SubGaussian.lean)
- Implementation module: `SLT.SubGaussian`
- Spec file sha256: `dc3fc809cf56d491…`
- Existing sign-off: **none**

### `IsSubGaussianProcess`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> A stochastic process X indexed by a metric space is σ-sub-Gaussian if
> the MGF of increments satisfies E[exp(l(X_s - X_t))] ≤ exp(l²σ²d(s,t)²/2).

**Lean statement** (`Registry/StatLearning/SubGaussian.lean` lines 17–19):

```lean
def IsSubGaussianProcess (μ : Measure Ω) (X : A → Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ s t : A, ∀ l : ℝ, μ[fun ω => exp (l * (X s ω - X t ω))] ≤
    exp (l^2 * σ^2 * (dist s t)^2 / 2)
```

---

## `Registry.StatLearning.EfronSteinApp`

- Spec file: [`specs/stat-learning/Registry/StatLearning/EfronSteinApp.lean`](../specs/stat-learning/Registry/StatLearning/EfronSteinApp.lean)
- Implementation module: `SLT.GaussianPoincare.EfronSteinApp`
- Spec file sha256: `d6ba113a87118f67…`
- Existing sign-off: **none**

### `EfronSteinApp.CompactlySupportedSmooth`

*Machine checks: comparator: not-applicable*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> A function is compactly supported and smooth (C²)

**Lean statement** (`Registry/StatLearning/EfronSteinApp.lean` lines 15–16):

```lean
def CompactlySupportedSmooth (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ HasCompactSupport f
```

---

## `Registry.StatLearning.GaussianLipschitzConcentration`

- Spec file: [`specs/stat-learning/Registry/StatLearning/GaussianLipschitzConcentration.lean`](../specs/stat-learning/Registry/StatLearning/GaussianLipschitzConcentration.lean)
- Implementation module: `SLT.GaussianLipConcen`
- Spec file sha256: `9a0d1e293d37b275…`
- Existing sign-off: **none**

### `GaussianLipConcen.gaussian_lipschitz_concentration`

*Machine checks: comparator: pass*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> **Gaussian Lipschitz Concentration Inequality**
>
> For any L-Lipschitz function f on ℝⁿ equipped with the standard Gaussian measure,
> the probability that f deviates from its mean by more than t is at most
> 2 exp(-t² / (2L²)).

**Lean statement** (`Registry/StatLearning/GaussianLipschitzConcentration.lean` lines 39–43):

```lean
theorem gaussian_lipschitz_concentration {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hn : 0 < n) (hL : 0 < L) (hf : LipschitzWith L f) (t : ℝ) (ht : 0 < t) :
    let μ := stdGaussianE n
    (μ {x | t ≤ |f x - ∫ y, f y ∂μ|}).toReal ≤ 2 * exp (-t^2 / (2 * (L : ℝ)^2)) := by
  sorry
```

---

## `Registry.StatLearning.Dudley`

- Spec file: [`specs/stat-learning/Registry/StatLearning/Dudley.lean`](../specs/stat-learning/Registry/StatLearning/Dudley.lean)
- Implementation module: `SLT.Dudley`
- Spec file sha256: `d0b8f0e3f0b1ceb2…`
- Existing sign-off: **none**

### `dudley`

*Machine checks: comparator: pass*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> **Dudley's Entropy Integral Theorem**
>
> For a σ-sub-Gaussian process X indexed by a totally bounded set s with diameter ≤ D,
> the expected supremum satisfies:
>   E[sup_{t∈s} X_t] ≤ 12√2 · σ · ∫₀^D √(log N(ε, s)) dε

**Lean statement** (`Registry/StatLearning/Dudley.lean` lines 86–97):

```lean
theorem dudley {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : A → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : IsSubGaussianProcess μ X σ)
    {s : Set A} (hs : TotallyBounded s)
    {D : ℝ} (hD : 0 < D) (hdiam : Metric.diam s ≤ D)
    (t₀ : A) (ht₀ : t₀ ∈ s) (hcenter : ∀ ω, X t₀ ω = 0)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_int_exp : ∀ t s : A, ∀ l : ℝ, Integrable (fun ω => Real.exp (l * (X t ω - X s ω))) μ)
    (hfinite : entropyIntegralENNReal s D ≠ ⊤)
    (hcont : ∀ ω, Continuous (fun (t : ↥s) => X t.1 ω)) :
    ∫ ω, ⨆ t ∈ s, X t ω ∂μ ≤ (12 * Real.sqrt 2) * σ * entropyIntegral s D := by
  sorry
```

---

## `Registry.StatLearning.EfronStein`

- Spec file: [`specs/stat-learning/Registry/StatLearning/EfronStein.lean`](../specs/stat-learning/Registry/StatLearning/EfronStein.lean)
- Implementation module: `SLT.EfronStein`
- Spec file sha256: `8b251546ee2c17e2…`
- Existing sign-off: **none**

### `efronStein`

*Machine checks: comparator: pass*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> **Efron-Stein Inequality**
>
> For independent random variables X₁,...,Xₙ and a square-integrable function f:
>   Var(f) ≤ ∑ᵢ E[(f - E^{(i)}f)²]
> where E^{(i)}f is the conditional expectation given all variables except Xᵢ.

**Lean statement** (`Registry/StatLearning/EfronStein.lean` lines 24–27):

```lean
theorem efronStein (f : (Fin n → Ω) → ℝ) (hf : MemLp f 2 (Measure.pi μs)) :
    variance f (Measure.pi μs) ≤
    ∑ i : Fin n, ∫ x, (f x - condExpExceptCoord (μs := μs) i f x)^2 ∂(Measure.pi μs) := by
  sorry
```

---

## `Registry.StatLearning.GaussianPoincare`

- Spec file: [`specs/stat-learning/Registry/StatLearning/GaussianPoincare.lean`](../specs/stat-learning/Registry/StatLearning/GaussianPoincare.lean)
- Implementation module: `SLT.GaussianPoincare.Limit`
- Spec file sha256: `3027217ddd233d20…`
- Existing sign-off: **none**

### `GaussianPoincare.gaussianPoincare`

*Machine checks: comparator: pass*

**Informal statement**: _none adopted_ — the reviewer must supply the intended mathematics from the literature.

**Spec docstring**:

> **Gaussian Poincaré Inequality**
>
> For any f ∈ C²_c(ℝ) and X ~ N(0,1):
>   Var(f(X)) ≤ E[f'(X)²]

**Lean statement** (`Registry/StatLearning/GaussianPoincare.lean` lines 46–49):

```lean
theorem gaussianPoincare {f : ℝ → ℝ} (hf : CompactlySupportedSmooth f) :
    variance (fun x => f x) stdGaussianMeasure ≤
    ∫ x, (deriv f x)^2 ∂stdGaussianMeasure := by
  sorry
```

---

## Submitting

Open a [sign-off issue](https://github.com/GasStationManager/VibeRegistry/issues/new?template=spec-signoff.yml) for `stat-learning`, listing the spec files you reviewed. A GitHub Action records the sign-off in the entry TOML and marks it stale automatically if the spec files change afterwards.

> 16 declaration(s) have no informal statement adopted: `GaussianMeasure.stdGaussianPi`, `GaussianMeasure.stdGaussianE`, `IsENet`, `coveringNumber`, `metricEntropyOfNat`, `metricEntropy`, `sqrtEntropy`, `dudleyIntegrand`, `entropyIntegralENNReal`, `entropyIntegral`, `IsSubGaussianProcess`, `EfronSteinApp.CompactlySupportedSmooth`, `GaussianLipConcen.gaussian_lipschitz_concentration`, `dudley`, `efronStein`, `GaussianPoincare.gaussianPoincare`.
