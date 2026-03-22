/-
  # Spec for Harmonic-Mean Inequality (Archon-FirstProof Problem 4)

  Source: https://github.com/frenzymath/Archon-FirstProof-Results
  Module: FirstProof.FirstProof4.Problem4

  Main theorem: For monic real-rooted polynomials p, q of degree n ≥ 2,
    1/Φₙ(p ⊞ₙ q) ≥ 1/Φₙ(p) + 1/Φₙ(q)

  Reference: Marcus, Spielman, Srivastava — Interlacing Families

  Definitions replicated from:
    FirstProof.FirstProof4.Auxiliary.Defs (polyBoxPlus chain)
    FirstProof.FirstProof4.Auxiliary.PhiN (PhiN)
    FirstProof.FirstProof4.Auxiliary.SignSquarefree (extract_ordered_real_roots)
    FirstProof.FirstProof4.Auxiliary.InvPhiN (invPhiN_poly)
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star

open Polynomial BigOperators Nat Classical

noncomputable section

namespace Problem4

/-! ### Definitions from Defs.lean -/

variable (n : ℕ) (hn : 2 ≤ n)

/-- The coefficient formula for box-plus convolution. -/
def boxPlusCoeff (n : ℕ) (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sum fun i ↦
    ((n - i).factorial * (n - (k - i)).factorial : ℝ) /
      ((n.factorial * (n - k).factorial : ℝ)) * a i * b (k - i)

/-- The box-plus convolution of two coefficient sequences of degree ≤ n. -/
def boxPlusConv (n : ℕ) (a b : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ if k ≤ n then boxPlusCoeff n a b k else 0

/-- Convert a polynomial to its coefficient sequence in the basis x^{n-k}. -/
def polyToCoeffs (p : ℝ[X]) (n : ℕ) : ℕ → ℝ :=
  fun k ↦ p.coeff (n - k)

/-- Convert a coefficient sequence back to a polynomial. -/
def coeffsToPoly (a : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  (Finset.range (n + 1)).sum fun k ↦ Polynomial.C (a k) * Polynomial.X ^ (n - k)

/-- The box-plus convolution of two polynomials of degree ≤ n. -/
def polyBoxPlus (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  coeffsToPoly (boxPlusConv n (polyToCoeffs p n) (polyToCoeffs q n)) n

/-! ### Definitions from PhiN.lean -/

/-- Φₙ(p) for a polynomial with distinct real roots λ₁,...,λₙ:
    Φₙ(p) = ∑ᵢ (∑_{j≠i} 1/(λᵢ - λⱼ))² -/
def PhiN (roots : Fin n → ℝ) : ℝ :=
  ∑ i, ((Finset.univ.filter (· ≠ i)).sum fun j ↦
    1 / (roots i - roots j)) ^ 2

/-! ### Lemma from SignSquarefree.lean -/

/-- Extraction of ordered real roots: if a monic separable polynomial of degree m
    has all complex roots with zero imaginary part, then it has m distinct ordered
    real roots. -/
lemma extract_ordered_real_roots (f : ℝ[X]) (m : ℕ)
    (hf_monic : f.Monic) (hf_deg : f.natDegree = m)
    (hf_real : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0)
    (hf_sep : Squarefree f) :
    ∃ (μ : Fin m → ℝ), StrictMono μ ∧ (∀ i, f.IsRoot (μ i)) := by sorry

/-! ### Definition from InvPhiN.lean -/

/-- The polynomial-level inverse of PhiN. For a monic squarefree polynomial with
    all real roots, returns `1/Φₙ(p)` using the sorted roots. Otherwise returns 0. -/
def invPhiN_poly (n : ℕ) (p : ℝ[X]) : ℝ :=
  if h : p.Monic ∧ p.natDegree = n ∧ Squarefree p ∧
      (∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0) then
    1 / PhiN n (extract_ordered_real_roots p n h.1 h.2.1 h.2.2.2 h.2.2.1).choose
  else 0

/-! ### Main theorem -/

/-- **Main Theorem (Problem 4)**: Harmonic-mean inequality for Φₙ under box-plus
    convolution. For monic real-rooted polynomials p, q of degree n ≥ 2:
    1/Φₙ(p ⊞ₙ q) ≥ 1/Φₙ(p) + 1/Φₙ(q) -/
theorem harmonic_mean_inequality_full
    (n : ℕ) (hn : 2 ≤ n) (p q : ℝ[X])
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_real : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0)
    (hq_real : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0) :
    invPhiN_poly n (polyBoxPlus n p q) ≥ invPhiN_poly n p + invPhiN_poly n q := by sorry

end Problem4
