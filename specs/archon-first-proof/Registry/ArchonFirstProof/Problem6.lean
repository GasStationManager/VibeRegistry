/-
  # Spec for Large Epsilon-Light Vertex Subsets (Archon-FirstProof Problem 6)

  Source: https://github.com/frenzymath/Archon-FirstProof-Results
  Module: FirstProof.FirstProof6.Problem6

  Main theorem: For every simple graph G on a finite vertex set V
  and every ε ∈ (0, 1], there exists an ε-light subset S
  with |S| ≥ ε/256 · |V|.

  Definitions replicated from FirstProof.FirstProof6.Auxiliary.LaplacianBasics
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Laplacian matrix of a simple graph, defined as ∑_{e ∈ E} L_e
    where each L_e is the edge Laplacian.
    We use the standard definition L_{ij} = deg(i) if i=j, -1 if i~j, 0 otherwise. -/
def graphLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (G.Adj i)).card : ℝ)
    else if G.Adj i j then -1
    else 0

/-- The Laplacian of the induced subgraph on S: restricting to edges within S. -/
def inducedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (fun k => i ∈ S ∧ k ∈ S ∧ G.Adj i k)).card : ℝ)
    else if G.Adj i j ∧ i ∈ S ∧ j ∈ S then -1
    else 0

/-- A set S is ε-light if εL - L_S is positive semidefinite. -/
def IsEpsLight (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (S : Finset V) : Prop :=
  (ε • graphLaplacian G - inducedLaplacian G S).PosSemidef

/-- **Main Theorem (Problem 6)**: For every simple graph G on a finite vertex set V
    and every ε ∈ (0, 1], there exists an ε-light subset S with |S| ≥ ε/256 · |V|. -/
theorem exists_eps_light_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∃ S : Finset V, IsEpsLight G ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤
      (S.card : ℝ) := by sorry

end Problem6
