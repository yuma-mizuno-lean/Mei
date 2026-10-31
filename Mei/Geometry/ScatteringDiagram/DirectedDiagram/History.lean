/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Algebra.Lie.Graded.Shifted.Resolution

/-!
# Component-history identities from consistency

Two finite chains of admissible paths with the same endpoints in a consistent
directed diagram give equal finite sums of homogeneous component maps. The
chains can have different lengths and intermediate vertices. The equality holds
for every incoming parameter simultaneously and in each retained outgoing degree.

We combine endpoint independence of `DirectedDiagram.levelTransport` with
`PositiveDegrees.sum_component_homogeneousHistory_eq_of_prod_eq`. The finite
sum includes every algebraic degree history, with zero maps contributing zero;
identification of the histories realized by a geometric local resolution is
additional data. This is the coefficient-map part of local resolution identities
as in Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ : Type} {Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

variable {M E : Type*} [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [AddCommMonoid E] [Module R E]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]
  (p : Γ)

/-- Consistency gives equality of the finite sums of outgoing component maps
along any two chains with common endpoints. There is no assumption that the
represented action is faithful, or that the incoming parameter is nonzero. -/
theorem sum_component_homogeneousHistory_levelPathProduct_eq
    {k : ℕ} (hD : D.LevelConsistent k) {n m : ℕ}
    (x : Fin (n + 1) → WallComplement (fun j : D.active k => (D.wall j).support))
    (y : Fin (m + 1) → WallComplement (fun j : D.active k => (D.wall j).support))
    (γ : (j : Fin n) → AdmissiblePLPath (x j.succ) (x j.castSucc))
    (γ' : (j : Fin m) → AdmissiblePLPath (y j.succ) (y j.castSucc))
    (h₀ : x 0 = y 0) (h₁ : x (Fin.last n) = y (Fin.last m))
    (q : Γ) (hq : d.degree (q - p) ≤ k)
    (a : E →ₗ[R] (d.shiftedLieFiltration ℒ ℳ p).quotient k) :
    ∑ r : Fin n → (d.finite_cutoff k).toFinset,
      (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ j))).toLinearMap)
          (fun j => (r j).val)).comp a) =
    ∑ r : Fin m → (d.finite_cutoff k).toFinset,
      (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ' j))).toLinearMap)
          (fun j => (r j).val)).comp a) := by
  apply d.sum_component_homogeneousHistory_eq_of_prod_eq ℒ ℳ p k _ _ _ q hq a
  rw [D.prod_levelPathProduct_eq_levelTransport hD x γ,
    D.prod_levelPathProduct_eq_levelTransport hD y γ', h₀, h₁]

end Mei.DirectedDiagram
