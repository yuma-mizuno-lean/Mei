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
chains can have different lengths and intermediate vertices. Each chain may use
its own uniform finite contributing support on the input range, so the full
positive degree cutoff is not required. The equality holds for every incoming
parameter simultaneously and in each retained outgoing degree.

We combine endpoint independence of `DirectedDiagram.levelTransport` with the
shared uniform expansion `sum_comp_homogeneousHistory_comp_eq` and the
`truncatedBCHAction` product law. The finite-cutoff specialization uses
`PositiveDegrees.shiftedQuotientGrading_piece_eq_bot`. It includes every
algebraic degree history, with zero maps contributing zero; identification of
the histories realized by a geometric local resolution is additional data.
This is the coefficient-map part of local resolution identities
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

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "G(" k ")" => TauCeti.InternalGrading.piece
  (d.shiftedQuotientGrading ℳ p k)

/-- Consistency gives equality of two uniformly supported sums of outgoing
component maps along chains with common endpoints. Each chain has its own finite
history support on the input range; the full positive degree cutoff need not be
summed, and no finite generation of the input range is assumed. -/
theorem sum_component_homogeneousHistory_levelPathProduct_eq_of_support
    {k : ℕ} (hD : D.LevelConsistent k) {n m : ℕ}
    (x : Fin (n + 1) → WallComplement (fun j : D.active k => (D.wall j).support))
    (y : Fin (m + 1) → WallComplement (fun j : D.active k => (D.wall j).support))
    (γ : (j : Fin n) → AdmissiblePLPath (x j.succ) (x j.castSucc))
    (γ' : (j : Fin m) → AdmissiblePLPath (y j.succ) (y j.castSucc))
    (h₀ : x 0 = y 0) (h₁ : x (Fin.last n) = y (Fin.last m))
    (q : Γ) (hq : d.degree (q - p) ≤ k)
    (a : E →ₗ[R] (d.shiftedLieFiltration ℒ ℳ p).quotient k)
    (S : Finset (Fin n → Γ)) (S' : Finset (Fin m → Γ))
    (hS : ∀ r ∉ S, (homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        (D.levelPathProduct k (γ j))).toLinearMap) r).comp a = 0)
    (hS' : ∀ r ∉ S', (homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        (D.levelPathProduct k (γ' j))).toLinearMap) r).comp a = 0) :
    ∑ r ∈ S, (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ j))).toLinearMap) r).comp a) =
    ∑ r ∈ S', (d.shiftedQuotientComponent ℳ p q k hq).comp
        ((homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ' j))).toLinearMap) r).comp a) := by
  have hprod : (List.ofFn fun j => D.levelPathProduct k (γ j)).prod =
      (List.ofFn fun j => D.levelPathProduct k (γ' j)).prod := by
    rw [D.prod_levelPathProduct_eq_levelTransport hD x γ,
      D.prod_levelPathProduct_eq_levelTransport hD y γ', h₀, h₁]
  calc
    _ = (d.shiftedQuotientComponent ℳ p q k hq).comp
        (((F).truncatedBCHAction d ℒ k
          (List.ofFn fun j => D.levelPathProduct k (γ j)).prod).toLinearMap.comp a) := by
      simpa only [(F).truncatedBCHAction_list_ofFn_prod_toLinearMap d ℒ k
        (fun j => D.levelPathProduct k (γ j))] using
        sum_comp_homogeneousHistory_comp_eq G(k)
          (fun j => ((F).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ j))).toLinearMap)
          a (d.shiftedQuotientComponent ℳ p q k hq) S hS
    _ = (d.shiftedQuotientComponent ℳ p q k hq).comp
        (((F).truncatedBCHAction d ℒ k
          (List.ofFn fun j => D.levelPathProduct k (γ' j)).prod).toLinearMap.comp a) := by
      rw [hprod]
    _ = _ := by
      symm
      simpa only [(F).truncatedBCHAction_list_ofFn_prod_toLinearMap d ℒ k
        (fun j => D.levelPathProduct k (γ' j))] using
        sum_comp_homogeneousHistory_comp_eq G(k)
          (fun j => ((F).truncatedBCHAction d ℒ k
            (D.levelPathProduct k (γ' j))).toLinearMap)
          a (d.shiftedQuotientComponent ℳ p q k hq) S' hS'

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
  let emb {l : ℕ} (r : Fin l → (d.finite_cutoff k).toFinset) : Fin l → Γ :=
    fun j => (r j).val
  have hemb {l : ℕ} : Function.Injective (@emb l) := by
    intro r r' hrr'
    funext j
    exact Subtype.ext (congrFun hrr' j)
  have hz {l : ℕ} (g : Fin l → d.truncatedGroup ℒ k)
      (r : Fin l → Γ) (hr : r ∉ Finset.univ.image (@emb l)) :
      (homogeneousHistory G(k)
        (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
          (g j)).toLinearMap) r).comp a = 0 := by
    have hr' : r ∉ Fintype.piFinset (fun _ : Fin l => (d.finite_cutoff k).toFinset) := by
      intro hmem
      apply hr
      exact Finset.mem_image.mpr
        ⟨fun j => ⟨r j, Fintype.mem_piFinset.mp hmem j⟩, Finset.mem_univ _, rfl⟩
    rw [homogeneousHistory_eq_zero_of_notMem_piFinset G(k) (d.finite_cutoff k).toFinset
      (d.shiftedQuotientGrading_piece_eq_bot ℳ p) _ r hr', LinearMap.zero_comp]
  have hsum := D.sum_component_homogeneousHistory_levelPathProduct_eq_of_support ℳ p hD
    x y γ γ' h₀ h₁ q hq a
    (Finset.univ.image (@emb n)) (Finset.univ.image (@emb m))
    (fun r hr => hz _ r hr) (fun r hr => hz _ r hr)
  rw [Finset.sum_image (fun r _ r' _ hrr' => hemb hrr'),
    Finset.sum_image (fun r _ r' _ hrr' => hemb hrr')] at hsum
  exact hsum

end Mei.DirectedDiagram
