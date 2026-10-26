/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Basic

/-!
# Sign factors across a wall

Suppose two characters preserve the nonzero signs of a third character on all
retained degrees, and send its zero degrees to the positive and negative sides,
respectively. Their sign factorizations are obtained by absorbing the old middle
factor into the positive or negative factor. In particular, the quotient of the
negative factors is exactly the middle factor on the wall. This is the algebraic
identity that makes a single wall crossing agree with endpoint transport.

The argument follows the single-crossing calculation in Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4, proof of
Lemma 3.2 ([arXiv:1603.00416v4](https://arxiv.org/html/1603.00416v4#S3.SS4)).
It uses `PositiveDegrees.signFactorizationEquiv` for uniqueness and
`Mei.signSubalgebra_le_of_sign_imp` for the subgroup inclusions. All hypotheses
concern degrees below the chosen cutoff; no behavior of higher degrees is required.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] (θ φ : N →+ A) (k : ℕ)

private theorem signFactor_mem_of_refinement (ε : SignType)
    (h : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (φ n) =
      if θ n = 0 then ε else SignType.sign (θ n))
    (g : d.truncatedGroup ℒ k) (s : SignType) :
    ((signFactorizationEquiv ℒ θ d k).symm g s : d.truncatedGroup ℒ k) ∈
      (signSubalgebra (d.truncatedGrading ℒ k) φ
        (if s = .zero then ε else s)).bchSubgroup := by
  apply LieSubalgebra.bchSubgroup_le_bchSubgroup.mpr
    (signSubalgebra_le_of_sign_imp _ _ _ _ _ ?_)
    ((signFactorizationEquiv ℒ θ d k).symm g s).property
  intro n hn hs
  rw [h n (d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hn)]
  by_cases hz : θ n = 0
  · have he : s = .zero := by simpa [hz] using hs.symm
    rw [ite_eq_left hz, ite_eq_left he]
  · have he : s ≠ .zero := fun he => hz (sign_eq_zero_iff.mp (hs.trans he))
    rw [ite_eq_right hz, ite_eq_right he]
    exact hs

/-- Moving all retained zero degrees to the positive side absorbs the middle
factor on the right of the positive factor and leaves the negative factor fixed. -/
theorem signFactorizationEquiv_symm_of_pos_refinement
    (h : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (φ n) =
      if θ n = 0 then .pos else SignType.sign (θ n))
    (g : d.truncatedGroup ℒ k) (s : SignType) :
    ((signFactorizationEquiv ℒ φ d k).symm g s : d.truncatedGroup ℒ k) =
      match s with
      | .pos => ((signFactorizationEquiv ℒ θ d k).symm g .pos : d.truncatedGroup ℒ k) *
          ((signFactorizationEquiv ℒ θ d k).symm g .zero : d.truncatedGroup ℒ k)
      | .zero => 1
      | .neg => ((signFactorizationEquiv ℒ θ d k).symm g .neg : d.truncatedGroup ℒ k) := by
  let a := (signFactorizationEquiv ℒ θ d k).symm g
  have hm := d.signFactor_mem_of_refinement ℒ θ φ k .pos h g
  let b : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) φ s).bchSubgroup
    | .pos => ⟨(a .pos : d.truncatedGroup ℒ k) * a .zero,
        Subgroup.mul_mem _ (by simpa using hm .pos) (by simpa using hm .zero)⟩
    | .zero => 1
    | .neg => ⟨a .neg, by simpa using hm .neg⟩
  have hb : (signFactorizationEquiv ℒ φ d k).symm g = b := by
    apply (signFactorizationEquiv ℒ φ d k).symm_apply_eq.mpr
    simpa only [signFactorizationEquiv_apply, b, OneMemClass.coe_one, mul_one] using
      (signFactorizationEquiv ℒ θ d k).apply_symm_apply g |>.symm
  rw [hb]
  cases s <;> rfl

/-- Moving all retained zero degrees to the negative side absorbs the middle
factor on the left of the negative factor and leaves the positive factor fixed. -/
theorem signFactorizationEquiv_symm_of_neg_refinement
    (h : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (φ n) =
      if θ n = 0 then .neg else SignType.sign (θ n))
    (g : d.truncatedGroup ℒ k) (s : SignType) :
    ((signFactorizationEquiv ℒ φ d k).symm g s : d.truncatedGroup ℒ k) =
      match s with
      | .pos => ((signFactorizationEquiv ℒ θ d k).symm g .pos : d.truncatedGroup ℒ k)
      | .zero => 1
      | .neg => ((signFactorizationEquiv ℒ θ d k).symm g .zero : d.truncatedGroup ℒ k) *
          ((signFactorizationEquiv ℒ θ d k).symm g .neg : d.truncatedGroup ℒ k) := by
  let a := (signFactorizationEquiv ℒ θ d k).symm g
  have hm := d.signFactor_mem_of_refinement ℒ θ φ k .neg h g
  let b : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) φ s).bchSubgroup
    | .pos => ⟨a .pos, by simpa using hm .pos⟩
    | .zero => 1
    | .neg => ⟨(a .zero : d.truncatedGroup ℒ k) * a .neg,
        Subgroup.mul_mem _ (by simpa using hm .zero) (by simpa using hm .neg)⟩
  have hb : (signFactorizationEquiv ℒ φ d k).symm g = b := by
    apply (signFactorizationEquiv ℒ φ d k).symm_apply_eq.mpr
    simpa only [signFactorizationEquiv_apply, b, OneMemClass.coe_one, mul_one, mul_assoc] using
      (signFactorizationEquiv ℒ θ d k).apply_symm_apply g |>.symm
  rw [hb]
  cases s <;> rfl

/-- The negative factors on opposite sides of a wall differ by its middle
factor, with the positive-to-negative crossing order. -/
theorem signFactorizationEquiv_neg_mul_inv_eq_middle (ψ : N →+ A)
    (hpos : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (φ n) =
      if θ n = 0 then .pos else SignType.sign (θ n))
    (hneg : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (ψ n) =
      if θ n = 0 then .neg else SignType.sign (θ n))
    (g : d.truncatedGroup ℒ k) :
    ((signFactorizationEquiv ℒ ψ d k).symm g .neg : d.truncatedGroup ℒ k) *
        ((signFactorizationEquiv ℒ φ d k).symm g .neg : d.truncatedGroup ℒ k)⁻¹ =
      ((signFactorizationEquiv ℒ θ d k).symm g .zero : d.truncatedGroup ℒ k) := by
  rw [d.signFactorizationEquiv_symm_of_neg_refinement ℒ θ ψ k hneg g .neg,
    d.signFactorizationEquiv_symm_of_pos_refinement ℒ θ φ k hpos g .neg]
  exact mul_inv_cancel_right _ _

/-- The positive factors give the same wall label, with the inverse on the
negative-side factor. No commutativity of the sign subgroups is required. -/
theorem signFactorizationEquiv_pos_inv_mul_eq_middle (ψ : N →+ A)
    (hpos : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (φ n) =
      if θ n = 0 then .pos else SignType.sign (θ n))
    (hneg : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (ψ n) =
      if θ n = 0 then .neg else SignType.sign (θ n))
    (g : d.truncatedGroup ℒ k) :
    ((signFactorizationEquiv ℒ ψ d k).symm g .pos : d.truncatedGroup ℒ k)⁻¹ *
        ((signFactorizationEquiv ℒ φ d k).symm g .pos : d.truncatedGroup ℒ k) =
      ((signFactorizationEquiv ℒ θ d k).symm g .zero : d.truncatedGroup ℒ k) := by
  rw [d.signFactorizationEquiv_symm_of_neg_refinement ℒ θ ψ k hneg g .pos,
    d.signFactorizationEquiv_symm_of_pos_refinement ℒ θ φ k hpos g .pos]
  exact inv_mul_cancel_left _ _

end Mei.PositiveDegrees
