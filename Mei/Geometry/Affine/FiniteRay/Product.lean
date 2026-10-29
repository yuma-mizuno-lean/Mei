/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Map

/-!
# Products and coordinate lifts of finite bent rays

A pair of finite bent rays determines a unique ray in the product affine space.
The two histories may bend at different times. In particular, increments erased
by the first projection remain in the forgotten coordinates. Realizations,
interval directions and incoming affine data are computed coordinatewise.

Prescribing the endpoint, final direction and finite increments in the forgotten
coordinates therefore integrates them uniquely over a given projected ray. This
is the geometric lifting used for cylinder walls; no choice of an origin in the
point spaces is required.
-/

public noncomputable section

namespace Mei.FiniteAffineRay

variable {V W P Q : Type*} [AddCommGroup V] [AddCommGroup W]

/-- Combine two finite affine histories, allowing bends at different times. -/
def prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    FiniteAffineRay (V × W) (P × Q) where
  endpoint := (β.endpoint, γ.endpoint)
  direction := (β.direction, γ.direction)
  bends := Finsupp.zipWith Prod.mk rfl β.bends γ.bends
  bend_neg t ht := by
    classical
    rcases Finset.mem_union.mp (Finsupp.support_zipWith ht) with h | h
    · exact β.bend_neg t h
    · exact γ.bend_neg t h

@[simp]
theorem endpoint_prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    (β.prod γ).endpoint = (β.endpoint, γ.endpoint) := (rfl)

@[simp]
theorem direction_prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    (β.prod γ).direction = (β.direction, γ.direction) := (rfl)

/-- Every time has exactly the prescribed pair of direction increments. -/
@[simp]
theorem bends_prod_apply (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) (t : ℝ) :
    (β.prod γ).bends t = (β.bends t, γ.bends t) := (rfl)

variable [Module ℝ V] [Module ℝ W] [AddTorsor V P] [AddTorsor W Q]

/-- Projection recovers the first ray, even when its projection erases bends. -/
@[simp]
theorem map_fst_prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    (β.prod γ).map (AffineMap.fst : P × Q →ᵃ[ℝ] P) = β := by
  ext <;> simp

/-- Projection recovers the entire forgotten-coordinate history. -/
@[simp]
theorem map_snd_prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    (β.prod γ).map (AffineMap.snd : P × Q →ᵃ[ℝ] Q) = γ := by
  ext <;> simp

/-- A ray in a product is recovered from its two coordinate histories. -/
@[simp]
theorem prod_map_fst_map_snd (δ : FiniteAffineRay (V × W) (P × Q)) :
    (δ.map (AffineMap.fst : P × Q →ᵃ[ℝ] P)).prod (δ.map (AffineMap.snd : P × Q →ᵃ[ℝ] Q)) = δ := by
  ext <;> simp

/-- Rays in a product affine space are equivalent to pairs of finite ray histories. -/
def prodEquiv : FiniteAffineRay (V × W) (P × Q) ≃
    FiniteAffineRay V P × FiniteAffineRay W Q where
  toFun δ := (δ.map (AffineMap.fst : P × Q →ᵃ[ℝ] P), δ.map (AffineMap.snd : P × Q →ᵃ[ℝ] Q))
  invFun a := a.1.prod a.2
  left_inv := prod_map_fst_map_snd
  right_inv a := by simp

@[simp]
theorem prodEquiv_apply (δ : FiniteAffineRay (V × W) (P × Q)) :
    prodEquiv δ =
      (δ.map (AffineMap.fst : P × Q →ᵃ[ℝ] P),
        δ.map (AffineMap.snd : P × Q →ᵃ[ℝ] Q)) := (rfl)

@[simp]
theorem prodEquiv_symm_apply (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    prodEquiv.symm (β, γ) = β.prod γ := (rfl)

/-- The product integrates both coordinate histories at every time. -/
@[simp]
theorem prod_apply (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) (t : ℝ) :
    β.prod γ t = (β t, γ t) := by
  apply Prod.ext
  · simpa only [map_fst_prod, AffineMap.coe_fst, AffineMap.fst_linear,
    LinearMap.fst_apply] using (map_apply (β.prod γ) (AffineMap.fst : P × Q →ᵃ[ℝ] P) t).symm
  · simpa only [map_snd_prod, AffineMap.coe_snd, AffineMap.snd_linear,
    LinearMap.snd_apply] using (map_apply (β.prod γ) (AffineMap.snd : P × Q →ᵃ[ℝ] Q) t).symm

omit [Module ℝ V] [Module ℝ W] [AddTorsor V P] [AddTorsor W Q] in
@[simp]
theorem incomingDirection_prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    (β.prod γ).incomingDirection = (β.incomingDirection, γ.incomingDirection) := by
  classical
  simp only [incomingDirection_def, direction_prod]
  rw [Finsupp.sum_of_support_subset (β.prod γ).bends
      (s := β.bends.support ∪ γ.bends.support) (by
        intro b hb
        simpa only [Finset.mem_union, Finsupp.mem_support_iff, bends_prod_apply,
          ne_eq, Prod.mk_eq_zero, not_and_or] using hb) _ (by simp),
    Finsupp.sum_of_support_subset β.bends
      (s := β.bends.support ∪ γ.bends.support) Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset γ.bends
      (s := β.bends.support ∪ γ.bends.support) Finset.subset_union_right _ (by simp)]
  apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]

@[simp]
theorem incomingReference_prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) :
    (β.prod γ).incomingReference = (β.incomingReference, γ.incomingReference) := by
  apply Prod.ext
  · simpa only [map_fst_prod, AffineMap.coe_fst, AffineMap.fst_linear,
    LinearMap.fst_apply] using
      (incomingReference_map (β.prod γ) (AffineMap.fst : P × Q →ᵃ[ℝ] P)).symm
  · simpa only [map_snd_prod, AffineMap.coe_snd, AffineMap.snd_linear,
    LinearMap.snd_apply] using
      (incomingReference_map (β.prod γ) (AffineMap.snd : P × Q →ᵃ[ℝ] Q)).symm

omit [Module ℝ V] [Module ℝ W] [AddTorsor V P] [AddTorsor W Q] in
@[simp]
theorem directionAt_prod (β : FiniteAffineRay V P) (γ : FiniteAffineRay W Q) (t : ℝ) :
    (β.prod γ).directionAt t = (β.directionAt t, γ.directionAt t) := by
  classical
  simp only [directionAt_def, direction_prod]
  rw [Finsupp.sum_of_support_subset (β.prod γ).bends
      (s := β.bends.support ∪ γ.bends.support) (by
        intro b hb
        simpa only [Finset.mem_union, Finsupp.mem_support_iff, bends_prod_apply,
          ne_eq, Prod.mk_eq_zero, not_and_or] using hb) _ (by simp),
    Finsupp.sum_of_support_subset β.bends
      (s := β.bends.support ∪ γ.bends.support) Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset γ.bends
      (s := β.bends.support ∪ γ.bends.support) Finset.subset_union_right _ (by simp)]
  apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum, apply_ite]

/-- Given the forgotten endpoint, final direction and increments, there is exactly
one lift of the projected ray with those finite affine data. -/
theorem existsUnique_lift (β : FiniteAffineRay V P) (q : Q) (w : W)
    (b : ℝ →₀ W) (hb : ∀ t ∈ b.support, t < 0) :
    ∃! δ : FiniteAffineRay (V × W) (P × Q),
      δ.map (AffineMap.fst : P × Q →ᵃ[ℝ] P) = β ∧ δ.endpoint.2 = q ∧
        δ.direction.2 = w ∧ (∀ t, (δ.bends t).2 = b t) := by
  let γ : FiniteAffineRay W Q := ⟨q, w, b, hb⟩
  refine ⟨β.prod γ, by simp [γ], ?_⟩
  rintro δ ⟨hβ, hq, hw, hb⟩
  have hγ : δ.map (AffineMap.snd : P × Q →ᵃ[ℝ] Q) = γ := by
    ext
    · simpa [γ] using hq
    · simpa [γ] using hw
    · simpa [γ] using hb _
  rw [← prod_map_fst_map_snd δ, hβ, hγ]

end Mei.FiniteAffineRay
