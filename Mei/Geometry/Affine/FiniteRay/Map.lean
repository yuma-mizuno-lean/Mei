/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Basic

/-!
# Affine images of finite bent rays

An affine map transports endpoints and direction increments. Realization and the
incoming affine data commute with this operation. Noninjective maps can erase
geometric bends; the remaining increments still have finite negative support.
In particular, coordinate projections of a bent ray are again finite bent rays.
-/

public noncomputable section

namespace Mei.FiniteAffineRay

variable {V W U P Q S : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
  [Module ℝ V] [Module ℝ W] [Module ℝ U]
  [AddTorsor V P] [AddTorsor W Q] [AddTorsor U S]

/-- Apply an affine map to a ray, including all its direction increments. -/
def map (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) : FiniteAffineRay W Q where
  endpoint := f β.endpoint
  direction := f.linear β.direction
  bends := β.bends.mapRange f.linear (map_zero _)
  bend_neg t ht := β.bend_neg t (Finsupp.support_mapRange ht)

@[simp]
theorem endpoint_map (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) :
    (β.map f).endpoint = f β.endpoint := (rfl)

@[simp]
theorem direction_map (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) :
    (β.map f).direction = f.linear β.direction := (rfl)

/-- The increment at every time is the image of the original increment. -/
@[simp]
theorem bends_map_apply (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) (t : ℝ) :
    (β.map f).bends t = f.linear (β.bends t) := (rfl)

/-- An affine map can remove bends but cannot introduce new bend times. -/
theorem support_bends_map_subset (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) :
    (β.map f).bends.support ⊆ β.bends.support := by
  exact Finsupp.support_mapRange (hf := map_zero _)

/-- An affine image is straight exactly when its linear part kills every increment. -/
@[simp]
theorem map_eq_straight_iff (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) :
    β.map f = straight (f β.endpoint) (f.linear β.direction) ↔
      ∀ t, f.linear (β.bends t) = 0 := by
  rw [← endpoint_map, ← direction_map, eq_straight_iff, Finsupp.ext_iff]
  simp only [bends_map_apply, Finsupp.zero_apply]

/-- An affine image is straight if its linear part kills every direction increment.
It suffices to check the finitely many actual bends. -/
theorem map_eq_straight (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q)
    (hf : ∀ t ∈ β.bends.support, f.linear (β.bends t) = 0) :
    β.map f = straight (f β.endpoint) (f.linear β.direction) := by
  apply (map_eq_straight_iff β f).mpr
  intro t
  by_cases ht : t ∈ β.bends.support
  · exact hf t ht
  · simp only [Finsupp.notMem_support_iff.mp ht, map_zero]

/-- Affine maps commute with the entire hinge realization. -/
@[simp]
theorem map_apply (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) (t : ℝ) :
    β.map f t = f (β t) := by
  rw [eval_def, eval_def, f.map_vadd]
  simp only [map, map_sub, map_smul, map_finsuppSum,
    Finsupp.sum_mapRange_index (fun _ => smul_zero _)]

/-- Incoming directions project even when some projected bends vanish. -/
@[simp]
theorem incomingDirection_map (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) :
    (β.map f).incomingDirection = f.linear β.incomingDirection := by
  simp only [incomingDirection_def, direction_map, map_add, map_finsuppSum]
  simp [map, Finsupp.sum_mapRange_index]

/-- Incoming reference positions transform affinely. -/
@[simp]
theorem incomingReference_map (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) :
    (β.map f).incomingReference = f β.incomingReference := by
  rw [incomingReference_def, incomingReference_def, f.map_vadd]
  simp only [map, map_finsuppSum, map_smul,
    Finsupp.sum_mapRange_index (fun _ => smul_zero _)]

/-- The direction on each incoming interval transforms by the linear part. -/
@[simp]
theorem directionAt_map (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) (t : ℝ) :
    (β.map f).directionAt t = f.linear (β.directionAt t) := by
  simp only [directionAt_def, direction_map, map_add, map_finsuppSum]
  simp [map, Finsupp.sum_mapRange_index, apply_ite]

@[simp]
theorem map_id (β : FiniteAffineRay V P) : β.map (AffineMap.id ℝ P) = β := by
  ext <;> simp

/-- Successive affine images agree with the image under their composite. -/
@[simp]
theorem map_map (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] Q) (g : Q →ᵃ[ℝ] S) :
    (β.map f).map g = β.map (g.comp f) := by
  ext <;> simp

end Mei.FiniteAffineRay
