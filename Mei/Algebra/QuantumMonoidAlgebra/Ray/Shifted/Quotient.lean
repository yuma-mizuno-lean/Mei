/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Nilpotent

/-!
# Quantum ray actions on finite shifted quotients

Unit ray series act by linear automorphisms on the original finite relative
quotients. Projection intertwines these actions with the completed actions,
and all quotient transitions intertwine them. Their differences from the identity
are the previously constructed nilpotent quotient endomorphisms.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (n : d.monoid) (hn : 0 < d.degree n) (p : Γ)

local notation "S" => d.shiftedFiltration (grade q β) p

private def quotientRayMap (H : (PowerSeries R)ˣ) (k : ℕ) :
    Module.End R ((S).quotient k) :=
  LinearMap.id + shiftedRayQuotientDifference q β d n hn p H k

private theorem quotientRayMap_projection (H : (PowerSeries R)ˣ) (k : ℕ)
    (a : (S).completion) :
    quotientRayMap q β d n hn p H k ((S).projection k a) =
      (S).projection k (shiftedRayAction q β d n hn p H a) := by
  simp only [quotientRayMap, LinearMap.add_apply, LinearMap.id_apply,
    shiftedRayQuotientDifference_projection, map_sub]
  abel

private def quotientRayEquiv (H : (PowerSeries R)ˣ) (k : ℕ) :
    (S).quotient k ≃ₗ[R] (S).quotient k where
  __ := quotientRayMap q β d n hn p H k
  invFun := quotientRayMap q β d n hn p (H⁻¹) k
  left_inv a := by
    obtain ⟨b, rfl⟩ := (S).projection_surjective k a
    simp only [LinearMap.toFun_eq_coe, quotientRayMap_projection, shiftedRayAction_inv,
      LinearEquiv.symm_apply_apply]
  right_inv a := by
    obtain ⟨b, rfl⟩ := (S).projection_surjective k a
    simp only [LinearMap.toFun_eq_coe, quotientRayMap_projection, shiftedRayAction_inv,
      LinearEquiv.apply_symm_apply]

private theorem quotientRayEquiv_projection (H : (PowerSeries R)ˣ) (k : ℕ)
    (a : (S).completion) :
    quotientRayEquiv q β d n hn p H k ((S).projection k a) =
      (S).projection k (shiftedRayAction q β d n hn p H a) :=
  quotientRayMap_projection q β d n hn p H k a

/-- Unit ray series act on each original finite relative coefficient quotient. -/
def shiftedRayQuotientAction (k : ℕ) :
    (PowerSeries R)ˣ →* ((S).quotient k ≃ₗ[R] (S).quotient k) where
  toFun H := quotientRayEquiv q β d n hn p H k
  map_one' := by
    ext a
    obtain ⟨b, rfl⟩ := (S).projection_surjective k a
    simp only [quotientRayEquiv_projection, map_one]
    -- LinearEquiv.refl applies as the identity; both sides are this same projection.
    rfl
  map_mul' H K := by
    ext a
    obtain ⟨b, rfl⟩ := (S).projection_surjective k a
    simp only [quotientRayEquiv_projection, map_mul, LinearEquiv.mul_apply]

/-- Projection intertwines the completed and finite ray actions. -/
@[simp]
theorem shiftedRayQuotientAction_projection (k : ℕ) (H : (PowerSeries R)ˣ)
    (a : (S).completion) :
    shiftedRayQuotientAction q β d n hn p k H ((S).projection k a) =
      (S).projection k (shiftedRayAction q β d n hn p H a) :=
  quotientRayEquiv_projection q β d n hn p H k a

/-- The inverse series reverses the finite ray action. -/
@[simp]
theorem shiftedRayQuotientAction_inv (k : ℕ) (H : (PowerSeries R)ˣ) :
    shiftedRayQuotientAction q β d n hn p k (H⁻¹) =
      (shiftedRayQuotientAction q β d n hn p k H).symm :=
  map_inv (shiftedRayQuotientAction q β d n hn p k) H

/-- Finite ray actions commute with every relative quotient transition. -/
@[simp]
theorem transition_shiftedRayQuotientAction (H : (PowerSeries R)ˣ)
    {k l : ℕ} (hkl : k ≤ l) (a : (S).quotient l) :
    (S).transition hkl (shiftedRayQuotientAction q β d n hn p l H a) =
      shiftedRayQuotientAction q β d n hn p k H ((S).transition hkl a) := by
  obtain ⟨b, rfl⟩ := (S).projection_surjective l a
  simp only [shiftedRayQuotientAction_projection, ModuleFiltration.transition_projection]

/-- The finite action differs from the identity by its nilpotent quotient endomorphism. -/
theorem shiftedRayQuotientAction_sub_id (k : ℕ) (H : (PowerSeries R)ˣ) :
    (shiftedRayQuotientAction q β d n hn p k H).toLinearMap - LinearMap.id =
      shiftedRayQuotientDifference q β d n hn p H k :=
  add_sub_cancel_left _ _

/-- Every finite ray action is unipotent, with the explicit relative-order bound. -/
theorem shiftedRayQuotientAction_sub_id_pow_eq_zero (k : ℕ) (H : (PowerSeries R)ˣ) :
    ((shiftedRayQuotientAction q β d n hn p k H).toLinearMap - LinearMap.id) ^
        (k + 1) = 0 := by
  rw [shiftedRayQuotientAction_sub_id]
  exact shiftedRayQuotientDifference_pow_eq_zero q β d n hn p H k

end Mei.QuantumMonoidAlgebra
