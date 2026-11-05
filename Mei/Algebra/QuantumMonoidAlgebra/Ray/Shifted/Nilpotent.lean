/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Order
public import Mei.LinearAlgebra.ModuleFiltration.Nilpotent

/-!
# Finite-order unipotence of shifted quantum ray actions

The difference between a ray action and the identity raises relative order.
It therefore induces a nilpotent endomorphism on every finite relative quotient:
the `(k + 1)`st power vanishes at order `k`. These endomorphisms act on the original
finite coefficient quotients, identified with quotients of the completed module
by the canonical projection. No nilpotence of the full completed endomorphism
is asserted.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (n : d.monoid) (hn : 0 < d.degree n) (p : Γ)

local notation "S" => d.shiftedFiltration (grade q β) p

/-- The difference of the completed shifted ray action and the identity. -/
abbrev shiftedRayDifference (H : (PowerSeries R)ˣ) : Module.End R (S).completion :=
  (shiftedRayAction q β d n hn p H).toLinearMap - LinearMap.id

/-- Applying the difference endomorphism subtracts the original coefficient. -/
@[simp]
theorem shiftedRayDifference_apply (H : (PowerSeries R)ˣ) (a : (S).completion) :
    shiftedRayDifference q β d n hn p H a = shiftedRayAction q β d n hn p H a - a := by
  simp only [shiftedRayDifference, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]

private theorem shiftedRayDifference_raises (H : (PowerSeries R)ˣ) (k : ℕ) :
    (S).completedFiltration.submodule k ≤
      ((S).completedFiltration.submodule (k + 1)).comap
        (shiftedRayDifference q β d n hn p H) := by
  intro a ha
  exact shiftedRayAction_sub_mem q β d n hn p H k ha

/-- The action-minus-identity endomorphism on the original finite shifted quotient. -/
def shiftedRayQuotientDifference (H : (PowerSeries R)ˣ) (k : ℕ) :
    Module.End R ((S).quotient k) :=
  ((S).completedQuotientEquiv k).conjRingEquiv
    ((S).completedFiltration.quotientRaisingEnd
      (shiftedRayDifference q β d n hn p H)
      (shiftedRayDifference_raises q β d n hn p H) k)

/-- Powers on the finite quotient are projections of the completed difference powers. -/
theorem shiftedRayQuotientDifference_pow_projection (H : (PowerSeries R)ˣ)
    (k j : ℕ) (a : (S).completion) :
    (shiftedRayQuotientDifference q β d n hn p H k ^ j) ((S).projection k a) =
      (S).projection k ((shiftedRayDifference q β d n hn p H ^ j) a) := by
  simp only [shiftedRayQuotientDifference, ← map_pow,
    ← ModuleFiltration.completedQuotientEquiv_mk, LinearEquiv.conjRingEquiv_apply_apply,
    LinearEquiv.symm_apply_apply, ModuleFiltration.quotientRaisingEnd_pow_mk]

/-- The finite endomorphism is exactly the projected action minus the identity. -/
@[simp]
theorem shiftedRayQuotientDifference_projection (H : (PowerSeries R)ˣ)
    (k : ℕ) (a : (S).completion) :
    shiftedRayQuotientDifference q β d n hn p H k ((S).projection k a) =
      (S).projection k (shiftedRayAction q β d n hn p H a - a) := by
  simpa only [pow_one, shiftedRayDifference_apply] using
    shiftedRayQuotientDifference_pow_projection q β d n hn p H k 1 a

/-- The inverse series gives the projected inverse action minus the identity. -/
theorem shiftedRayQuotientDifference_inv_projection (H : (PowerSeries R)ˣ)
    (k : ℕ) (a : (S).completion) :
    shiftedRayQuotientDifference q β d n hn p (H⁻¹) k ((S).projection k a) =
      (S).projection k ((shiftedRayAction q β d n hn p H).symm a - a) := by
  simpa only [shiftedRayAction_inv] using
    shiftedRayQuotientDifference_projection q β d n hn p (H⁻¹) k a

/-- On the order-`k` quotient, `k + 1` differences always vanish. -/
theorem shiftedRayQuotientDifference_pow_eq_zero (H : (PowerSeries R)ˣ) (k : ℕ) :
    shiftedRayQuotientDifference q β d n hn p H k ^ (k + 1) = 0 := by
  have h := congrArg ((S).completedQuotientEquiv k).conjRingEquiv
    ((S).completedFiltration.quotientRaisingEnd_pow_eq_zero
      (shiftedRayDifference q β d n hn p H)
      (shiftedRayDifference_raises q β d n hn p H) k)
  simpa only [map_pow, map_zero, shiftedRayQuotientDifference] using h

/-- Every finite shifted ray difference is nilpotent. -/
theorem isNilpotent_shiftedRayQuotientDifference (H : (PowerSeries R)ˣ) (k : ℕ) :
    IsNilpotent (shiftedRayQuotientDifference q β d n hn p H k) :=
  ⟨k + 1, shiftedRayQuotientDifference_pow_eq_zero q β d n hn p H k⟩

/-- The finite differences commute with all relative quotient transitions. -/
@[simp]
theorem transition_shiftedRayQuotientDifference (H : (PowerSeries R)ˣ)
    {k l : ℕ} (hkl : k ≤ l) (a : (S).quotient l) :
    (S).transition hkl (shiftedRayQuotientDifference q β d n hn p H l a) =
      shiftedRayQuotientDifference q β d n hn p H k ((S).transition hkl a) := by
  obtain ⟨b, rfl⟩ := (S).projection_surjective l a
  simp only [shiftedRayQuotientDifference_projection, ModuleFiltration.transition_projection]

end Mei.QuantumMonoidAlgebra
