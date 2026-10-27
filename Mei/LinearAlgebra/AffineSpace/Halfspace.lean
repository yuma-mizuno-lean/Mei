/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.Projection.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Half-space slices transverse to a boundary hyperplane

Intersect an affine subspace with a closed linear half-space through a point `p`.
In a subspace complementary to the boundary's tangent direction, this intersection
is exactly one inward ray based at `p`. The direction is normalized to have
functional value `-1`. This identifies the ray followed from a transverse test's
interior to its exit face. No topology or ambient dimension is required.

The normal coordinate is the restriction bijection
`LinearMap.bijective_domRestrict_inf_of_isCompl`; affine membership uses
`AffineSubspace.vsub_right_mem_direction_iff_mem`.
-/

public section

noncomputable section

namespace AffineSubspace

variable {K V P : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [AddTorsor V P]

/-- A half-space in an affine subspace cuts out one inward ray in a complement
to the boundary direction. The ray direction has functional value `-1`;
the equivalence characterizes every point of the slice, including its base. -/
theorem exists_transverse_halfspace_ray (A : AffineSubspace K P)
    (f : V →ₗ[K] K) {p : P} (hp : p ∈ A) (T : Submodule K V)
    (hf : f.domRestrict A.direction ≠ 0)
    (hcompl : IsCompl (A.direction ⊓ f.ker) T) :
    ∃ u ∈ A.direction ⊓ T, f u = -1 ∧
      ∀ z : P, (z -ᵥ p ∈ T ∧ z ∈ A ∧ f (z -ᵥ p) ≤ 0) ↔
        ∃ t : K, 0 ≤ t ∧ z = t • u +ᵥ p := by
  let e : ↥(A.direction ⊓ T) ≃ₗ[K] K := LinearEquiv.ofBijective _
    (f.bijective_domRestrict_inf_of_isCompl A.direction T
      (LinearMap.surjective hf) hcompl)
  -- The equivalence has the restricted functional as its forward map.
  have he (v : ↥(A.direction ⊓ T)) : e v = f v := (rfl)
  let u := e.symm (-1)
  have hu : f (u : V) = -1 := by
    exact e.apply_symm_apply (-1)
  refine ⟨u, u.property, hu, fun z => ?_⟩
  constructor
  · rintro ⟨hzT, hzA, hle⟩
    have hzU : z -ᵥ p ∈ A.direction :=
      (vsub_right_mem_direction_iff_mem hp z).mpr hzA
    let w : ↥(A.direction ⊓ T) := ⟨z -ᵥ p, hzU, hzT⟩
    have hw : w = (-(f (z -ᵥ p))) • u := by
      apply e.injective
      simp only [he, Submodule.coe_smul, map_smul, hu, smul_eq_mul, neg_mul_neg, mul_one]
      rfl
    refine ⟨-(f (z -ᵥ p)), neg_nonneg.mpr hle, ?_⟩
    have hv := congrArg (fun x : ↥(A.direction ⊓ T) => (x : V)) hw
    exact (eq_vadd_iff_vsub_eq _ _ _).mpr hv
  · rintro ⟨t, ht, rfl⟩
    refine ⟨by simpa only [vadd_vsub] using T.smul_mem t u.property.2, ?_, ?_⟩
    · have hm := A.vadd_mem_of_mem_direction (A.direction.smul_mem t u.property.1) hp
      exact hm
    · simp only [vadd_vsub, map_smul, hu, smul_eq_mul, mul_neg_one]
      exact neg_nonpos.mpr ht

end AffineSubspace
