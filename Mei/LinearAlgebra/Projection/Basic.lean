/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Restricting a surjection to a transverse submodule

A linear map surjective on a submodule `U` becomes bijective on `U ⊓ T`
when `T` complements the kernel inside `U` in the ambient module. This gives
coordinates on transverse slices without dimension or freeness assumptions.
The proof uses Mathlib's `LinearMap.injective_domRestrict_iff`,
`Submodule.mem_sup` and the two complement laws.
-/

public section

namespace LinearMap

variable {R V W : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- A map surjective on `U` restricts to a bijection on `U ⊓ T` if `T`
complements its kernel inside `U` in the ambient module. -/
theorem bijective_domRestrict_inf_of_isCompl (f : V →ₗ[R] W)
    (U T : Submodule R V) (hsurj : Function.Surjective (f.domRestrict U))
    (hcompl : IsCompl (U ⊓ f.ker) T) :
    Function.Bijective (f.domRestrict (U ⊓ T)) := by
  constructor
  · apply injective_domRestrict_iff.mpr
    rw [disjoint_iff]
    simpa only [inf_assoc, inf_comm, inf_left_comm] using hcompl.inf_eq_bot
  · intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hxsum : (x : V) ∈ (U ⊓ f.ker) ⊔ T := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨w, hw, t, ht, he⟩ := Submodule.mem_sup.mp hxsum
    have htU : t ∈ U := by
      rw [← add_sub_cancel_left w t, he]
      exact U.sub_mem x.property hw.1
    refine ⟨⟨t, htU, ht⟩, ?_⟩
    have hwt := congrArg f he
    simpa only [domRestrict_apply, map_add, mem_ker.mp hw.2, zero_add] using hwt.trans hx

end LinearMap
