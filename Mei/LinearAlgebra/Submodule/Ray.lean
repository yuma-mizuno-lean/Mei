/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Transverse slices of linear half-spaces

A complement to a hyperplane in a subspace cuts either closed half-space in a
single ray. This describes the one-sided slice of a polyhedral facet in a
transverse plane. The construction uses Mathlib's complementary decomposition
`Submodule.existsUnique_add_of_isCompl` and the dimension formula
`Submodule.finrank_sup_add_finrank_inf_eq`.
-/

public section

open Set Module

namespace Submodule

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V]

/-- A complement to a codimension-one subspace of `U` meets a nontrivial
closed half-space of `U` in a ray, with a strictly inward generator. -/
theorem exists_neg_ray_of_isCompl (U W T : Submodule K V) [FiniteDimensional K U]
    (hWU : W ≤ U)
    (hdim : finrank K W + 1 = finrank K U) (hT : IsCompl W T)
    (f : V →ₗ[K] K) (hfW : W ≤ f.ker) (hneg : ∃ u ∈ U, f u < 0) :
    ∃ v ∈ U ⊓ T, f v < 0 ∧ ∀ x ∈ T,
      (x ∈ U ∧ f x ≤ 0 ↔ ∃ t : K, 0 ≤ t ∧ t • v = x) := by
  obtain ⟨u, hu, hfu⟩ := hneg
  have huW : u ∉ W := fun hw => hfu.ne (hfW hw)
  have : FiniteDimensional K W := finiteDimensional_of_le hWU
  have hu0 : u ≠ 0 := by rintro rfl; exact huW W.zero_mem
  have hdimSpan := finrank_sup_add_finrank_inf_eq W (K ∙ u)
  rw [(disjoint_span_singleton_of_notMem huW).eq_bot, finrank_bot, add_zero,
    finrank_span_singleton hu0] at hdimSpan
  have hspan : W ⊔ K ∙ u = U :=
    eq_of_le_of_finrank_eq (sup_le hWU (span_le.mpr (singleton_subset_iff.mpr hu)))
      (hdimSpan.trans hdim)
  obtain ⟨a, v, hav, -⟩ := W.existsUnique_add_of_isCompl hT u
  have hvU : (v : V) ∈ U := by
    have he : (v : V) = u - a := by rw [← hav]; simp
    rw [he]
    exact U.sub_mem hu (hWU a.property)
  have hfv : f v < 0 := by
    have hfa : f (a : V) = 0 := hfW a.property
    have he := congrArg f hav
    simp only [map_add, hfa, zero_add] at he
    exact he.symm ▸ hfu
  refine ⟨v, ⟨hvU, v.property⟩, hfv, fun x hxT => ⟨?_, ?_⟩⟩
  · rintro ⟨hxU, hfx⟩
    rw [← hspan] at hxU
    obtain ⟨b, hb, z, hz, hbx⟩ := mem_sup.mp hxU
    obtain ⟨t, rfl⟩ := mem_span_singleton.mp hz
    have hx : x = t • (v : V) := by
      have hw : x - t • (v : V) ∈ W := by
        have he : x - t • (v : V) = b + t • (a : V) := by
          rw [← hbx, ← hav]
          module
        rw [he]
        exact W.add_mem hb (W.smul_mem t a.property)
      have ht : x - t • (v : V) ∈ T := T.sub_mem hxT (T.smul_mem t v.property)
      exact sub_eq_zero.mp (Submodule.disjoint_def.mp hT.disjoint _ hw ht)
    refine ⟨t, ?_, hx.symm⟩
    have he : f x = t * f v := by rw [hx, map_smul, smul_eq_mul]
    rw [he] at hfx
    exact nonneg_of_mul_nonpos_left hfx hfv
  · rintro ⟨t, ht, rfl⟩
    exact ⟨U.smul_mem t hvU, by simpa using mul_nonpos_of_nonneg_of_nonpos ht hfv.le⟩

end Submodule
