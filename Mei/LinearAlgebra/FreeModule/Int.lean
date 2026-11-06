/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.IndexNSmul
public import Mei.LinearAlgebra.Dual.Basis
public import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# Singular maps between integer lattices

A map between finite free integer modules of equal rank has image of index zero exactly
when it is singular. This complements the determinant formula for injective maps and
allows index comparisons to include singular maps.

An injective map `f : M → N` from a finite free integer module to a free one has a left
inverse up to a nonzero natural factor `c`: some `g : N → M` satisfies `g ∘ f = c • id`
(`LinearMap.exists_comp_eq_nsmul_id_of_injective_left`). Over `ℚ` this is a left inverse
`c⁻¹ • g` of `f`.
-/

public section

namespace LinearMap

open Module

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module.Free ℤ M] [Module.Finite ℤ M]
  [Module.Free ℤ N] [Module.Finite ℤ N]

/-- A map between finite free integer modules of equal rank has image of index zero
exactly when it is not injective. -/
theorem index_range_eq_zero_iff {f : M →ₗ[ℤ] N} (hrank : finrank ℤ M = finrank ℤ N) :
    (range f).toAddSubgroup.index = 0 ↔ ¬Function.Injective f := by
  contrapose!
  constructor
  · intro h
    have : (range f).toAddSubgroup.FiniteIndex := ⟨h⟩
    have hrange : finrank ℤ (range f) = finrank ℤ N :=
      AddSubgroup.finrank_eq_of_finiteIndex (range f).toAddSubgroup
    exact (injective_rangeRestrict_iff f).mp
      (OrzechProperty.bijective_of_surjective_of_finrank_le f.rangeRestrict
        f.surjective_rangeRestrict (hrank.trans hrange.symm).le).injective
  · intro hf
    have : Finite (N ⧸ range f) := Submodule.finiteQuotientOfFreeOfRankEq _
      ((finrank_range_of_inj hf).trans hrank)
    have : Finite (N ⧸ (range f).toAddSubgroup) := ‹Finite (N ⧸ range f)›
    exact AddSubgroup.index_ne_zero_of_finite

omit [Module.Finite ℤ N] in
/-- An injective map from a finite free integer module to a free integer module has a left
inverse up to a nonzero natural factor. The ranks may differ. -/
theorem exists_comp_eq_nsmul_id_of_injective_left {f : M →ₗ[ℤ] N} (hf : Function.Injective f) :
    ∃ c : ℕ, c ≠ 0 ∧ ∃ g : N →ₗ[ℤ] M, g ∘ₗ f = c • LinearMap.id := by
  classical
  let bM := Module.Free.chooseBasis ℤ M
  let bN := Module.Free.chooseBasis ℤ N
  -- The Gram map of the coordinate pairing on `N`, pulled back along `f`, is an injective
  -- endomorphism of `M`, which is invertible up to a nonzero factor.
  let p : N →ₗ[ℤ] M := bM.toDualEquiv.symm.toLinearMap ∘ₗ Module.Dual.transpose f ∘ₗ bN.toDual
  have hp : Function.Injective (p ∘ₗ f) := fun x y hxy => by
    have h : bN.toDual (f (x - y)) (f (x - y)) = 0 := by
      have := congrArg bM.toDualEquiv hxy
      simpa [p, map_sub, Module.Dual.transpose_apply] using
        congrArg (fun φ => φ (x - y)) (sub_eq_zero.mpr this)
    exact sub_eq_zero.mp (hf ((bN.toDual_self_eq_zero_iff.mp h).trans (map_zero f).symm))
  obtain ⟨c, hc, g, -, hg⟩ := exists_comp_eq_nsmul_id_of_injective hp rfl
  exact ⟨c, hc, g ∘ₗ p, by rw [LinearMap.comp_assoc, hg]⟩

end LinearMap
