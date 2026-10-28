/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.IndexNSmul
public import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# Singular maps between integer lattices

A map between finite free integer modules of equal rank has image of index zero exactly
when it is singular. This complements the determinant formula for injective maps and
allows index comparisons to include singular maps.
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

end LinearMap
