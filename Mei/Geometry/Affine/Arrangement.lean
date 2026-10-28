/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Generic
public import Mei.Analysis.Convex.Sign
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Exceptional arrangements from affine conditions

The zero sets of the nonconstant members of a finite family of affine functionals
form an exceptional arrangement. Constant conditions are omitted, including the
identically zero condition. At a generic point, all signs are locally constant.
This turns finite affine inequalities into stable local membership tests, even
when some inequalities vanish identically.

We use Mathlib's affine-subspace preimages and the existing generic-locus and
open-sign-region APIs.
-/

public section

noncomputable section

open Set Filter Topology

namespace Mei.ExceptionalArrangement

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Finite ι]

/-- The arrangement of zero sets of the nonconstant affine conditions. Constant
conditions contribute no exception, regardless of their value. -/
def ofAffineForms (g : ι → V →ᵃ[ℝ] ℝ) : ExceptionalArrangement V := by
  classical
  letI := Fintype.ofFinite ι
  refine ⟨(Finset.univ.filter fun j => (g j).linear ≠ 0).image
    (fun j => (affineSpan ℝ ({0} : Set ℝ)).comap (g j)), ?_⟩
  intro S hS htop
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
  have hz (x : V) : g j x = 0 := by
    have hx : x ∈ (affineSpan ℝ ({0} : Set ℝ)).comap (g j) := by rw [htop]; trivial
    simpa using hx
  have heq : g j = AffineMap.const ℝ V 0 := by ext x; exact hz x
  exact (Finset.mem_filter.mp hj).2 (by rw [heq]; rfl)

/-- An exception is precisely the zero set of one nonconstant input condition. -/
@[simp]
theorem mem_exceptions_ofAffineForms (g : ι → V →ᵃ[ℝ] ℝ) (S : AffineSubspace ℝ V) :
    S ∈ (ofAffineForms g).exceptions ↔
      ∃ j, (g j).linear ≠ 0 ∧ (affineSpan ℝ ({0} : Set ℝ)).comap (g j) = S := by
  classical
  simp [ofAffineForms]

/-- Genericity ignores constant conditions and excludes exactly the zeros of
nonconstant conditions. -/
@[simp]
theorem isGeneric_ofAffineForms_iff (g : ι → V →ᵃ[ℝ] ℝ) (x : V) :
    (ofAffineForms g).IsGeneric x ↔ ∀ j, (g j).linear ≠ 0 → g j x ≠ 0 := by
  classical
  rw [isGeneric_iff]
  simp only [mem_exceptions_ofAffineForms, forall_exists_index, and_imp]
  simp

variable [TopologicalSpace V]

/-- All signs of a finite continuous affine family are simultaneously constant
near any generic point, including the signs of constant zero conditions. -/
theorem eventually_sign_eq_of_isGeneric (g : ι → V →ᴬ[ℝ] ℝ) {x : V}
    (hx : (ofAffineForms (fun j => (g j).toAffineMap)).IsGeneric x) :
    ∀ᶠ y in 𝓝 x, ∀ j, SignType.sign (g j y) = SignType.sign (g j x) := by
  rw [isGeneric_ofAffineForms_iff] at hx
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : (g j).toAffineMap.linear = 0
  · obtain ⟨c, hc⟩ := (g j).toAffineMap.linear_eq_zero_iff_exists_const.mp hj
    have heq (y : V) : g j y = c := congrArg (fun f : V →ᵃ[ℝ] ℝ => f y) hc
    exact Filter.Eventually.of_forall fun y => by rw [heq y, heq x]
  · exact ((isOpen_setOf_sign_eq (sign_ne_zero.mpr (hx j hj))).preimage
      (g j).continuous).mem_nhds rfl

end Mei.ExceptionalArrangement
