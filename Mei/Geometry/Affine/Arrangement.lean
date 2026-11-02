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
identically zero condition. When the affine conditions are continuous, all signs
are locally constant at a generic point. This turns finite continuous affine
inequalities into stable local membership tests, even when some inequalities
vanish identically.

A finite arrangement has an open generic locus, and a countable family of finite
arrangements only has a dense common generic locus. The family `{x = 1/(j+1)}` of the
line is the sharp example: `0` is generic for every member and every finite subfamily is
generic on a neighbourhood of `0`, but no neighbourhood of `0` is generic for the whole
family. Local uniformity is therefore an extra condition in the countable case.

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


section LocalUniformity

/-- The exceptional arrangement of a single point `c` of the real line, given by the
nonconstant condition `x ↦ x - c`. -/
noncomputable def ofPoint (c : ℝ) : ExceptionalArrangement ℝ :=
  ofAffineForms fun _ : Unit =>
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap - AffineMap.const ℝ ℝ c

/-- A point is generic for the arrangement of a single point exactly when it is a
different point. -/
@[simp]
theorem isGeneric_ofPoint_iff (c x : ℝ) : (ofPoint c).IsGeneric x ↔ x ≠ c := by
  rw [ofPoint, isGeneric_ofAffineForms_iff]
  have hlin : ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap -
      AffineMap.const ℝ ℝ c).linear ≠ 0 := by
    intro hzero
    have h1 : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) = 0 := by simpa using hzero
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using LinearMap.congr_fun h1 1)
  constructor
  · intro h hxc
    exact h () hlin (by simp [hxc])
  · intro hx j hj
    simpa using sub_ne_zero.mpr hx

/-- The arrangement `{x = 1/(j+1)}` of the line. -/
noncomputable def ofInvSucc (j : ℕ) : ExceptionalArrangement ℝ :=
  ofPoint ((j + 1 : ℝ)⁻¹)

/-- The origin is a common generic point of the family `{x = 1/(j+1)}`. -/
@[simp]
theorem isGeneric_zero_ofInvSucc (j : ℕ) : (ofInvSucc j).IsGeneric 0 := by
  rw [ofInvSucc, isGeneric_ofPoint_iff]
  exact (inv_ne_zero (by positivity : (j : ℝ) + 1 ≠ 0)).symm

/-- No neighbourhood of the origin is contained in the common generic locus of the
family `{x = 1/(j+1)}`: the common generic locus is dense but not a neighbourhood of
any of its points. -/
theorem not_exists_nhds_forall_isGeneric_ofInvSucc :
    ¬ ∃ U ∈ 𝓝 (0 : ℝ), ∀ y ∈ U, ∀ j : ℕ, (ofInvSucc j).IsGeneric y := by
  rintro ⟨U, hU, hgen⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  have hmem : ((j + 1 : ℝ)⁻¹) ∈ U := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    simpa only [one_div] using hj
  have hnot := hgen _ hmem j
  rw [ofInvSucc, isGeneric_ofPoint_iff] at hnot
  exact hnot rfl

/-- Every finite subfamily of `{x = 1/(j+1)}` is generic on a neighbourhood of the
origin, so only the countable family fails to be locally uniform. -/
theorem exists_mem_nhds_forall_isGeneric_ofInvSucc_finset (s : Finset ℕ) :
    ∃ U ∈ 𝓝 (0 : ℝ), ∀ y ∈ U, ∀ j ∈ s, (ofInvSucc j).IsGeneric y := by
  have hopen : IsOpen {y : ℝ | ∀ j ∈ s, (ofInvSucc j).IsGeneric y} := by
    have h : IsOpen (⋂ j ∈ s, {y : ℝ | (ofInvSucc j).IsGeneric y}) :=
      isOpen_biInter_finset fun j _ => isOpen_isGeneric _
    simpa only [Set.ofPred_forall, Set.mem_iInter] using h
  exact ⟨_, hopen.mem_nhds fun j _ => isGeneric_zero_ofInvSucc j, fun _ hy => hy⟩

end LocalUniformity

end Mei.ExceptionalArrangement
