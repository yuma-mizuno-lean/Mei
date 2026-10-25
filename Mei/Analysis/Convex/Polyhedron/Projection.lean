/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.FourierMotzkin
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

/-!
# One-parameter projections of convex polyhedra

Eliminating a nonnegative real parameter produces a finite family of continuous
affine inequalities. The resulting rows are the original rows with nonnegative
parameter coefficient and the pairwise resultants of a negative and a positive
coefficient. The family is explicit and uses no division, so additional scalar
properties of its rows can be checked directly.

As an application, adding a negative ray to a convex polyhedron preserves
polyhedrality without any transversality or boundedness assumption.
-/

public section

namespace Mei.Convex

/-- The rows remaining after elimination of a nonnegative parameter: rows with
nonnegative coefficient, and pairs of a negative with a positive coefficient. -/
@[expose]
def NonnegElimIndex {ι : Type*} (a : ι → ℝ) :=
  {i : ι // 0 ≤ a i} ⊕ ({i : ι // a i < 0} × {i : ι // 0 < a i})

/-- Eliminating one parameter from a finite family leaves a finite family. -/
instance {ι : Type*} [Finite ι] (a : ι → ℝ) : Finite (NonnegElimIndex a) := by
  unfold NonnegElimIndex
  infer_instance

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The explicit continuous affine rows obtained by eliminating `t ≥ 0` from
`g i y + a i * t ≤ 0`. Pair rows use only multiplication and subtraction. -/
@[expose]
def nonnegElimFamily (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ) :
    NonnegElimIndex a → (V →ᴬ[ℝ] ℝ)
  | .inl i => g i.val
  | .inr (i, j) => a j.val • g i.val - a i.val • g j.val

/-- A retained single row evaluates as its original affine functional. -/
@[simp]
theorem nonnegElimFamily_single_apply (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ)
    (i : {i : ι // 0 ≤ a i}) (y : V) :
    nonnegElimFamily g a (.inl i) y = g i.val y := rfl

/-- A paired resultant evaluates as the division-free linear combination of its rows. -/
@[simp]
theorem nonnegElimFamily_pair_apply (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ)
    (i : {i : ι // a i < 0}) (j : {i : ι // 0 < a i}) (y : V) :
    nonnegElimFamily g a (.inr (i, j)) y = a j.val * g i.val y - a i.val * g j.val y :=
  rfl

/-- Membership in the one-parameter projection is given by the explicit finite
family of resultant affine inequalities. -/
theorem exists_nonneg_affine_le_iff [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {a : ι → ℝ} {y : V} :
    (∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0) ↔
      ∀ k : NonnegElimIndex a, nonnegElimFamily g a k y ≤ 0 := by
  have he : (∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0) ↔
      ∃ t : ℝ, 0 ≤ t ∧ ∀ i, a i * t ≤ -g i y := by
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨t, ht, fun i => by linarith [h i]⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨t, ht, fun i => by linarith [h i]⟩
  rw [he, Mei.exists_nonneg_mul_le_iff]
  constructor
  · rintro ⟨hsingle, hpair⟩ k
    rcases k with i | ⟨i, j⟩
    · exact neg_nonneg.mp (hsingle i.val i.property)
    · rw [nonnegElimFamily_pair_apply]
      have h := hpair i.val j.val i.property j.property
      simp only [mul_neg] at h
      linarith
  · intro h
    constructor
    · intro i hi
      exact neg_nonneg.mpr (h (.inl ⟨i, hi⟩))
    · intro i j hi hj
      have hp := h (.inr (⟨i, hi⟩, ⟨j, hj⟩))
      rw [nonnegElimFamily_pair_apply] at hp
      simp only [mul_neg]
      linarith

/-- An explicit presentation of a nonnegative one-parameter projection. -/
theorem setOf_exists_nonneg_affine_le_eq [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ) :
    {y : V | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0} =
      {y : V | ∀ k : NonnegElimIndex a, nonnegElimFamily g a k y ≤ 0} := by
  ext y
  exact exists_nonneg_affine_le_iff

/-- Convex polyhedrality is preserved by elimination of a nonnegative parameter. -/
theorem isConvexPolyhedron_setOf_exists_nonneg_affine_le [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (a : ι → ℝ) :
    TauCeti.IsConvexPolyhedron {y : V | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i y + a i * t ≤ 0} := by
  rw [setOf_exists_nonneg_affine_le_eq]
  exact TauCeti.isConvexPolyhedron_setOf_forall _

/-- Evaluation of a continuous affine functional along an affine ray. -/
theorem continuousAffineMap_apply_add_smul (g : V →ᴬ[ℝ] ℝ) (y n : V) (t : ℝ) :
    g (y + t • n) = g y + g.linear n * t := by
  rw [add_comm y]
  have h := g.map_vadd' y (t • n)
  simpa only [vadd_eq_add, map_smul, smul_eq_mul, mul_comm, add_comm,
    AffineMap.toFun_eq_coe, ContinuousAffineMap.coe_toAffineMap] using h

/-- The resultant presentation for adding a negative ray to a finite family of
closed affine halfspaces. The parameter slopes are the linear parts evaluated at `n`. -/
theorem setOf_exists_nonneg_add_smul_forall_le_eq [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (n : V) :
    {y : V | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i (y + t • n) ≤ 0} =
      {y : V | ∀ k : NonnegElimIndex (fun i => (g i).linear n),
        nonnegElimFamily g (fun i => (g i).linear n) k y ≤ 0} := by
  simp_rw [continuousAffineMap_apply_add_smul]
  exact setOf_exists_nonneg_affine_le_eq g (fun i => (g i).linear n)

/-- Adding a negative ray preserves convex polyhedrality, including tangent
sweeps and arbitrary unbounded polyhedra. -/
theorem isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem {P : Set V}
    (hP : TauCeti.IsConvexPolyhedron P) (n : V) :
    TauCeti.IsConvexPolyhedron {y : V | ∃ t : ℝ, 0 ≤ t ∧ y + t • n ∈ P} := by
  obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  change TauCeti.IsConvexPolyhedron {y : V | ∃ t : ℝ, 0 ≤ t ∧ ∀ i, g i (y + t • n) ≤ 0}
  rw [setOf_exists_nonneg_add_smul_forall_le_eq]
  exact TauCeti.isConvexPolyhedron_setOf_forall _

end Mei.Convex
