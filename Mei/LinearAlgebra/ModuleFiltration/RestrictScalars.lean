/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Restriction of scalars in filtered module completions

Restricting scalars in a module filtration preserves the quotient tower and its
compatible families. The resulting linear equivalence of completions commutes
with quotient projections, the canonical map, and compatible linear lifts. It
also identifies the induced filtrations. Thus completed coefficient modules can
change their scalar ring without changing their finite-order values.

The finite-order comparisons are Mathlib's
`Submodule.Quotient.restrictScalarsEquiv`; `LinearEquiv.piCongrRight` and
`LinearEquiv.ofSubmodules` restrict their product to compatible families.
No freeness, flatness or separatedness is required.
-/

public section

namespace Mei.ModuleFiltration

section Semiring

variable (R : Type*) {S M : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module S M] [Module R M] [SMul R S] [IsScalarTower R S M]
  (F : ModuleFiltration S M)

/-- Restrict the scalars in every term of a module filtration. -/
abbrev restrictScalars : ModuleFiltration R M where
  submodule k := (F.submodule k).restrictScalars R
  antitone := fun _ _ h => Submodule.restrictScalars_mono R (F.antitone h)
  zero_eq_top := by simp

@[simp]
lemma restrictScalars_submodule (k : ℕ) :
    (F.restrictScalars R).submodule k = (F.submodule k).restrictScalars R :=
  (rfl)

@[simp]
lemma restrictScalars_self : F.restrictScalars S = F := by
  ext k
  simp

end Semiring

section Ring

variable (R : Type*) {S M : Type*} [Ring R] [Ring S]
  [AddCommGroup M] [Module S M] [Module R M] [SMul R S] [IsScalarTower R S M]
  (F : ModuleFiltration S M)

/-- The finite-order scalar comparison commutes with the tower transitions. -/
@[simp]
lemma restrictScalarsEquiv_transition {k l : ℕ} (h : k ≤ l)
    (x : (F.restrictScalars R).quotient l) :
    Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))
        ((F.restrictScalars R).transition h x) =
      F.transition h (Submodule.Quotient.restrictScalarsEquiv R
        (F.submodule (l + 1)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

/-- The inverse finite-order comparison also commutes with transitions. -/
@[simp]
lemma restrictScalarsEquiv_symm_transition {k l : ℕ} (h : k ≤ l)
    (x : F.quotient l) :
    (Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))).symm
        (F.transition h x) =
      (F.restrictScalars R).transition h
        ((Submodule.Quotient.restrictScalarsEquiv R (F.submodule (l + 1))).symm x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

/-- Completing after scalar restriction gives the restriction of the completed module. -/
def completionRestrictScalarsEquiv :
    (F.restrictScalars R).completion ≃ₗ[R] F.completion := by
  let e := LinearEquiv.piCongrRight fun k : ℕᵒᵖ =>
    Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k.unop + 1))
  exact e.ofSubmodules (F.restrictScalars R).completionSubmodule
    (F.completionSubmodule.restrictScalars R) (by
      ext x
      simp only [Submodule.mem_map_equiv, Submodule.restrictScalars_mem,
        mem_completionSubmodule_iff, e, LinearEquiv.piCongrRight_symm,
        LinearEquiv.piCongrRight_apply, ← restrictScalarsEquiv_symm_transition,
        EmbeddingLike.apply_eq_iff_eq])

/-- The completed comparison acts by the finite-order quotient comparisons. -/
@[simp]
lemma projection_completionRestrictScalarsEquiv
    (x : (F.restrictScalars R).completion) (k : ℕ) :
    F.projection k (F.completionRestrictScalarsEquiv R x) =
      Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))
        ((F.restrictScalars R).projection k x) := by
  rw [F.projection_mk (F.completionRestrictScalarsEquiv R x).val
    (F.completionRestrictScalarsEquiv R x).property k,
    (F.restrictScalars R).projection_mk x.val x.property k]
  exact congrFun (LinearEquiv.ofSubmodules_apply _ _ x) (Opposite.op k)

/-- The inverse completed comparison acts by the inverse quotient comparisons. -/
@[simp]
lemma projection_completionRestrictScalarsEquiv_symm (x : F.completion) (k : ℕ) :
    (F.restrictScalars R).projection k ((F.completionRestrictScalarsEquiv R).symm x) =
      (Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))).symm
        (F.projection k x) := by
  rw [(F.restrictScalars R).projection_mk
    ((F.completionRestrictScalarsEquiv R).symm x).val
    ((F.completionRestrictScalarsEquiv R).symm x).property k,
    F.projection_mk x.val x.property k]
  exact congrFun (LinearEquiv.ofSubmodules_symm_apply
    (LinearEquiv.piCongrRight fun j : ℕᵒᵖ =>
      Submodule.Quotient.restrictScalarsEquiv R (F.submodule (j.unop + 1)))
    (p := (F.restrictScalars R).completionSubmodule)
    (q := F.completionSubmodule.restrictScalars R) _ x) (Opposite.op k)

/-- The canonical map into the completion is preserved by scalar restriction. -/
@[simp]
lemma completionRestrictScalarsEquiv_of (x : M) :
    F.completionRestrictScalarsEquiv R ((F.restrictScalars R).of x) = F.of x := by
  ext k
  simp

/-- Scalar restriction preserves the canonical map in the reverse direction. -/
@[simp]
lemma completionRestrictScalarsEquiv_symm_of (x : M) :
    (F.completionRestrictScalarsEquiv R).symm (F.of x) =
      (F.restrictScalars R).of x := by
  apply (F.completionRestrictScalarsEquiv R).injective
  simp

/-- The induced filtration is unchanged under the completed scalar comparison. -/
@[simp]
lemma comap_completedFiltration_completionRestrictScalarsEquiv (k : ℕ) :
    ((F.completedFiltration.submodule k).restrictScalars R).comap
        (F.completionRestrictScalarsEquiv R).toLinearMap =
      (F.restrictScalars R).completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    ext x
    simp only [completedFiltration_succ, Submodule.mem_comap,
      Submodule.restrictScalars_mem, LinearMap.mem_ker,
      LinearEquiv.coe_coe, projection_completionRestrictScalarsEquiv,
      LinearEquiv.map_eq_zero_iff]

variable {X : Type*} [AddCommGroup X] [Module S X] [Module R X]
  [IsScalarTower R S X]

/-- Restricting a compatible family of linear maps commutes with its universal lift. -/
lemma completionRestrictScalarsEquiv_lift (f : ∀ k, X →ₗ[S] F.quotient k)
    (hf : ∀ k l (h : k ≤ l), (F.transition h).comp (f l) = f k) :
    (F.completionRestrictScalarsEquiv R).toLinearMap.comp
        ((F.restrictScalars R).lift
          (fun k => (Submodule.Quotient.restrictScalarsEquiv R
            (F.submodule (k + 1))).symm.toLinearMap.comp ((f k).restrictScalars R))
          (by
            intro k l h
            ext x
            simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
              LinearEquiv.coe_coe, restrictScalarsEquiv_symm_transition] using
              congrArg (Submodule.Quotient.restrictScalarsEquiv R
                (F.submodule (k + 1))).symm (LinearMap.congr_fun (hf k l h) x))) =
      (F.lift f hf).restrictScalars R := by
  ext x k
  simp

end Ring

end Mei.ModuleFiltration
