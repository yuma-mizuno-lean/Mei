/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Scalar restriction of filtered module completions

Restricting scalars preserves a decreasing module filtration and identifies its
finite quotients and completion with the original ones. The comparison commutes
with transitions, projections, canonical maps and compatible linear lifts. It
also identifies the induced filtrations, so scalar restriction does not change
the order of a completed coefficient.

The finite comparisons use Mathlib's
`Submodule.Quotient.restrictScalarsEquiv`. The completion comparison restricts
their product to the compatible-family submodules using
`LinearEquiv.ofSubmodules`; no choice of quotient representatives is needed.
-/

public section

namespace Mei.ModuleFiltration

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (F : ModuleFiltration R M) (S : Type*) [Semiring S] [SMul S R]
  [Module S M] [IsScalarTower S R M]

/-- Regard every term of a module filtration as a submodule over a smaller scalar ring. -/
def restrictScalars : ModuleFiltration S M where
  submodule k := (F.submodule k).restrictScalars S
  antitone := fun _ _ h => Submodule.restrictScalars_mono S (F.antitone h)
  zero_eq_top := by simp

@[simp]
lemma restrictScalars_submodule (k : ℕ) :
    (F.restrictScalars S).submodule k = (F.submodule k).restrictScalars S :=
  (rfl)

@[simp]
lemma restrictScalars_self : F.restrictScalars R = F := by
  ext k
  simp

/-- Successive scalar restrictions agree with direct restriction. -/
@[simp]
lemma restrictScalars_restrictScalars (T : Type*) [Semiring T] [SMul T S]
    [SMul T R] [Module T M] [IsScalarTower T S M] [IsScalarTower T R M] :
    (F.restrictScalars S).restrictScalars T = F.restrictScalars T := by
  ext k
  simp

end Semiring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) (S : Type*) [Ring S] [SMul S R]
  [Module S M] [IsScalarTower S R M]

/-- The scalar comparison at each order, on the filtered quotient types. -/
def quotientRestrictScalarsEquiv (k : ℕ) :
    (F.restrictScalars S).quotient k ≃ₗ[S] F.quotient k :=
  Submodule.Quotient.restrictScalarsEquiv S (F.submodule (k + 1))

@[simp]
lemma quotientRestrictScalarsEquiv_mk (k : ℕ) (x : M) :
    F.quotientRestrictScalarsEquiv S k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  Submodule.Quotient.restrictScalarsEquiv_mk S _ x

@[simp]
lemma quotientRestrictScalarsEquiv_symm_mk (k : ℕ) (x : M) :
    (F.quotientRestrictScalarsEquiv S k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  Submodule.Quotient.restrictScalarsEquiv_symm_mk S _ x

/-- The finite scalar comparisons commute with all tower transitions. -/
@[simp]
lemma quotientRestrictScalarsEquiv_transition {k l : ℕ} (h : k ≤ l)
    (x : (F.restrictScalars S).quotient l) :
    F.quotientRestrictScalarsEquiv S k
        ((F.restrictScalars S).transition h x) =
      F.transition h (F.quotientRestrictScalarsEquiv S l x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x => simp

/-- Scalar restriction identifies the compatible-family completions linearly. -/
def completionRestrictScalarsEquiv :
    (F.restrictScalars S).completion ≃ₗ[S] F.completion :=
  ((LinearEquiv.piCongrRight fun k : ℕᵒᵖ =>
      F.quotientRestrictScalarsEquiv S k.unop).ofSubmodules
    (F.restrictScalars S).completionSubmodule
    (F.completionSubmodule.restrictScalars S) (by
      ext x
      simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [mem_completionSubmodule_iff] at hy ⊢
        intro k l h
        exact (F.quotientRestrictScalarsEquiv_transition S h _).symm.trans
          (congrArg (F.quotientRestrictScalarsEquiv S k)
            (hy k l h))
      · intro hx
        refine ⟨(LinearEquiv.piCongrRight fun k : ℕᵒᵖ =>
          F.quotientRestrictScalarsEquiv S k.unop).symm x,
          ?_, by ext k; simp⟩
        rw [mem_completionSubmodule_iff] at hx ⊢
        intro k l h
        apply (F.quotientRestrictScalarsEquiv S k).injective
        simpa using hx k l h)).trans
    ((Submodule.restrictScalarsEquiv S R _ F.completionSubmodule).restrictScalars S)

/-- Projections of the comparison are the finite quotient comparisons. -/
@[simp]
lemma projection_completionRestrictScalarsEquiv (k : ℕ)
    (x : (F.restrictScalars S).completion) :
    F.projection k (F.completionRestrictScalarsEquiv S x) =
      F.quotientRestrictScalarsEquiv S k
        ((F.restrictScalars S).projection k x) := by
  rw [F.projection_mk _ (F.completionRestrictScalarsEquiv S x).property,
    (F.restrictScalars S).projection_mk _ x.property]
  simp only [completionRestrictScalarsEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  -- The remaining scalar restriction changes only the structure on the subtype.
  rfl

/-- Projections of the inverse comparison use the inverse quotient comparisons. -/
@[simp]
lemma projection_completionRestrictScalarsEquiv_symm (k : ℕ) (x : F.completion) :
    (F.restrictScalars S).projection k ((F.completionRestrictScalarsEquiv S).symm x) =
      (F.quotientRestrictScalarsEquiv S k).symm
        (F.projection k x) := by
  apply (F.quotientRestrictScalarsEquiv S k).injective
  simpa using (F.projection_completionRestrictScalarsEquiv S k
    ((F.completionRestrictScalarsEquiv S).symm x)).symm

/-- The comparison preserves the canonical map from the original module. -/
@[simp]
lemma completionRestrictScalarsEquiv_of (x : M) :
    F.completionRestrictScalarsEquiv S ((F.restrictScalars S).of x) = F.of x := by
  apply F.completion_ext
  intro k
  simp

/-- The inverse comparison also preserves the canonical map. -/
@[simp]
lemma completionRestrictScalarsEquiv_symm_of (x : M) :
    (F.completionRestrictScalarsEquiv S).symm (F.of x) = (F.restrictScalars S).of x := by
  apply (F.completionRestrictScalarsEquiv S).injective
  simp

/-- Scalar restriction preserves and reflects the filtration on the completion. -/
@[simp]
lemma comap_completedFiltration_restrictScalars (k : ℕ) :
    ((F.completedFiltration.submodule k).restrictScalars S).comap
        (F.completionRestrictScalarsEquiv S).toLinearMap =
      (F.restrictScalars S).completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    ext x
    simp

variable {X : Type*} [AddCommGroup X] [Module R X]
  [Module S X] [IsScalarTower S R X]

/-- Restricting a compatible linear family and then lifting agrees with restricting its lift. -/
lemma completionRestrictScalarsEquiv_lift (f : ∀ k, X →ₗ[R] F.quotient k)
    (hf : ∀ k l (h : k ≤ l), (F.transition h).comp (f l) = f k) (x : X) :
    F.completionRestrictScalarsEquiv S
        ((F.restrictScalars S).lift
          (fun k => (F.quotientRestrictScalarsEquiv S k).symm.toLinearMap.comp
            ((f k).restrictScalars S))
          (by
            intro k l h
            ext y
            apply (F.quotientRestrictScalarsEquiv S k).injective
            simpa using LinearMap.congr_fun (hf k l h) y) x) = F.lift f hf x := by
  apply F.completion_ext
  intro k
  simp

end Mei.ModuleFiltration
