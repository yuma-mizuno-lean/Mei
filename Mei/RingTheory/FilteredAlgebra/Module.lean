/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.RestrictScalars
public import Mei.RingTheory.FilteredAlgebra.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The underlying module filtration of a filtered algebra

Restricting scalars in the ideals of an algebra filtration gives a module filtration over
the coefficient semiring. This allows results on filtered modules to apply to coefficient
algebras without losing their original ideal filtration. In particular, the quotient
representation of a filtration-raising Lie action can be used on the original quotient rings.

The underlying module completion is canonically linearly equivalent to the algebra
completion. The equivalence identifies projections, original elements, and every
completed filtration term, without a separatedness hypothesis.

The module/algebra completion comparison API `moduleCompletionEquiv`, including
its projection and filtration compatibility lemmas, incorporates the comparison
introduced in [Mei #419](https://github.com/yuma-mizuno-lean/Mei/pull/419).
-/

public section

namespace Mei.AlgFiltration

variable (R : Type*) {A : Type*} [Semiring R] [Semiring A]
  [Module R A] [IsScalarTower R A A]
  (F : AlgFiltration A)

/-- The ideal filtration viewed as submodules over the coefficient semiring. -/
abbrev toModuleFiltration : ModuleFiltration R A where
  submodule k := (F.ideal k).restrictScalars R
  antitone := fun _ _ h => Submodule.restrictScalars_mono R (F.antitone h)
  zero_eq_top := by simp

/-- Each module filtration term is the scalar restriction of the original ideal. -/
@[simp]
theorem toModuleFiltration_submodule (k : ℕ) :
    (F.toModuleFiltration R).submodule k = (F.ideal k).restrictScalars R := (rfl)

end Mei.AlgFiltration

noncomputable section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- The module and algebra completions of an ideal filtration are linearly equivalent. -/
def moduleCompletionEquiv : (F.toModuleFiltration R).completion ≃ₗ[R] F.completion := by
  let e := (F.toModuleFiltration A).completionRestrictScalarsEquiv R
  let E : (F.toModuleFiltration A).completion ≃ F.completion :=
    Equiv.subtypeEquivRight
      fun (x : ∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1)) => by
      have ht {k l : ℕ} (h : k ≤ l) (y : A ⧸ F.ideal (l + 1)) :
          (F.toModuleFiltration A).transition h y = Ideal.Quotient.factor
            (F.antitone (Nat.add_le_add_right h 1)) y := by
        rw [ModuleFiltration.transition_eq_factor]
        simpa only [ModuleFiltration.quotient, toModuleFiltration_submodule,
          Submodule.restrictScalars_self] using!
          Submodule.factor_eq_factor (F.antitone (Nat.add_le_add_right h 1)) y
      constructor
      · intro hx
        apply (F.mem_completion_iff x).mpr
        intro k l h
        exact (ht h _).symm.trans
          (((F.toModuleFiltration A).mem_completionSubmodule_iff x).mp hx k l h)
      · intro hx
        apply ((F.toModuleFiltration A).mem_completionSubmodule_iff x).mpr
        intro k l h
        exact (ht h _).trans ((F.mem_completion_iff x).mp hx h)
  have hproj (k : ℕ) (x : (F.toModuleFiltration A).completion) :
      F.projection k (E x) = (F.toModuleFiltration A).projection k x := by
    rw [projection_apply, (F.toModuleFiltration A).projection_mk]
    rfl
  refine e.trans { E with map_add' := ?_, map_smul' := ?_ }
  · intro x y
    -- The record update uses `E.toFun`; present it as `E` so `hproj` can rewrite
    -- the projections of both sides of the additivity goal.
    change E (x + y) = E x + E y
    apply F.completion_ext
    intro k
    rw [map_add (F.projection k), hproj, hproj, hproj, map_add]
    rfl
  · intro r x
    -- Reduce the record update's `E.toFun` and identity scalar homomorphism so
    -- `hproj` and the R-linear projection laws match the scalar-linearity goal.
    change E (r • x) = r • E x
    apply F.completion_ext
    intro k
    have hs := map_smul (F.projectionₐ (R := R) k) r (E x)
    have ht := map_smul (((F.toModuleFiltration A).projection k).restrictScalars R) r x
    simp only [projectionₐ_apply] at hs
    simp only [LinearMap.restrictScalars_apply] at ht
    rw [hproj, hs, hproj, ht]
    rfl

/-- The comparison uses the scalar-restriction equivalence at every finite order. -/
@[simp]
theorem projection_moduleCompletionEquiv (k : ℕ)
    (x : (F.toModuleFiltration R).completion) :
    F.projection k (F.moduleCompletionEquiv x) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).projection k x) := by
  have h := (F.toModuleFiltration A).projection_completionRestrictScalarsEquiv R x k
  rw [(F.toModuleFiltration A).projection_mk] at h
  rw [projection_apply]
  exact h

/-- The inverse comparison uses the inverse scalar-restriction equivalence. -/
@[simp]
theorem projection_moduleCompletionEquiv_symm (k : ℕ) (x : F.completion) :
    (F.toModuleFiltration R).projection k ((F.moduleCompletionEquiv (R := R)).symm x) =
      (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).symm
        (F.projection k x) := by
  conv_rhs =>
    rw [← (F.moduleCompletionEquiv (R := R)).apply_symm_apply x,
      projection_moduleCompletionEquiv]
  rw [LinearEquiv.symm_apply_apply]

/-- The comparison sends original elements to their canonical algebra completion images. -/
@[simp]
theorem moduleCompletionEquiv_of (x : A) :
    F.moduleCompletionEquiv ((F.toModuleFiltration R).of x) = F.toCompletion x := by
  apply F.completion_ext
  intro k
  simp [projection_moduleCompletionEquiv, ModuleFiltration.projection_of,
    projection_toCompletion]

/-- Every completed module filtration term corresponds exactly to the completion ideal. -/
@[simp]
theorem moduleCompletionEquiv_mem_completionIdeal_iff (k : ℕ)
    (x : (F.toModuleFiltration R).completion) :
    F.moduleCompletionEquiv x ∈ F.completionIdeal k ↔
      x ∈ (F.toModuleFiltration R).completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [completionIdeal_succ, ModuleFiltration.completedFiltration_succ,
      RingHom.mem_ker, LinearMap.mem_ker, projection_moduleCompletionEquiv,
      LinearEquiv.map_eq_zero_iff]

/-- The inverse comparison recovers the module image of an original element. -/
@[simp]
theorem moduleCompletionEquiv_symm_toCompletion (x : A) :
    (F.moduleCompletionEquiv (R := R)).symm (F.toCompletion x) =
      (F.toModuleFiltration R).of x := by
  rw [← F.moduleCompletionEquiv_of (R := R), LinearEquiv.symm_apply_apply]

/-- Pulling back a completion ideal gives the completed module filtration exactly. -/
theorem comap_completionIdeal_moduleCompletionEquiv (k : ℕ) :
    ((F.completionIdeal k).restrictScalars R).comap
        (F.moduleCompletionEquiv (R := R)).toLinearMap =
      (F.toModuleFiltration R).completedFiltration.submodule k := by
  ext x
  exact F.moduleCompletionEquiv_mem_completionIdeal_iff k x

end Mei.AlgFiltration
