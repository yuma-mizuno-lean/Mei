/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Monomial
public import Mei.Algebra.QuantumMonoidAlgebra.Positive
public import Mei.RingTheory.FilteredAlgebra.Module
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Positive completion coordinates for shifted quantum coefficients

Multiplication by a quantum monomial identifies the completed positive algebra,
as a module, with coefficients supported on any translate of the positive monoid.
The filtration on the translate measures relative degree, so the shift itself
need not have nonnegative degree.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (P : AddSubmonoid Γ)

/-- The positive coefficient algebra is the coefficient module at shift zero. -/
def positiveZeroShiftEquiv :
    positiveSubalgebra q β P ≃ₗ[R] shiftedSubmodule (grade q β) P 0 where
  toFun x := ⟨x, by
    simpa only [← supportedSubalgebra_toSubmodule, Subalgebra.mem_toSubmodule] using x.property⟩
  invFun x := ⟨x, by
    simpa only [← supportedSubalgebra_toSubmodule, Subalgebra.mem_toSubmodule] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The zero-shift identification preserves underlying quantum coefficients. -/
@[simp]
theorem coe_positiveZeroShiftEquiv (x : positiveSubalgebra q β P) :
    (positiveZeroShiftEquiv q β P x : QuantumMonoidAlgebra q β) = x := (rfl)

variable (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)

/-- Algebra degree and relative degree at shift zero define the same filtration. -/
theorem comap_shiftedFiltration_positiveZeroShiftEquiv (k : ℕ) :
    ((d.shiftedFiltration (grade q β) 0).submodule k).comap
        (positiveZeroShiftEquiv q β d.monoid).toLinearMap =
      ((F).toModuleFiltration R).submodule k := by
  classical
  ext x
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Submodule.restrictScalars_mem,
    mem_positiveFiltration_iff]
  rw [PositiveDegrees.mem_shiftedFiltration_iff]
  simp only [coe_positiveZeroShiftEquiv, sub_zero, ZeroMemClass.coe_eq_zero,
    decompose_eq_zero_iff]

/-- Multiplication by a monomial gives positive coordinates on an arbitrary translate. -/
def positiveShiftEquiv (p : Γ) :
    positiveSubalgebra q β d.monoid ≃ₗ[R] shiftedSubmodule (grade q β) d.monoid p :=
  ((positiveZeroShiftEquiv q β d.monoid).trans
    (shiftedMonomialEquiv q β d.monoid p 0)).trans
      (LinearEquiv.ofEq _ _ (congrArg (shiftedSubmodule (grade q β) d.monoid) (add_zero p)))

/-- Positive coordinates use left quantum multiplication by the shift monomial. -/
@[simp]
theorem coe_positiveShiftEquiv (p : Γ)
    (x : positiveSubalgebra q β d.monoid) :
    (positiveShiftEquiv q β d p x : QuantumMonoidAlgebra q β) =
      monomial q β p * x := by
  simp only [positiveShiftEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    coe_shiftedMonomialEquiv, coe_positiveZeroShiftEquiv]

/-- Positive coordinates identify every relative filtration term. -/
theorem comap_shiftedFiltration_positiveShiftEquiv (p : Γ) (k : ℕ) :
    ((d.shiftedFiltration (grade q β) p).submodule k).comap
        (positiveShiftEquiv q β d p).toLinearMap =
      ((F).toModuleFiltration R).submodule k := by
  classical
  have h := comap_shiftedFiltration_shiftedMonomialEquiv q β p 0 d k
  ext x
  have hx := Iff.of_eq (congrArg
    (fun S => positiveZeroShiftEquiv q β d.monoid x ∈ S) h)
  rw [← comap_shiftedFiltration_positiveZeroShiftEquiv q β d k]
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
  simp only [PositiveDegrees.mem_shiftedFiltration_iff,
    coe_shiftedMonomialEquiv, coe_positiveZeroShiftEquiv, add_zero] at hx
  simpa only [PositiveDegrees.mem_shiftedFiltration_iff,
    coe_positiveShiftEquiv, coe_positiveZeroShiftEquiv] using hx

/-- The positive algebra completion gives coordinates on every shifted coefficient module. -/
def positiveCompletionShiftEquiv (p : Γ) :
    (F).completion ≃ₗ[R] d.ShiftedCoefficients (grade q β) p :=
  (F).moduleCompletionEquiv.symm.trans
    (((F).toModuleFiltration R).completionEquiv (d.shiftedFiltration (grade q β) p)
      (positiveShiftEquiv q β d p)
      (comap_shiftedFiltration_positiveShiftEquiv q β d p))

/-- Completed positive coordinates agree with the original monomial translation. -/
@[simp]
theorem positiveCompletionShiftEquiv_toCompletion (p : Γ)
    (x : positiveSubalgebra q β d.monoid) :
    positiveCompletionShiftEquiv q β d p ((F).toCompletion x) =
      (d.shiftedFiltration (grade q β) p).of (positiveShiftEquiv q β d p x) := by
  simp only [positiveCompletionShiftEquiv, LinearEquiv.trans_apply,
    AlgFiltration.moduleCompletionEquiv_symm_toCompletion, ModuleFiltration.completionEquiv_of]

/-- The completed unit is the monomial of relative exponent zero at the chosen shift. -/
@[simp]
theorem positiveCompletionShiftEquiv_one (p : Γ) :
    positiveCompletionShiftEquiv q β d p (1 : (F).completion) =
      (d.shiftedFiltration (grade q β) p).of
        (shiftedMonomial q β d.monoid p 0) := by
  have h := positiveCompletionShiftEquiv_toCompletion q β d p
    (1 : positiveSubalgebra q β d.monoid)
  have h₁ := congrArg (positiveCompletionShiftEquiv q β d p) (F).toCompletion.map_one
  have hm : positiveShiftEquiv q β d p (1 : positiveSubalgebra q β d.monoid) =
      shiftedMonomial q β d.monoid p 0 := by
    apply Subtype.ext
    simp only [coe_positiveShiftEquiv, Subalgebra.coe_one, mul_one,
      coe_shiftedMonomial, ZeroMemClass.coe_zero, add_zero]
  exact h₁.symm.trans (h.trans (congrArg (d.shiftedFiltration (grade q β) p).of hm))

/-- Positive coordinates preserve and reflect all completed relative degrees. -/
@[simp]
theorem positiveCompletionShiftEquiv_mem_iff (p : Γ) (k : ℕ)
    (x : (F).completion) :
    positiveCompletionShiftEquiv q β d p x ∈
        (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k ↔
      x ∈ (F).completionIdeal k := by
  simp only [positiveCompletionShiftEquiv, LinearEquiv.trans_apply,
    ModuleFiltration.completionEquiv_mem_completedFiltration_iff,
    ← AlgFiltration.moduleCompletionEquiv_mem_completionIdeal_iff,
    LinearEquiv.apply_symm_apply]

/-- A representative of a positive completed coefficient gives translated quotient coordinates. -/
theorem projection_positiveCompletionShiftEquiv_of_projection (p : Γ)
    (k : ℕ) (a : (F).completion) (b : positiveSubalgebra q β d.monoid)
    (hb : (F).projection k a = Ideal.Quotient.mk ((F).ideal (k + 1)) b) :
    (d.shiftedFiltration (grade q β) p).projection k
        (positiveCompletionShiftEquiv q β d p a) =
      Submodule.Quotient.mk (positiveShiftEquiv q β d p b) := by
  simp only [positiveCompletionShiftEquiv, LinearEquiv.trans_apply,
    ModuleFiltration.projection_completionEquiv,
    AlgFiltration.projection_moduleCompletionEquiv_symm, hb]
  -- The quotient linear maps send mk to mk by definition; the ideal and submodule
  -- quotients here use the same underlying quotient type and constructor.
  rfl

end Mei.QuantumMonoidAlgebra
