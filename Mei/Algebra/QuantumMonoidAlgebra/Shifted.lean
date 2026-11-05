/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Units
public import Mei.RingTheory.GradedAlgebra.Shifted.Basic
public import Mei.LinearAlgebra.ModuleFiltration.Equiv
public import Mei.Algebra.DirectSum.Degree.Map

/-!
# Translation equivalences for shifted quantum coefficients

Left multiplication by a quantum monomial translates coefficient support from
`s + P` to `(p + s) + P`. Its inverse multiplies by the opposite monomial
and the scalar `q ^ β p p`; for an alternating form that scalar is one.
Relative degrees are unchanged, so this equivalence
extends to all completed shifted coefficients. The ambient shifts may have
negative degree; no positivity or injectivity assumption on them is used.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (P : AddSubmonoid Γ) (p s : Γ)

/-- A monomial translates the support of a shifted coefficient module. -/
theorem monomial_mul_mem_shiftedSubmodule {x : QuantumMonoidAlgebra q β}
    (hx : x ∈ shiftedSubmodule (grade q β) P s) :
    monomial q β p * x ∈ shiftedSubmodule (grade q β) P (p + s) := by
  have hp : monomial q β p ∈ shiftedSubmodule (grade q β) P p := by
    apply le_shiftedSubmodule (grade q β) P p P.zero_mem
    simpa only [add_zero] using (mem_grade_iff q β p _).mpr ⟨1, one_smul _ _⟩
  exact shiftedSubmodule_mul_le (grade q β) P p s (Submodule.mul_mem_mul hp hx)

/-- Multiplication by a monomial is a linear equivalence between translated supports. -/
def shiftedMonomialEquiv :
    shiftedSubmodule (grade q β) P s ≃ₗ[R]
      shiftedSubmodule (grade q β) P (p + s) where
  toFun x := ⟨(monomialUnit q β p : QuantumMonoidAlgebra q β) * x, by
    rw [coe_monomialUnit]
    exact monomial_mul_mem_shiftedSubmodule q β P p s x.property⟩
  invFun y := ⟨(↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) * y, by
    rw [coe_monomialUnit_inv, smul_mul_assoc]
    apply Submodule.smul_mem
    simpa only [neg_add_cancel_left] using
      monomial_mul_mem_shiftedSubmodule q β P (-p) (p + s) y.property⟩
  left_inv x := by
    apply Subtype.ext
    -- Unfold the nested subtype to expose multiplication by the inverse unit.
    change (↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) *
      ((monomialUnit q β p : QuantumMonoidAlgebra q β) * x) = x
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv y := by
    apply Subtype.ext
    -- Unfold the nested subtype to expose multiplication by the unit and its inverse.
    change (monomialUnit q β p : QuantumMonoidAlgebra q β) *
      ((↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) * y) = y
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_smul_comm _ _ _)

/-- The translation equivalence is left multiplication on underlying coefficients. -/
@[simp]
theorem coe_shiftedMonomialEquiv
    (x : shiftedSubmodule (grade q β) P s) :
    (shiftedMonomialEquiv q β P p s x : QuantumMonoidAlgebra q β) =
      monomial q β p * x := by
  -- Unfold the LinearEquiv application and subtype value to rewrite the defining unit.
  change (monomialUnit q β p : QuantumMonoidAlgebra q β) * x = _
  rw [coe_monomialUnit]

/-- Inverse translation includes the diagonal scalar for an arbitrary bilinear form. -/
@[simp]
theorem coe_shiftedMonomialEquiv_symm
    (y : shiftedSubmodule (grade q β) P (p + s)) :
    ((shiftedMonomialEquiv q β P p s).symm y : QuantumMonoidAlgebra q β) =
      ((q ^ β p p : Rˣ) : R) • (monomial q β (-p) * y) := by
  -- Unfold the inverse LinearEquiv application and subtype value to rewrite its unit.
  change (↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) * y = _
  rw [coe_monomialUnit_inv, smul_mul_assoc]

/-- For an alternating form the inverse is multiplication by the opposite monomial. -/
theorem coe_shiftedMonomialEquiv_symm_of_isAlt (hβ : β.IsAlt)
    (y : shiftedSubmodule (grade q β) P (p + s)) :
    ((shiftedMonomialEquiv q β P p s).symm y : QuantumMonoidAlgebra q β) =
      monomial q β (-p) * y := by
  simp only [coe_shiftedMonomialEquiv_symm, hβ p, zpow_zero, Units.val_one, one_smul]

/-- Translation preserves the relative homogeneous index. -/
theorem shiftedMonomialEquiv_mem_shiftedGrading {n : Γ}
    {x : shiftedSubmodule (grade q β) P s}
    (hx : x ∈ shiftedGrading (grade q β) P s n) :
    shiftedMonomialEquiv q β P p s x ∈ shiftedGrading (grade q β) P (p + s) n := by
  rw [mem_shiftedGrading] at hx ⊢
  rw [coe_shiftedMonomialEquiv]
  have hp : monomial q β p ∈ grade q β p :=
    (mem_grade_iff q β p _).mpr ⟨1, one_smul _ _⟩
  simpa only [add_assoc] using SetLike.mul_mem_graded hp hx

variable (d : PositiveDegrees Γ)

/-- Arbitrary translation identifies every relative filtration term exactly. -/
theorem comap_shiftedFiltration_shiftedMonomialEquiv (k : ℕ) :
    ((d.shiftedFiltration (grade q β) (p + s)).submodule k).comap
        (shiftedMonomialEquiv q β d.monoid p s).toLinearMap =
      (d.shiftedFiltration (grade q β) s).submodule k := by
  classical
  cases k with
  | zero => simp
  | succ k =>
    rw [d.shiftedFiltration_succ (grade q β) (p + s) k,
      d.shiftedFiltration_succ (grade q β) s k,
      d.degreeSubmodule_eq_degreeTail, d.degreeSubmodule_eq_degreeTail]
    exact (shiftedMonomialEquiv q β d.monoid p s).toLinearMap.comap_degreeTail_eq_of_injective
      (shiftedGrading (grade q β) d.monoid s)
      (shiftedGrading (grade q β) d.monoid (p + s))
      (shiftedMonomialEquiv q β d.monoid p s).injective
      (fun _ _ hx => shiftedMonomialEquiv_mem_shiftedGrading q β d.monoid p s hx)
      d.degree (k + 1)

/-- Quantum monomial translation extends to all shifted completed coefficients. -/
def shiftedCompletedMonomialEquiv :
    d.ShiftedCoefficients (grade q β) s ≃ₗ[R]
      d.ShiftedCoefficients (grade q β) (p + s) :=
  (d.shiftedFiltration (grade q β) s).completionEquiv
    (d.shiftedFiltration (grade q β) (p + s))
    (shiftedMonomialEquiv q β d.monoid p s)
    (comap_shiftedFiltration_shiftedMonomialEquiv q β p s d)

/-- The completed equivalence agrees with multiplication on original shifted coefficients. -/
@[simp]
theorem shiftedCompletedMonomialEquiv_of
    (x : shiftedSubmodule (grade q β) d.monoid s) :
    shiftedCompletedMonomialEquiv q β p s d ((d.shiftedFiltration (grade q β) s).of x) =
      (d.shiftedFiltration (grade q β) (p + s)).of
        (shiftedMonomialEquiv q β d.monoid p s x) := by
  exact ModuleFiltration.completionEquiv_of _ _ _ _ x

/-- Inverse completed translation computes on canonical images. -/
@[simp]
theorem shiftedCompletedMonomialEquiv_symm_of
    (y : shiftedSubmodule (grade q β) d.monoid (p + s)) :
    (shiftedCompletedMonomialEquiv q β p s d).symm
        ((d.shiftedFiltration (grade q β) (p + s)).of y) =
      (d.shiftedFiltration (grade q β) s).of
        ((shiftedMonomialEquiv q β d.monoid p s).symm y) :=
  ModuleFiltration.completionEquiv_symm_of _ _ _ _ y

/-- Each projection of an arbitrary completed translation is the induced finite map. -/
@[simp]
theorem projection_shiftedCompletedMonomialEquiv (k : ℕ)
    (x : d.ShiftedCoefficients (grade q β) s) :
    (d.shiftedFiltration (grade q β) (p + s)).projection k
        (shiftedCompletedMonomialEquiv q β p s d x) =
      ((d.shiftedFiltration (grade q β) s).submodule (k + 1)).mapQ
        ((d.shiftedFiltration (grade q β) (p + s)).submodule (k + 1))
        (shiftedMonomialEquiv q β d.monoid p s).toLinearMap
        (by rw [comap_shiftedFiltration_shiftedMonomialEquiv])
        ((d.shiftedFiltration (grade q β) s).projection k x) :=
  ModuleFiltration.projection_completionEquiv _ _ _ _ k x

/-- Each inverse projection is induced by the scalar-normalized inverse translation. -/
@[simp]
theorem projection_shiftedCompletedMonomialEquiv_symm (k : ℕ)
    (y : d.ShiftedCoefficients (grade q β) (p + s)) :
    (d.shiftedFiltration (grade q β) s).projection k
        ((shiftedCompletedMonomialEquiv q β p s d).symm y) =
      ((d.shiftedFiltration (grade q β) (p + s)).submodule (k + 1)).mapQ
        ((d.shiftedFiltration (grade q β) s).submodule (k + 1))
        (shiftedMonomialEquiv q β d.monoid p s).symm.toLinearMap
        (by rw [ModuleFiltration.comap_submodule_equiv_symm _ _ _
          (comap_shiftedFiltration_shiftedMonomialEquiv q β p s d)])
        ((d.shiftedFiltration (grade q β) (p + s)).projection k y) :=
  ModuleFiltration.projection_completionEquiv_symm _ _ _ _ k y

/-- The completed inverse is obtained by completing the finite inverse translation. -/
theorem shiftedCompletedMonomialEquiv_symm :
    (shiftedCompletedMonomialEquiv q β p s d).symm =
      (d.shiftedFiltration (grade q β) (p + s)).completionEquiv
        (d.shiftedFiltration (grade q β) s)
        (shiftedMonomialEquiv q β d.monoid p s).symm
        (ModuleFiltration.comap_submodule_equiv_symm _ _ _
          (comap_shiftedFiltration_shiftedMonomialEquiv q β p s d)) :=
  ModuleFiltration.completionEquiv_symm _ _ _ _

/-- Monomial translation preserves and reflects every completed relative order. -/
@[simp]
theorem shiftedCompletedMonomialEquiv_mem_completedFiltration_iff
    (k : ℕ) (x : d.ShiftedCoefficients (grade q β) s) :
    shiftedCompletedMonomialEquiv q β p s d x ∈
        (d.shiftedFiltration (grade q β) (p + s)).completedFiltration.submodule k ↔
      x ∈ (d.shiftedFiltration (grade q β) s).completedFiltration.submodule k :=
  ModuleFiltration.completionEquiv_mem_completedFiltration_iff _ _ _ _ k x

end Mei.QuantumMonoidAlgebra
