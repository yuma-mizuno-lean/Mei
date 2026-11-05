/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted

/-!
# Monomials in shifted quantum coefficient modules

The monomial of relative exponent `n` in the module shifted by `p` has ambient
exponent `p + n`. Its scalar multiples have exactly relative order `δ(n)` unless
the scalar vanishes. Thus finite relative quotients need no assumption on the
degree of the ambient shift.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (P : AddSubmonoid Γ) (p : Γ)

/-- A quantum monomial with an allowed relative exponent in a shifted coefficient module. -/
def shiftedMonomial (n : P) : shiftedSubmodule (grade q β) P p :=
  ⟨monomial q β (p + n), le_shiftedSubmodule (grade q β) P p n.property
    ((mem_grade_iff q β (p + n) _).mpr ⟨1, one_smul _ _⟩)⟩

/-- The underlying exponent is the ambient shift plus the relative exponent. -/
@[simp]
theorem coe_shiftedMonomial (n : P) :
    (shiftedMonomial q β P p n : QuantumMonoidAlgebra q β) = monomial q β (p + n) := (rfl)

variable (d : PositiveDegrees Γ)

/-- A scalar shifted monomial lies in a filtration term exactly at its relative order. -/
@[simp]
theorem smul_shiftedMonomial_mem_shiftedFiltration_iff (n : d.monoid) (r : R) (k : ℕ) :
    r • shiftedMonomial q β d.monoid p n ∈
        (d.shiftedFiltration (grade q β) p).submodule k ↔
      r = 0 ∨ (k : ℤ) ≤ d.degree n := by
  classical
  let x : grade q β (p + n) :=
    ⟨monomial q β (p + n), (mem_grade_iff q β (p + n) _).mpr ⟨1, one_smul _ _⟩⟩
  have h := d.shiftedInclusion_mem_shiftedFiltration_iff (grade q β) p n (r • x) k
  have hx : (x : QuantumMonoidAlgebra q β) = monomial q β (p + n) := rfl
  have hz : r • x = 0 ↔ r = 0 := by
    constructor
    · intro he
      have he' : r • monomial q β (p + n) = 0 := by
        simpa only [Submodule.coe_smul, ZeroMemClass.coe_zero, hx] using
          congrArg (fun z : grade q β (p + n) => (z : QuantumMonoidAlgebra q β)) he
      have hc := congrArg (fun z : QuantumMonoidAlgebra q β => (basis q β).repr z (p + n)) he'
      simpa only [← basis_apply, _root_.map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero, Finsupp.zero_apply] using hc
    · rintro rfl
      simp
  have hi : shiftedInclusion (grade q β) d.monoid p n x =
      shiftedMonomial q β d.monoid p n := by
    apply Subtype.ext
    simp only [coe_shiftedInclusion, hx, coe_shiftedMonomial]
  simpa only [map_smul, hz, hi] using h

/-- Vanishing in a finite relative quotient is detected by the scalar and relative degree. -/
theorem quotient_smul_shiftedMonomial_eq_zero_iff (n : d.monoid) (r : R) (k : ℕ) :
    (Submodule.Quotient.mk (p := (d.shiftedFiltration (grade q β) p).submodule (k + 1))
      (r • shiftedMonomial q β d.monoid p n)) = 0 ↔
      r = 0 ∨ (k : ℤ) < d.degree n := by
  rw [Submodule.Quotient.mk_eq_zero, smul_shiftedMonomial_mem_shiftedFiltration_iff]
  exact or_congr Iff.rfl (by omega)

end Mei.QuantumMonoidAlgebra
