/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Twisted.Grading
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Quantum monoid algebras

The quantum algebra of an integral bilinear form `β` and a unit `q` has monomials
`z^p` satisfying `z^p * z^r = q^(β p r) • z^(p+r)`. Its underlying module is free
on the exponent group, and its exponent pieces form a graded algebra. For an
alternating form the commutator has coefficient `q^(β p r) - q^(-β p r)`.
The zero form gives the ordinary additive monoid algebra, preserving degrees.

The ring and basis are the existing `TauCeti.twistedMonoidAlgebra` of the
factor set `q^(β p r)`; we do not construct another twisted multiplication.
The conventions follow Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Example 2.1(iii), and Nakanishi, *Pentagon relation in
quantum cluster scattering diagrams*, §2.3.
-/

public section

noncomputable section

namespace Mei

namespace QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]

/-- The normalized factor set associated with an integral bilinear form. -/
def factorSet (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)
    (p r : Multiplicative Γ) : Rˣ := q ^ β p.toAdd r.toAdd

/-- Evaluation of the bilinear quantum factor set. -/
@[simp]
theorem factorSet_apply (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)
    (p r : Multiplicative Γ) : factorSet q β p r = q ^ β p.toAdd r.toAdd := (rfl)

instance instIsFactorSet (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) :
    TauCeti.IsFactorSet (factorSet q β) where
  cocycle p r s := by
    simp only [factorSet, toAdd_mul, map_add, LinearMap.add_apply,
      ← zpow_add]
    congr 1
    omega
  one_left p := by simp [factorSet]
  one_right p := by simp [factorSet]

end QuantumMonoidAlgebra

/-- The quantum algebra of an exponent group and an integral bilinear form.
Alternating forms give the usual quantum torus multiplication. -/
abbrev QuantumMonoidAlgebra {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
    (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) :=
  TauCeti.twistedMonoidAlgebra R (Multiplicative Γ) (QuantumMonoidAlgebra.factorSet q β)

namespace QuantumMonoidAlgebra

open TauCeti

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- The quantum monomial with exponent `p`. -/
def monomial (p : Γ) : QuantumMonoidAlgebra q β :=
  TauCeti.TwistedMonoidAlgebra.of (Multiplicative.ofAdd p)

/-- The zero exponent is the multiplicative identity. -/
@[simp]
theorem monomial_zero : monomial q β 0 = 1 := TauCeti.TwistedMonoidAlgebra.of_one

/-- Multiplication of quantum monomials adds exponents and inserts the form's scalar. -/
@[simp]
theorem monomial_mul (p r : Γ) :
    monomial q β p * monomial q β r =
      ((q ^ β p r : Rˣ) : R) • monomial q β (p + r) :=
  TauCeti.TwistedMonoidAlgebra.of_mul_of _ _

/-- Quantum monomials form a basis indexed by the original additive exponent group. -/
def basis : Module.Basis Γ R (QuantumMonoidAlgebra q β) :=
  (TauCeti.TwistedMonoidAlgebra.basis R (Multiplicative Γ) (factorSet q β)).reindex
    Multiplicative.toAdd

@[simp]
theorem basis_apply (p : Γ) : basis q β p = monomial q β p := by
  simp only [basis, Module.Basis.reindex_apply, TauCeti.TwistedMonoidAlgebra.basis_apply, monomial]
  rfl

/-- The homogeneous piece of exponent `p`. -/
abbrev grade (p : Γ) : Submodule R (QuantumMonoidAlgebra q β) :=
  TwistedMonoidAlgebra.grade R (factorSet q β) p

/-- Homogeneous elements are precisely scalar multiples of a quantum monomial. -/
theorem mem_grade_iff (p : Γ) (x : QuantumMonoidAlgebra q β) :
    x ∈ grade q β p ↔ ∃ r : R, r • monomial q β p = x :=
  TwistedMonoidAlgebra.mem_grade_iff _ _ _ _

/-- Homogeneous projection extracts the monomial's coefficient in the quantum basis. -/
theorem coe_decompose [DecidableEq Γ] (x : QuantumMonoidAlgebra q β) (p : Γ) :
    (DirectSum.decompose (grade q β) x p : QuantumMonoidAlgebra q β) =
      (basis q β).repr x p • monomial q β p := by
  simpa only [basis, Module.Basis.repr_reindex_apply, Multiplicative.toAdd,
    Equiv.symm_symm, monomial] using
    TwistedMonoidAlgebra.coe_decompose_grade R (factorSet q β) x p

/-- For an alternating form, monomials with opposite exponents are inverse. -/
theorem monomial_mul_neg (hβ : β.IsAlt) (p : Γ) :
    monomial q β p * monomial q β (-p) = 1 := by
  simp [hβ.self_eq_zero]

/-- Along a single alternating ray, ordinary powers multiply only the exponent. -/
@[simp]
theorem monomial_pow (hβ : β.IsAlt) (p : Γ) (n : ℕ) :
    monomial q β p ^ n = monomial q β (n • p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, monomial_mul]
    simp [succ_nsmul, hβ.self_eq_zero]

/-- The untwisting equivalence for the zero form. -/
def zeroFormEquiv : QuantumMonoidAlgebra q (0 : LinearMap.BilinForm ℤ Γ) ≃ₐ[R]
    AddMonoidAlgebra R Γ :=
  (TauCeti.TwistedMonoidAlgebra.equivOfCoboundary
    (1 : Multiplicative Γ → Multiplicative Γ → Rˣ)
    (factorSet q (0 : LinearMap.BilinForm ℤ Γ)) (fun _ => 1)
    (by intros; simp [factorSet])).trans
    ((TauCeti.TwistedMonoidAlgebra.monoidAlgebraEquiv R (Multiplicative Γ)).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R Γ).symm)

/-- Untwisting preserves the exponent and the coefficient of every monomial. -/
@[simp]
theorem zeroFormEquiv_monomial (p : Γ) :
    zeroFormEquiv q (monomial q 0 p) = AddMonoidAlgebra.single p 1 := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R Γ).injective
  simp [zeroFormEquiv, monomial]

/-- The zero-form comparison preserves and reflects the homogeneous pieces. -/
theorem zeroFormEquiv_mem_grade_iff (p : Γ) (x : QuantumMonoidAlgebra q 0) :
    zeroFormEquiv q x ∈ AddMonoidAlgebra.grade R p ↔ x ∈ grade q 0 p := by
  rw [AddMonoidAlgebra.mem_grade_iff', mem_grade_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, (zeroFormEquiv q).injective ?_⟩
    simpa only [map_smul, zeroFormEquiv_monomial, AddMonoidAlgebra.smul_single,
      smul_eq_mul, mul_one, AddMonoidAlgebra.lsingle_apply] using hr
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp⟩

attribute [local instance] LieRing.ofAssociativeRing

/-- The quantum commutator is the difference of the two ordered multiplication scalars. -/
theorem lie_monomial (hβ : β.IsAlt) (p r : Γ) :
    ⁅monomial q β p, monomial q β r⁆ =
      (((q ^ β p r : Rˣ) : R) - ((q ^ (-β p r) : Rˣ) : R)) •
        monomial q β (p + r) := by
  rw [Ring.lie_def, monomial_mul, monomial_mul, ← hβ.neg_eq p r, add_comm r p,
    sub_smul]

end QuantumMonoidAlgebra
end Mei
