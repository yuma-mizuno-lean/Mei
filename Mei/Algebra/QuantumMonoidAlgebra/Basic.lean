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

The ring and basis are transported from the existing `TauCeti.twistedMonoidAlgebra`
of the factor set `q^(β p r)` along the identification `twistedEquiv`; we do not
construct another twisted multiplication. The quantum algebra is a type synonym with
its own instances, so instance search does not unfold it to the subalgebra of
twisted translations. The exponent pieces are those of the twisted algebra, presented
by the quantum basis.
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
@[expose]
def QuantumMonoidAlgebra {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
    (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) : Type _ :=
  TauCeti.twistedMonoidAlgebra R (Multiplicative Γ) (QuantumMonoidAlgebra.factorSet q β)

namespace QuantumMonoidAlgebra

open TauCeti

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- The ring structure inherited from the algebra of twisted translations. -/
instance instRing : Ring (QuantumMonoidAlgebra q β) :=
  -- Instance search does not find the ring structure of the twisted subalgebra itself.
  letI : Ring (twistedMonoidAlgebra R (Multiplicative Γ) (factorSet q β)) :=
    Subalgebra.toRing (R := R) (A := Module.End R (Multiplicative Γ →₀ R)) _
  inferInstanceAs (Ring (twistedMonoidAlgebra R (Multiplicative Γ) (factorSet q β)))

/-- The algebra structures over the algebras under the coefficient ring, inherited from
the algebra of twisted translations. -/
instance instAlgebra' {k : Type*} [CommSemiring k] [Algebra k R] :
    Algebra k (QuantumMonoidAlgebra q β) :=
  inferInstanceAs (Algebra k (twistedMonoidAlgebra R (Multiplicative Γ) (factorSet q β)))

/-- The coefficient algebra structure, stated directly as for `Subalgebra.algebra`. -/
instance instAlgebra : Algebra R (QuantumMonoidAlgebra q β) :=
  instAlgebra' q β

/-- Scalars from below the coefficient ring act through the coefficient ring. -/
instance instIsScalarTower {k : Type*} [CommSemiring k] [Algebra k R] :
    IsScalarTower k R (QuantumMonoidAlgebra q β) :=
  inferInstanceAs (IsScalarTower k R (twistedMonoidAlgebra R (Multiplicative Γ) (factorSet q β)))

/-- The identification of a quantum algebra with its underlying algebra of twisted
translations, through which the twisted-monoid-algebra API applies. -/
def twistedEquiv :
    QuantumMonoidAlgebra q β ≃ₐ[R] twistedMonoidAlgebra R (Multiplicative Γ) (factorSet q β) :=
  AlgEquiv.refl

/-- The quantum monomial with exponent `p`. -/
def monomial (p : Γ) : QuantumMonoidAlgebra q β :=
  (twistedEquiv q β).symm (TwistedMonoidAlgebra.of (Multiplicative.ofAdd p))

/-- The identification sends the twisted basis vector back to the quantum monomial. -/
@[simp]
theorem twistedEquiv_symm_of (g : Multiplicative Γ) :
    (twistedEquiv q β).symm (TwistedMonoidAlgebra.of g) = monomial q β g.toAdd := (rfl)

/-- The identification sends a quantum monomial to the twisted basis vector. -/
@[simp]
theorem twistedEquiv_monomial (p : Γ) :
    twistedEquiv q β (monomial q β p) = TwistedMonoidAlgebra.of (Multiplicative.ofAdd p) := by
  conv_lhs => rw [show p = (Multiplicative.ofAdd p).toAdd from rfl]
  rw [← twistedEquiv_symm_of, AlgEquiv.apply_symm_apply]

/-- The zero exponent is the multiplicative identity. -/
@[simp]
theorem monomial_zero : monomial q β 0 = 1 :=
  (twistedEquiv q β).injective (by simp)

/-- Multiplication of quantum monomials adds exponents and inserts the form's scalar. -/
@[simp]
theorem monomial_mul (p r : Γ) :
    monomial q β p * monomial q β r =
      ((q ^ β p r : Rˣ) : R) • monomial q β (p + r) := by
  apply (twistedEquiv q β).injective
  simp [TwistedMonoidAlgebra.of_mul_of, ofAdd_add]

/-- Quantum monomials form a basis indexed by the original additive exponent group. -/
def basis : Module.Basis Γ R (QuantumMonoidAlgebra q β) :=
  ((TwistedMonoidAlgebra.basis R (Multiplicative Γ) (factorSet q β)).map
    (twistedEquiv q β).symm.toLinearEquiv).reindex Multiplicative.toAdd

@[simp]
theorem basis_apply (p : Γ) : basis q β p = monomial q β p := by
  simp [basis]

/-- Quantum basis coordinates are the twisted basis coordinates under `twistedEquiv`. -/
theorem basis_repr_apply (x : QuantumMonoidAlgebra q β) (p : Γ) :
    (basis q β).repr x p =
      (TwistedMonoidAlgebra.basis R (Multiplicative Γ) (factorSet q β)).repr
        (twistedEquiv q β x) (Multiplicative.ofAdd p) := by
  simp [basis]

/-- The homogeneous piece of exponent `p`, the twisted exponent piece under
`twistedEquiv`. -/
def grade (p : Γ) : Submodule R (QuantumMonoidAlgebra q β) :=
  (TwistedMonoidAlgebra.grade R (factorSet q β) p).comap (twistedEquiv q β).toLinearMap

/-- Homogeneity is homogeneity of the underlying twisted element. -/
theorem mem_grade_iff_twistedEquiv (p : Γ) (x : QuantumMonoidAlgebra q β) :
    x ∈ grade q β p ↔ twistedEquiv q β x ∈ TwistedMonoidAlgebra.grade R (factorSet q β) p :=
  Iff.rfl

/-- Homogeneous elements are precisely scalar multiples of a quantum monomial. -/
theorem mem_grade_iff (p : Γ) (x : QuantumMonoidAlgebra q β) :
    x ∈ grade q β p ↔ ∃ r : R, r • monomial q β p = x := by
  rw [mem_grade_iff_twistedEquiv, TwistedMonoidAlgebra.mem_grade_iff]
  refine exists_congr fun r => ?_
  rw [← (twistedEquiv q β).injective.eq_iff, map_smul, twistedEquiv_monomial]

/-- A quantum monomial belongs to the homogeneous piece of its exponent. -/
theorem monomial_mem_grade (p : Γ) : monomial q β p ∈ grade q β p :=
  (mem_grade_iff q β p _).mpr ⟨1, one_smul _ _⟩

/-- The exponent pieces multiply as those of the twisted algebra. -/
instance instGradedMonoidGrade : SetLike.GradedMonoid (grade q β) where
  one_mem := by
    rw [mem_grade_iff_twistedEquiv, map_one]
    exact SetLike.GradedOne.one_mem
  mul_mem i j x y hx hy := by
    rw [mem_grade_iff_twistedEquiv] at hx hy ⊢
    rw [map_mul]
    exact SetLike.GradedMul.mul_mem hx hy

/-- The quantum basis presents the exponent pieces as basis lines. -/
def monomialPresentation : MonomialPresentation (grade q β) where
  basis := basis q β
  grade_eq_span p := by
    ext x
    rw [mem_grade_iff, basis_apply, Submodule.mem_span_singleton]

/-- The presentation uses the quantum basis. -/
@[simp]
theorem monomialPresentation_basis : (monomialPresentation q β).basis = basis q β := (rfl)

/-- The exponent pieces form a graded algebra. -/
instance instGradedAlgebraGrade [DecidableEq Γ] : GradedAlgebra (grade q β) :=
  (monomialPresentation q β).isInternal.gradedAlgebra

/-- Homogeneous projection extracts the monomial's coefficient in the quantum basis. -/
theorem coe_decompose [DecidableEq Γ] (x : QuantumMonoidAlgebra q β) (p : Γ) :
    (DirectSum.decompose (grade q β) x p : QuantumMonoidAlgebra q β) =
      (basis q β).repr x p • monomial q β p := by
  simpa using (monomialPresentation q β).coe_decompose x p

/-- A homogeneous quantum component vanishes exactly when its basis coefficient does. -/
@[simp]
theorem decompose_eq_zero_iff [DecidableEq Γ] (x : QuantumMonoidAlgebra q β) (p : Γ) :
    DirectSum.decompose (grade q β) x p = 0 ↔
      (basis q β).repr x p = 0 := by
  rw [← ZeroMemClass.coe_eq_zero, coe_decompose, ← basis_apply]
  constructor
  · intro h
    exact (basis q β).linearIndependent.smul_left_injective p (by simpa using h)
  · intro h
    simp [h]

/-- For an alternating form, monomials with opposite exponents are inverse. -/
theorem monomial_mul_neg (hβ : β.IsAlt) (p : Γ) :
    monomial q β p * monomial q β (-p) = 1 := by
  simp [hβ.self_eq_zero]

/-- The diagonal factor normalizes the left inverse monomial for any bilinear form. -/
theorem diagonal_smul_monomial_neg_mul (p : Γ) :
    ((q ^ β p p : Rˣ) : R) • (monomial q β (-p) * monomial q β p) = 1 := by
  simp only [monomial_mul, map_neg, LinearMap.neg_apply, neg_add_cancel, monomial_zero,
    smul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    one_smul]

/-- The diagonal factor normalizes the right inverse monomial for any bilinear form. -/
theorem diagonal_smul_monomial_mul_neg (p : Γ) :
    ((q ^ β p p : Rˣ) : R) • (monomial q β p * monomial q β (-p)) = 1 := by
  simp only [monomial_mul, map_neg, add_neg_cancel, monomial_zero,
    smul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    one_smul]

/-- Moving a ray generator past a monomial is controlled by the skew part of the form. -/
theorem monomial_semiconjBy_skew (n p : Γ) :
    SemiconjBy (monomial q β p)
      (((q ^ (β n p - β p n) : Rˣ) : R) • monomial q β n) (monomial q β n) := by
  unfold SemiconjBy
  rw [mul_smul_comm, monomial_mul, monomial_mul, smul_smul,
    ← Units.val_mul, ← zpow_add, sub_add_cancel, add_comm p n]

/-- Moving a quantum ray generator past a monomial rescales it by `q^(2β(n,p))`. -/
theorem monomial_semiconjBy (hβ : β.IsAlt) (n p : Γ) :
    SemiconjBy (monomial q β p)
      (((q ^ (2 * β n p) : Rˣ) : R) • monomial q β n) (monomial q β n) := by
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul] using
    monomial_semiconjBy_skew q β n p

/-- Powers of one quantum monomial accumulate the diagonal bilinear factor. -/
theorem monomial_pow_eq_smul (p : Γ) (j : ℕ) :
    monomial q β p ^ j =
      ((q ^ ((j.choose 2 : ℤ) * β p p) : Rˣ) : R) • monomial q β (j • p) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, smul_mul_assoc, monomial_mul, smul_smul,
      ← Units.val_mul, ← zpow_add]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    have hexp : (j.choose 2 : ℤ) * β p p + (j : ℤ) * β p p =
        ((j + 1).choose 2 : ℤ) * β p p := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      ring
    have hdeg : j • p + p = (j + 1) • p := by
      simp only [succ_nsmul]
    rw [hexp, hdeg]

/-- Along a single alternating ray, ordinary powers multiply only the exponent. -/
@[simp]
theorem monomial_pow (hβ : β.IsAlt) (p : Γ) (n : ℕ) :
    monomial q β p ^ n = monomial q β (n • p) := by
  simpa only [hβ.self_eq_zero, mul_zero, zpow_zero, Units.val_one, one_smul] using
    monomial_pow_eq_smul q β p n

/-- The untwisting equivalence for the zero form. -/
def zeroFormEquiv : QuantumMonoidAlgebra q (0 : LinearMap.BilinForm ℤ Γ) ≃ₐ[R]
    AddMonoidAlgebra R Γ :=
  (twistedEquiv q 0).trans <|
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
  simp [zeroFormEquiv]

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
