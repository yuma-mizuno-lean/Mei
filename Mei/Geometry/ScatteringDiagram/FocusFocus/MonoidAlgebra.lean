/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Exponent
public import Mei.RingTheory.Node.ScalarTower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Monoid-algebra presentations of the focus-focus chambers

The free coordinates on the focus-focus exponent monoid identify its algebra
with `R[w,w⁻¹][x,y]`. The smoothing monomial becomes `xy`, so specializing it
to a scalar gives the nodal equation. This dictionary also identifies the
left and right order cutoffs with powers of `y` and `x`.

The construction uses Mathlib's `AddMonoidAlgebra.domCongr`, `curryAlgEquiv`
and double-quotient isomorphism, the free coordinates `exponentEquiv`, and
the quotient-map universal property of `TauCeti.NodeAlgebra.mk`.
The coordinate conventions follow Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2).
-/

public section

noncomputable section

namespace Mei.FocusFocus

open AddMonoidAlgebra
open scoped LaurentPolynomial

private def exponentIndex : exponentMonoid ≃+ ((Fin 2 →₀ ℕ) × ℤ) :=
  exponentEquiv.trans ((AddEquiv.prodCongr (AddEquiv.refl ℤ) AddEquiv.prodComm).trans
    (AddEquiv.prodComm.trans (AddEquiv.prodCongr
      (((LinearEquiv.finTwoArrow ℕ ℕ).symm.trans
        (Finsupp.linearEquivFunOnFinite ℕ ℕ (Fin 2)).symm).toAddEquiv)
      (AddEquiv.refl ℤ))))

private theorem exponentIndex_apply (q : exponentMonoid) :
    exponentIndex q =
      (Finsupp.single 0 (rightOrder q) + Finsupp.single 1 (leftOrder q), q.val.2.1) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [exponentIndex, AddEquiv.prodCongr, exponentEquiv_apply,
      LinearEquiv.finTwoArrow]
  · simp [exponentIndex, AddEquiv.prodCongr]

variable (R : Type*)

section Semiring

variable [CommSemiring R]

/-- The coefficient monoid algebra is a two-variable polynomial algebra over
the tangential Laurent algebra, with variables ordered as `x,y`. -/
def exponentPolynomialEquiv :
    AddMonoidAlgebra R exponentMonoid ≃ₐ[R] MvPolynomial (Fin 2) R[T;T⁻¹] :=
  (domCongr R R exponentIndex).trans (curryAlgEquiv R)

/-- The dictionary retains the Laurent exponent and both nonnegative orders. -/
@[simp]
theorem exponentPolynomialEquiv_single (q : exponentMonoid) (r : R) :
    exponentPolynomialEquiv R (single q r) =
      MvPolynomial.monomial
        (Finsupp.single 0 (rightOrder q) + Finsupp.single 1 (leftOrder q))
        (single q.val.2.1 r) := by
  simp only [exponentPolynomialEquiv, AlgEquiv.trans_apply, domCongr_single,
    exponentIndex_apply, curryAlgEquiv_single, MvPolynomial.single_eq_monomial]

/-- A polynomial monomial lifts to the unique exponent with the prescribed
Laurent coordinate and `y,x` multiplicities. -/
@[simp]
theorem exponentPolynomialEquiv_symm_monomial (m : Fin 2 →₀ ℕ) (b : ℤ) (r : R) :
    (exponentPolynomialEquiv R).symm (MvPolynomial.monomial m
        (_root_.LaurentPolynomial.C r * _root_.LaurentPolynomial.T b)) =
      single (exponentEquiv.symm (b, m 1, m 0)) r := by
  rw [← _root_.LaurentPolynomial.single_eq_C_mul_T]
  apply (exponentPolynomialEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, exponentPolynomialEquiv_single]
  have hm : Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) = m := by
    ext i
    fin_cases i <;> simp
  simp [hm]

@[simp high]
theorem exponentPolynomialEquiv_xDegree :
    exponentPolynomialEquiv R (single xDegree 1) = MvPolynomial.X 0 := by
  simp [MvPolynomial.X]

@[simp high]
theorem exponentPolynomialEquiv_yDegree :
    exponentPolynomialEquiv R (single yDegree 1) = MvPolynomial.X 1 := by
  simp [MvPolynomial.X]

/-- The smoothing monomial is the product of the two polynomial variables. -/
@[simp high]
theorem exponentPolynomialEquiv_smoothingDegree :
    exponentPolynomialEquiv R (single smoothingDegree 1) =
      MvPolynomial.X 0 * MvPolynomial.X 1 := by
  rw [← exponentPolynomialEquiv_xDegree, ← exponentPolynomialEquiv_yDegree,
    ← map_mul, single_mul_single, one_mul, xDegree_add_yDegree]

/-- Changing coefficient rings commutes with the polynomial dictionary. -/
@[simp]
theorem exponentPolynomialEquiv_mapRingHom {S : Type*} [CommSemiring S]
    (φ : R →+* S) (a : AddMonoidAlgebra R exponentMonoid) :
    exponentPolynomialEquiv S (mapRingHom exponentMonoid φ a) =
      MvPolynomial.map (mapRingHom ℤ φ) (exponentPolynomialEquiv R a) := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single q r =>
    simp only [mapRingHom_single, exponentPolynomialEquiv_single, MvPolynomial.map_monomial]

end Semiring

section Ring

variable [CommRing R]

open TauCeti
open scoped Mei.NodeAlgebra

/-- Specializing the smoothing monomial to `t` gives the nodal algebra
`R[w,w⁻¹][x,y]/(xy-t)`. -/
def smoothingSpecializationEquiv (t : R) :
    (AddMonoidAlgebra R exponentMonoid ⧸
      Ideal.span {single smoothingDegree 1 - single 0 t}) ≃ₐ[R]
        NodeAlgebra R[T;T⁻¹] (_root_.LaurentPolynomial.C t) := by
  let f : MvPolynomial (Fin 2) R[T;T⁻¹] →ₐ[R]
      NodeAlgebra R[T;T⁻¹] (_root_.LaurentPolynomial.C t) :=
    (NodeAlgebra.mk (_root_.LaurentPolynomial.C t)).restrictScalars R
  have hf : Function.Surjective f := by
    simpa only [f, AlgHom.coe_restrictScalars'] using NodeAlgebra.mk_surjective
      (_root_.LaurentPolynomial.C t)
  refine (Ideal.quotientEquivAlg
    (Ideal.span {(single smoothingDegree (1 : R) - single 0 t)})
    (RingHom.ker f)
    (exponentPolynomialEquiv R) ?_).trans
      (Ideal.quotientKerAlgEquivOfSurjective hf)
  dsimp only [f]
  rw [AlgHom.ker_coe, AlgHom.coe_restrictScalars, NodeAlgebra.ker_mk]
  simp [Ideal.map_span, Set.image_singleton,
    MvPolynomial.X, MvPolynomial.monomial_mul_monomial]

/-- Specialization on a monoid-algebra representative is the polynomial dictionary
followed by the nodal quotient map. -/
@[simp]
theorem smoothingSpecializationEquiv_mk (t : R)
    (a : AddMonoidAlgebra R exponentMonoid) :
    smoothingSpecializationEquiv R t (Ideal.Quotient.mk _ a) =
      NodeAlgebra.mk (_root_.LaurentPolynomial.C t) (exponentPolynomialEquiv R a) := by
  simp only [smoothingSpecializationEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlg_mk, Ideal.quotientKerAlgEquivOfSurjective_mk,
    AlgHom.restrictScalars_apply]

/-- The inverse dictionary lifts any polynomial representative of a nodal element. -/
@[simp]
theorem smoothingSpecializationEquiv_symm_mk (t : R)
    (p : MvPolynomial (Fin 2) R[T;T⁻¹]) :
    (smoothingSpecializationEquiv R t).symm
        (NodeAlgebra.mk (_root_.LaurentPolynomial.C t) p) =
      Ideal.Quotient.mk _ ((exponentPolynomialEquiv R).symm p) := by
  apply (smoothingSpecializationEquiv R t).injective
  rw [AlgEquiv.apply_symm_apply, smoothingSpecializationEquiv_mk,
    AlgEquiv.apply_symm_apply]

/-- Each monomial specializes to its Laurent coefficient times the corresponding
powers of the two nodal coordinates. -/
theorem smoothingSpecializationEquiv_single (t : R) (q : exponentMonoid) (r : R) :
    smoothingSpecializationEquiv R t (Ideal.Quotient.mk _ (single q r)) =
      algebraMap R[T;T⁻¹] (NodeAlgebra R[T;T⁻¹] (_root_.LaurentPolynomial.C t))
          (single q.val.2.1 r) *
        NodeAlgebra.coord (_root_.LaurentPolynomial.C t) 0 ^ rightOrder q *
        NodeAlgebra.coord (_root_.LaurentPolynomial.C t) 1 ^ leftOrder q := by
  rw [smoothingSpecializationEquiv_mk, exponentPolynomialEquiv_single,
    MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial]
  simp

/-- Imposing the smoothing relation and one chamber cutoff on the monoid algebra
gives the corresponding truncated nodal chamber. Index `1` is the left chamber
(`y^(k+1)=0`); index `0` is the right chamber (`x^(k+1)=0`).
This presentation does not need `t^(k+1)=0` as a hypothesis: that equation follows
from the two imposed relations. -/
def exponentChamberEquiv (t : R) (k : ℕ) (i : Fin 2) :
    (AddMonoidAlgebra R exponentMonoid ⧸
      (Ideal.span {(single smoothingDegree 1 - single 0 t)} ⊔
      Ideal.span {(single (![xDegree, yDegree] i) (1 : R)) ^ (k + 1)})) ≃ₐ[R]
    (NodeAlgebra R[T;T⁻¹] (_root_.LaurentPolynomial.C t) ⧸
      Ideal.span {NodeAlgebra.coord (_root_.LaurentPolynomial.C t) i ^ (k + 1)}) := by
  let I : Ideal (AddMonoidAlgebra R exponentMonoid) :=
    Ideal.span {(single smoothingDegree 1 - single 0 t)}
  let J : Ideal (AddMonoidAlgebra R exponentMonoid) :=
    Ideal.span {(single (![xDegree, yDegree] i) 1) ^ (k + 1)}
  refine (DoubleQuot.quotQuotEquivQuotSupₐ R I J).symm.trans
    (Ideal.quotientEquivAlg _ _ (smoothingSpecializationEquiv R t) ?_)
  simp only [J, Ideal.map_span, Set.image_singleton, RingHom.coe_coe,
    Ideal.Quotient.mkₐ_eq_mk]
  simp only [I, map_pow, smoothingSpecializationEquiv_mk]
  fin_cases i <;> simp

/-- The chamber dictionary evaluates a monoid-algebra representative by the
polynomial dictionary followed by the nodal and chamber quotient maps. -/
@[simp]
theorem exponentChamberEquiv_mk (t : R) (k : ℕ) (i : Fin 2)
    (a : AddMonoidAlgebra R exponentMonoid) :
    exponentChamberEquiv R t k i (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _
        (NodeAlgebra.mk (_root_.LaurentPolynomial.C t) (exponentPolynomialEquiv R a)) := by
  simp only [exponentChamberEquiv, AlgEquiv.trans_apply,
    DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm,
    DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk, DoubleQuot.quotQuotMk,
    RingHom.comp_apply]
  -- The double-quotient formula uses the ring quotient map, whereas the
  -- transported ideal uses its algebra-hom version.
  erw [Ideal.quotientEquivAlg_mk]

/-- The inverse chamber dictionary lifts a polynomial representative, so it can
be used without unfolding either nodal presentation. -/
@[simp]
theorem exponentChamberEquiv_symm_mk (t : R) (k : ℕ) (i : Fin 2)
    (p : MvPolynomial (Fin 2) R[T;T⁻¹]) :
    (exponentChamberEquiv R t k i).symm
        (Ideal.Quotient.mk _ (NodeAlgebra.mk (_root_.LaurentPolynomial.C t) p)) =
      Ideal.Quotient.mk _ ((exponentPolynomialEquiv R).symm p) := by
  apply (exponentChamberEquiv R t k i).injective
  rw [AlgEquiv.apply_symm_apply, exponentChamberEquiv_mk, AlgEquiv.apply_symm_apply]

end Ring

end Mei.FocusFocus
