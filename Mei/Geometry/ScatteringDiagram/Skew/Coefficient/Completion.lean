/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Coefficient
public import Mei.Geometry.ScatteringDiagram.Skew.AdaptedBasis
public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Algebra.MonoidAlgebra.Grading
public import Mei.RingTheory.FilteredAlgebra.Equiv
public import Mei.RingTheory.MvPowerSeries.Completion
public import Mei.RingTheory.MvPowerSeries.Algebra

/-!
# Principal coefficients as power series

Choose free additive coordinates on the positive unfrozen monoid, with total
coordinate degree equal to its positive degree. The principal coefficient algebra
is then a polynomial algebra over the Laurent character algebra. Its native
positive-increment filtration becomes the powers of the ideal of variables, so
its completion is the corresponding multivariate power series algebra.

The coefficient formula retains both the unfrozen exponent and the character
exponent. In particular, characters have filtration order zero even when the
skew form is degenerate. The inverse at each finite order is total-degree
truncation followed by the inverse polynomial dictionary and the quotient map.

For an adapted basis, the natural coordinates of the unfrozen basis supply these
free coordinates, giving `R[[Q_pr]] = R[M°][[t_i]]` with one variable `t_i` for each
unfrozen index (`AdaptedBasis.principalCoefficientCompletionEquiv`).

This uses Mathlib's `AddMonoidAlgebra.domCongr` and `curryAlgEquiv`, and Mei's
`principalCompletionEquiv`. The principal coefficient model follows
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open _root_.AddMonoidAlgebra

variable {N R ι : Type*} [AddCommGroup N]
  (D : SkewLatticeDatum N) (d : PositiveDegrees D.unfrozen)
  (e : d.monoid ≃+ (ι →₀ ℕ))

local notation "M" => Module.Dual ℤ D.sublattice
local notation "Q" => D.principalCoefficientMonoid d

private def coefficientExponentEquiv : Q ≃+ ((ι →₀ ℕ) × M) := by
  have hQ : Q = (⊤ : AddSubmonoid M).prod d.monoid := by
    ext p
    simp only [mem_principalCoefficientMonoid, AddSubmonoid.mem_prod,
      AddSubmonoid.mem_top, true_and]
  exact (AddEquiv.addSubmonoidCongr hQ).trans (((AddSubmonoid.prodEquiv ⊤ d.monoid).trans
    (AddEquiv.prodCongr AddSubmonoid.topEquiv e)).trans AddEquiv.prodComm)

section Polynomial

variable [CommSemiring R]

/-- Free positive coordinates identify the native principal coefficient algebra
with polynomials over the character monoid algebra. -/
def principalCoefficientPolynomialEquiv : R[Q] ≃ₐ[R] MvPolynomial ι R[M] :=
  (domCongr R R (D.coefficientExponentEquiv d e)).trans (curryAlgEquiv R)

/-- The polynomial dictionary sends a principal monomial to its character
coefficient times its positive-coordinate monomial. -/
@[simp]
theorem principalCoefficientPolynomialEquiv_single (p : Q) (r : R) :
    D.principalCoefficientPolynomialEquiv d e (single p r) =
      MvPolynomial.monomial
        (e ⟨p.val.2, (D.mem_principalCoefficientMonoid d p.val).mp p.property⟩)
        (single p.val.1 r) := by
  have hp : D.coefficientExponentEquiv d e p =
      (e ⟨p.val.2, (D.mem_principalCoefficientMonoid d p.val).mp p.property⟩,
        p.val.1) := rfl
  simp only [principalCoefficientPolynomialEquiv, AlgEquiv.trans_apply,
    domCongr_single, hp, curryAlgEquiv_single, MvPolynomial.single_eq_monomial]

/-- The dictionary preserves each individual character and positive-degree coefficient. -/
@[simp]
theorem coeff_principalCoefficientPolynomialEquiv (a : R[Q]) (n : ι →₀ ℕ) (m : M) :
    ((D.principalCoefficientPolynomialEquiv d e a).coeff n).coeff m =
      a.coeff ⟨(m, e.symm n), by simp⟩ := by
  simp only [principalCoefficientPolynomialEquiv, AlgEquiv.trans_apply]
  rw [← coeff_curryAlgEquiv_symm, AlgEquiv.symm_apply_apply, coeff_domCongr]
  rfl

end Polynomial

local notation "F" => TropicalVertexCoefficientAction.filtration
  (R := R) (D.principalPositiveDegrees d) Q

section FreeCoordinates

variable (he : ∀ n : d.monoid, d.degree n = ((e n).degree : ℤ))

include he

section Filtration

variable [CommSemiring R]

/-- Native principal filtration terms are exactly powers of the polynomial
variable ideal, in coordinates whose total degree is the positive degree. -/
theorem comap_idealOfVars_pow_principalCoefficientPolynomialEquiv (k : ℕ) :
    ((MvPolynomial.idealOfVars ι R[M]) ^ k).comap
      (D.principalCoefficientPolynomialEquiv (R := R) d e).toAlgHom = (F).ideal k := by
  ext a
  rw [Ideal.mem_comap, MvPolynomial.mem_pow_idealOfVars_iff',
    D.mem_principalCoefficientFiltration_ideal_iff]
  simp only [AlgEquiv.coe_toAlgHom]
  constructor
  · intro ha p hp
    let n : d.monoid := ⟨p.val.2, (D.mem_principalCoefficientMonoid d p.val).mp p.property⟩
    by_contra h
    have hd : d.degree p.val.2 = ((e n).degree : ℤ) := he n
    have hn : (e n).degree < k := by omega
    have hz := congrArg (fun b : R[M] => b.coeff p.val.1) (ha (e n) hn)
    simp only [coeff_principalCoefficientPolynomialEquiv, coeff_zero, Finsupp.zero_apply] at hz
    have hp' : (⟨(p.val.1, e.symm (e n)), by simp⟩ : Q) = p := by
      apply Subtype.ext
      simp [n]
    rw [hp'] at hz
    exact (Finsupp.mem_support_iff.mp hp) hz
  · intro ha n hn
    apply _root_.AddMonoidAlgebra.coeff_injective
    ext m
    simp only [coeff_principalCoefficientPolynomialEquiv, coeff_zero, Finsupp.zero_apply]
    by_contra h
    have hp : (k : ℤ) ≤ d.degree (e.symm n).val :=
      ha ⟨(m, e.symm n), by simp⟩ (Finsupp.mem_support_iff.mpr h)
    have hd := he (e.symm n)
    simp only [AddEquiv.apply_symm_apply] at hd
    omega

end Filtration

variable [CommRing R] [Finite ι]

/-- The completion of the native principal coefficient algebra is the power
series algebra in free positive coordinates over the character algebra. -/
def principalCoefficientCompletionEquiv :
    (F).completion ≃ₐ[R] MvPowerSeries ι R[M] :=
  ((F).completionEquiv (AlgFiltration.ofIdeal (MvPolynomial.idealOfVars ι R[M]))
    (D.principalCoefficientPolynomialEquiv d e) (fun k => by
      simpa only [AlgFiltration.ofIdeal_ideal] using
        D.comap_idealOfVars_pow_principalCoefficientPolynomialEquiv d e he k)).trans
    ((principalCompletionEquiv ι R[M]).restrictScalars R)

/-- Completing a finite principal coefficient expression gives its polynomial
dictionary, viewed as a power series. -/
@[simp]
theorem principalCoefficientCompletionEquiv_toCompletion (a : R[Q]) :
    D.principalCoefficientCompletionEquiv d e he ((F).toCompletion a) =
      (D.principalCoefficientPolynomialEquiv d e a : MvPowerSeries ι R[M]) := by
  simp only [principalCoefficientCompletionEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgFiltration.completionEquiv_toCompletion,
    principalCompletionEquiv_toCompletion]

/-- At finite order the inverse dictionary truncates total degree, converts
back to the native coefficient algebra, and takes its quotient class. -/
@[simp]
theorem projection_principalCoefficientCompletionEquiv_symm
    (k : ℕ) (f : MvPowerSeries ι R[M]) :
    (F).projection k ((D.principalCoefficientCompletionEquiv d e he).symm f) =
      Ideal.Quotient.mk ((F).ideal (k + 1))
        ((D.principalCoefficientPolynomialEquiv d e).symm (f.truncTotal (k + 1))) := by
  simp [principalCoefficientCompletionEquiv, AlgEquiv.symm_trans_apply,
    AlgEquiv.symm_restrictScalars, AlgFiltration.projection_completionEquiv_symm]

/-- Any native representative of a finite projection recovers the power series
coefficients through that order, including the individual character coefficients. -/
theorem coeff_principalCoefficientCompletionEquiv_eq_of_projection_eq
    (x : (F).completion) (k : ℕ) (a : R[Q])
    (ha : Ideal.Quotient.mk ((F).ideal (k + 1)) a = (F).projection k x)
    (n : ι →₀ ℕ) (hn : n.degree ≤ k) (m : M) :
    (MvPowerSeries.coeff n (D.principalCoefficientCompletionEquiv d e he x)).coeff m =
      a.coeff ⟨(m, e.symm n), by simp⟩ := by
  let G := AlgFiltration.ofIdeal (MvPolynomial.idealOfVars ι R[M])
  let E := D.principalCoefficientPolynomialEquiv (R := R) d e
  have hE : ∀ j, (G.ideal j).comap E.toAlgHom = (F).ideal j := fun j => by
    simpa only [G, AlgFiltration.ofIdeal_ideal] using
      D.comap_idealOfVars_pow_principalCoefficientPolynomialEquiv d e he j
  have hp : Ideal.Quotient.mk (G.ideal (k + 1)) (E a) =
      G.projection k ((F).completionEquiv G E hE x) := by
    rw [AlgFiltration.projection_completionEquiv, ← ha]
    simp
  have h := coeff_principalCompletionEquiv_eq_of_projection_eq ι R[M]
    ((F).completionEquiv G E hE x) k (E a) hp n hn
  have hc := congrArg (fun b : R[M] => b.coeff m) h
  simpa only [principalCoefficientCompletionEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, E, coeff_principalCoefficientPolynomialEquiv] using hc

end FreeCoordinates

section Adapted

variable [CommRing R] {D} {J : Type*} (B : D.AdaptedBasis J)

local notation "F₀" => TropicalVertexCoefficientAction.filtration
  (R := R) (D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees)
  (D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees)

/-- In the coordinates of an adapted basis, the completed principal coefficient algebra on
`P_N = ∑_{i ∈ I_uf} ℕ e_i` is the power series algebra `R[M°][[t_i]]`, with one variable for
each unfrozen index. -/
def AdaptedBasis.principalCoefficientCompletionEquiv :
    (F₀).completion ≃ₐ[R] MvPowerSeries B.unfrozenIndex R[M] :=
  D.principalCoefficientCompletionEquiv _ B.unfrozenBasis.positiveDegreesMonoidEquiv
    B.unfrozenBasis.positiveDegrees_degree_eq_degree_positiveDegreesMonoidEquiv

/-- In adapted coordinates the principal monomial `z^m t^n` is the power series monomial
whose exponent of `t_i` is the `i`-th coordinate of `n`. -/
@[simp]
theorem AdaptedBasis.principalCoefficientCompletionEquiv_toCompletion_single
    (p : D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees) (r : R) :
    B.principalCoefficientCompletionEquiv ((F₀).toCompletion (single p r)) =
      MvPowerSeries.monomial
        (B.unfrozenBasis.positiveDegreesMonoidEquiv
          ⟨p.val.2, (D.mem_principalCoefficientMonoid _ p.val).mp p.property⟩)
        (single p.val.1 r) := by
  rw [AdaptedBasis.principalCoefficientCompletionEquiv,
    principalCoefficientCompletionEquiv_toCompletion, principalCoefficientPolynomialEquiv_single,
    MvPolynomial.coe_monomial]

end Adapted

end Mei.SkewLatticeDatum
