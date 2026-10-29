/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.MonoidAlgebra
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Overlap

/-!
# Exponent coordinates on the focus-focus overlap

Specializing the smoothing monomial and imposing both chamber cutoffs on the
focus-focus exponent algebra gives the truncated nodal overlap. Under this
identification, the exponent shear `(a,b,h) ↦ (a,b-a,h)` is exactly the upper
overlap map `x ↦ wx`, `y ↦ w⁻¹y`. Consequently the upper and lower wall maps
agree on the monoid-algebra presentation, with its actual exponent transport.

We use `smoothingSpecializationEquiv`, Mathlib's double-quotient equivalence
and `Ideal.quotientEquivAlg`, and the existing overlap identity. The coordinate
conventions follow Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.2–2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

open scoped LaurentPolynomial

namespace Mei.FocusFocus

open TauCeti TauCeti.NodeAlgebra Mei.NodeAlgebra AddMonoidAlgebra
open scoped Mei.NodeAlgebra

variable (R : Type*) [CommRing R] (t : R) (k : ℕ)

/-- The exponent algebra with smoothing relation and both chamber cutoffs is
precisely the truncated nodal overlap. No nilpotence assumption on `t` is needed. -/
def exponentOverlapEquiv :
    (AddMonoidAlgebra R exponentMonoid ⧸
      (Ideal.span {single smoothingDegree 1 - single 0 t} ⊔
        Ideal.span {(single xDegree (1 : R)) ^ (k + 1),
          (single yDegree (1 : R)) ^ (k + 1)})) ≃ₐ[R]
      Overlap (_root_.LaurentPolynomial.C t) k := by
  let I : Ideal (AddMonoidAlgebra R exponentMonoid) :=
    Ideal.span {single smoothingDegree 1 - single 0 t}
  let J : Ideal (AddMonoidAlgebra R exponentMonoid) :=
    Ideal.span {(single xDegree 1) ^ (k + 1), (single yDegree 1) ^ (k + 1)}
  refine (DoubleQuot.quotQuotEquivQuotSupₐ R I J).symm.trans
    (Ideal.quotientEquivAlg _ _ (smoothingSpecializationEquiv R t) ?_)
  simp only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
    RingHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk]
  simp only [I, map_pow, smoothingSpecializationEquiv_mk]
  simp

/-- Evaluate any monoid-algebra representative by the polynomial dictionary and
the nodal and overlap quotient maps. -/
@[simp]
theorem exponentOverlapEquiv_mk (a : AddMonoidAlgebra R exponentMonoid) :
    exponentOverlapEquiv R t k (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _
        (NodeAlgebra.mk (_root_.LaurentPolynomial.C t) (exponentPolynomialEquiv R a)) := by
  simp only [exponentOverlapEquiv, AlgEquiv.trans_apply,
    DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm,
    DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk, DoubleQuot.quotQuotMk,
    RingHom.comp_apply]
  -- The double-quotient formula uses a ring map rather than its algebra-map version.
  erw [Ideal.quotientEquivAlg_mk]
  rw [smoothingSpecializationEquiv_mk]

/-- The inverse dictionary lifts a polynomial representative of an overlap
class, independently of its representative. -/
@[simp]
theorem exponentOverlapEquiv_symm_mk (p : MvPolynomial (Fin 2) R[T;T⁻¹]) :
    (exponentOverlapEquiv R t k).symm
        (Ideal.Quotient.mk _ (NodeAlgebra.mk (_root_.LaurentPolynomial.C t) p)) =
      Ideal.Quotient.mk _ ((exponentPolynomialEquiv R).symm p) := by
  apply (exponentOverlapEquiv R t k).injective
  rw [AlgEquiv.apply_symm_apply, exponentOverlapEquiv_mk, AlgEquiv.apply_symm_apply]

/-- A monomial retains its Laurent coefficient and its two coordinate powers
in the overlap. -/
theorem exponentOverlapEquiv_single (q : exponentMonoid) (r : R) :
    exponentOverlapEquiv R t k (Ideal.Quotient.mk _ (single q r)) =
      algebraMap R[T;T⁻¹] (Overlap (_root_.LaurentPolynomial.C t) k)
          (single q.val.2.1 r) *
        Ideal.Quotient.mk _ (coord (_root_.LaurentPolynomial.C t) 0) ^ rightOrder q *
        Ideal.Quotient.mk _ (coord (_root_.LaurentPolynomial.C t) 1) ^ leftOrder q := by
  rw [exponentOverlapEquiv_mk, exponentPolynomialEquiv_single,
    MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial]
  simp

/-- The monoid shear and the nodal upper transition agree on every coefficient
monomial, including those killed by the cutoffs. -/
private theorem upperOverlap_exponentOverlapEquiv_single (q : exponentMonoid) (r : R) :
    upperOverlap t k (exponentOverlapEquiv R t k (Ideal.Quotient.mk _ (single q r))) =
      exponentOverlapEquiv R t k (Ideal.Quotient.mk _ (single (upperMonoid q) r)) := by
  have he := exponentEquiv_upperMonoid q
  have hb := congrArg Prod.fst he
  have hl : leftOrder (upperMonoid q) = leftOrder q := by simp
  have hr : rightOrder (upperMonoid q) = rightOrder q := by simp
  simp only [exponentEquiv_apply] at hb
  rw [exponentOverlapEquiv_single, exponentOverlapEquiv_single,
    map_mul, map_mul, map_pow, map_pow, AlgEquiv.commutes,
    upperOverlap_mk_coord_zero, upperOverlap_mk_coord_one, hl, hr, hb]
  simp only [mul_pow, ← map_pow, _root_.LaurentPolynomial.single_eq_C_mul_T,
    _root_.LaurentPolynomial.T_pow]
  simp only [mul_one, mul_neg_one]
  rw [_root_.LaurentPolynomial.T_sub, _root_.LaurentPolynomial.T_add]
  simp only [map_mul]
  ring

/-- The exponent shear specializes to the upper overlap transition on every
monoid-algebra representative, not only on individual monomials. -/
private theorem upperOverlap_exponentOverlapEquiv_mk (a : AddMonoidAlgebra R exponentMonoid) :
    upperOverlap t k (exponentOverlapEquiv R t k (Ideal.Quotient.mk _ a)) =
      exponentOverlapEquiv R t k
        (Ideal.Quotient.mk _ (domCongr R R upperMonoid a)) := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single q r =>
    rw [domCongr_single, upperOverlap_exponentOverlapEquiv_single]

private theorem upperMonoid_map_overlapIdeal :
    (Ideal.span {single smoothingDegree 1 - single 0 t} ⊔
      Ideal.span {(single xDegree (1 : R)) ^ (k + 1),
        (single yDegree (1 : R)) ^ (k + 1)}).map
          (domCongr R R upperMonoid : AddMonoidAlgebra R exponentMonoid →+*
            AddMonoidAlgebra R exponentMonoid) =
      (Ideal.span {single smoothingDegree 1 - single 0 t} ⊔
        Ideal.span {(single xDegree (1 : R)) ^ (k + 1),
          (single yDegree (1 : R)) ^ (k + 1)}) := by
  have hmem (a : AddMonoidAlgebra R exponentMonoid) :
      domCongr R R upperMonoid a ∈
          (Ideal.span {single smoothingDegree 1 - single 0 t} ⊔
            Ideal.span {(single xDegree (1 : R)) ^ (k + 1),
              (single yDegree (1 : R)) ^ (k + 1)}) ↔
        a ∈ (Ideal.span {single smoothingDegree 1 - single 0 t} ⊔
          Ideal.span {(single xDegree (1 : R)) ^ (k + 1),
            (single yDegree (1 : R)) ^ (k + 1)}) := by
    have he := upperOverlap_exponentOverlapEquiv_mk R t k a
    have hz := congrArg (fun z => z = 0) he
    simpa only [map_eq_zero_iff _ (exponentOverlapEquiv R t k).injective,
      map_eq_zero_iff _ (upperOverlap t k).injective,
      Ideal.Quotient.eq_zero_iff_mem] using (Iff.of_eq hz.symm)
  have hf : Function.Surjective
      (domCongr R R upperMonoid : AddMonoidAlgebra R exponentMonoid →+*
        AddMonoidAlgebra R exponentMonoid) := (domCongr R R upperMonoid).surjective
  ext a
  refine (Ideal.mem_map_iff_of_surjective _ hf).trans ?_
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hmem b).mpr hb
  · intro ha
    obtain ⟨b, rfl⟩ := (domCongr R R upperMonoid).surjective a
    exact ⟨b, (hmem b).mp ha, rfl⟩

/-- The exponent shear descends to an automorphism after imposing the smoothing
relation and both chamber cutoffs. -/
def upperExponentOverlap :
    (AddMonoidAlgebra R exponentMonoid ⧸
      (Ideal.span {single smoothingDegree 1 - single 0 t} ⊔
        Ideal.span {(single xDegree (1 : R)) ^ (k + 1),
          (single yDegree (1 : R)) ^ (k + 1)})) ≃ₐ[R]
    (AddMonoidAlgebra R exponentMonoid ⧸
      (Ideal.span {single smoothingDegree 1 - single 0 t} ⊔
        Ideal.span {(single xDegree (1 : R)) ^ (k + 1),
          (single yDegree (1 : R)) ^ (k + 1)})) :=
  Ideal.quotientEquivAlg _ _ (domCongr R R upperMonoid)
    (upperMonoid_map_overlapIdeal R t k).symm

/-- On quotient representatives the descended transition is the original
monoid-algebra shear. -/
@[simp]
theorem upperExponentOverlap_mk (a : AddMonoidAlgebra R exponentMonoid) :
    upperExponentOverlap R t k (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (domCongr R R upperMonoid a) := by
  exact Ideal.quotientEquivAlg_mk _ _ _ a

/-- The inverse transition is induced by the inverse exponent shear. -/
@[simp]
theorem upperExponentOverlap_symm_mk (a : AddMonoidAlgebra R exponentMonoid) :
    (upperExponentOverlap R t k).symm (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ ((domCongr R R upperMonoid).symm a) := by
  apply (upperExponentOverlap R t k).injective
  rw [AlgEquiv.apply_symm_apply, upperExponentOverlap_mk, AlgEquiv.apply_symm_apply]

/-- The overlap dictionary intertwines the two actual quotient automorphisms. -/
@[simp]
theorem exponentOverlapEquiv_upperExponentOverlap (a) :
    exponentOverlapEquiv R t k (upperExponentOverlap R t k a) =
      upperOverlap t k (exponentOverlapEquiv R t k a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [upperExponentOverlap_mk, upperOverlap_exponentOverlapEquiv_mk]

/-- The upper crossing with transported exponents agrees with the lower
crossing on the entire exponent-algebra presentation of the overlap. -/
theorem lowerWallMap_exponentOverlapEquiv (a) :
    lowerWallMap t k (exponentOverlapEquiv R t k a) =
      upperWallMap t k
        (exponentOverlapEquiv R t k (upperExponentOverlap R t k a)) := by
  rw [exponentOverlapEquiv_upperExponentOverlap,
    lowerWallMap_eq_upperWallMap_comp_upperOverlap, AlgHom.comp_apply,
    AlgEquiv.toAlgHom_apply]

end Mei.FocusFocus
