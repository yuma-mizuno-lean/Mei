/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Pentagon

/-!
# Ordered and antiordered products of dilogarithm factors

In the completed skew group of a positively graded skew Lie algebra, the ray label
`Ψ[n]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jn}/j²)` at a nonzero allowed degree `n` and a
coefficient `c` is a *dilogarithm factor*. The coefficient is carried by each factor of a
product, because it is not determined by the degree: the normalized factor `Ψ[tn]^(s κ(tn))`
of the ordinary binomial scattering input takes a coefficient that depends on the degree
through the rational ray index `κ` of `SkewLatticeDatum.sublattice.toAddSubgroup.rayIndex`
(used in `Mei.Geometry.ScatteringDiagram.Skew.Dilogarithm`). A product therefore pairs each
nonzero allowed degree with its own coefficient, and a normalized single factor is the case
of one such pair.

Ordering is read from the skew form: a pair `a, b` is ordered when `{a,b} ≥ 0` and antiordered
when `{a,b} ≤ 0`. The two readings overlap at `{a,b} = 0`; such a pair is collinear, its
factors commute (`SkewLieAlgebra.commute_rayExp_of_eq_zero`) and may be kept in a fixed tie
order. For a pair whose coefficient satisfies `c {a,b} = -1`, the pentagon identity of
`Mei.Geometry.ScatteringDiagram.Skew.Pentagon` rewrites the product `Ψ[a]^c Ψ[b]^c` as the
product `Ψ[b]^c Ψ[b+a]^c Ψ[a]^c`, and for an antiordered pair the replacement `b, b+a, a` has
both adjacent pairs ordered. This is the exchange used when ordering a finite product of
dilogarithm factors.

The file records the exchange for an arbitrary segment of a list, the orderedness of the
adjacent pairs of the exchanged triple, and the zero-form case, in which every pair is ordered
and no exchange is needed. The exchange is the shared-coefficient one supplied by the pentagon:
it applies to an adjacent pair whose coefficients agree, which is the shape the pentagon has,
and it does not by itself exchange a pair with two different coefficients. The rank-two
wall-crossing formula of Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2
(arXiv:2111.00800v6), and Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §8.1 (arXiv:2503.03719v1), applies an adjacent exchange of this shape repeatedly.
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries PositiveDegrees

variable {R Γ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [PartialOrder R] [IsOrderedAddMonoid R]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) (d : PositiveDegrees Γ)

/-- The dilogarithm factor `Ψ[n]^c` at a nonzero allowed degree `n` with coefficient `c`. A
normalized factor is one such factor, with `c` its normalized coefficient. -/
def dilogFactor (n : NonzeroDegree d) (c : R) :
    d.completedBCHGroup (positiveGrading β hβ d) :=
  rayExp β hβ n.mem n.ne_zero (c • negDilogNeg R)

omit [PartialOrder R] [IsOrderedAddMonoid R] in
/-- The defining ray label of a dilogarithm factor. -/
theorem dilogFactor_def (n : NonzeroDegree d) (c : R) :
    dilogFactor β hβ d n c = rayExp β hβ n.mem n.ne_zero (c • negDilogNeg R) := (rfl)

/-- The product of a finite list of dilogarithm factors, each with its own coefficient. -/
def dilogFactorProduct (l : List (NonzeroDegree d × R)) :
    d.completedBCHGroup (positiveGrading β hβ d) :=
  (l.map fun p => dilogFactor β hβ d p.1 p.2).prod

omit [PartialOrder R] [IsOrderedAddMonoid R] in
@[simp]
theorem dilogFactorProduct_nil : dilogFactorProduct β hβ d [] = 1 := by
  simp [dilogFactorProduct]

omit [PartialOrder R] [IsOrderedAddMonoid R] in
@[simp]
theorem dilogFactorProduct_cons (p : NonzeroDegree d × R) (l : List (NonzeroDegree d × R)) :
    dilogFactorProduct β hβ d (p :: l) =
      dilogFactor β hβ d p.1 p.2 * dilogFactorProduct β hβ d l := by
  simp [dilogFactorProduct]

/-- A pair of dilogarithm degrees is ordered when its skew pairing is nonnegative; this is the
adjacent-pair relation of an ordered sequence of degrees. -/
def Ordered (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (d : PositiveDegrees Γ)
    (a b : NonzeroDegree d) : Prop := 0 ≤ β (a : Γ) (b : Γ)

omit [Algebra ℚ R] [DecidableEq Γ] [IsOrderedAddMonoid R] in
@[simp]
theorem ordered_iff {a b : NonzeroDegree d} : Ordered β d a b ↔ 0 ≤ β (a : Γ) (b : Γ) :=
  (Iff.rfl)

/-- A pair of dilogarithm degrees is antiordered when its skew pairing is nonpositive; this is
the adjacent-pair relation of an antiordered sequence of degrees. A collinear pair is both
ordered and antiordered; its factors commute and may be kept in a fixed tie order. -/
def Antiordered (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (d : PositiveDegrees Γ)
    (a b : NonzeroDegree d) : Prop := β (a : Γ) (b : Γ) ≤ 0

omit [Algebra ℚ R] [DecidableEq Γ] [IsOrderedAddMonoid R] in
@[simp]
theorem antiordered_iff {a b : NonzeroDegree d} : Antiordered β d a b ↔ β (a : Γ) (b : Γ) ≤ 0 :=
  (Iff.rfl)

omit [PartialOrder R] [IsOrderedAddMonoid R] in
/-- **Adjacent exchange, shared coefficient.** If `c {a,b} = -1`, the product of
`l₁ ++ (a,c) :: (b,c) :: l₂` is unchanged when the adjacent pair `a, b` is replaced by the triple
`b, b+a, a`, all at that same coefficient. At `l₁ = l₂ = []` this is
`Ψ[a]^c Ψ[b]^c = Ψ[b]^c Ψ[b+a]^c Ψ[a]^c`, the pentagon identity of
`Mei.Geometry.ScatteringDiagram.Skew.Pentagon`; for an antiordered pair the replacement is the
ordered one of `Antiordered.ordered_add_left` and `Antiordered.ordered_add_right`.

The hypothesis is the pentagon's own: `Pentagon.rayExp_smul_negDilogNeg_pentagon` carries one
coefficient `c` on `a`, `b` and `a + b`, so this lemma exchanges a pair whose two coefficients
already agree. An exchange of a pair with different coefficients is not a consequence of that
identity and is not proved here. -/
theorem dilogFactorProduct_append_cons_cons_eq_of_mul_form_eq_neg_one (hβ : β.IsAlt)
    (l₁ l₂ : List (NonzeroDegree d × R)) {a b : NonzeroDegree d} {c : R}
    (hc : c * β (a : Γ) (b : Γ) = -1) :
    dilogFactorProduct β hβ d (l₁ ++ (a, c) :: (b, c) :: l₂) =
      dilogFactorProduct β hβ d (l₁ ++ (b, c) :: (a + b, c) :: (a, c) :: l₂) := by
  have hba : c * β (b : Γ) (a : Γ) = 1 := by
    rw [← hβ.neg (a : Γ) (b : Γ), mul_neg, hc, neg_neg]
  -- The pentagon is stated for the reversed pair, at the ray label of `b + a`; the subtype
  -- proofs of the summed degree are irrelevant, and `add_comm` reconciles the order.
  have hex : dilogFactor β hβ d a c * dilogFactor β hβ d b c =
      dilogFactor β hβ d b c * dilogFactor β hβ d (a + b) c * dilogFactor β hβ d a c := by
    simpa only [dilogFactor, NonzeroDegree.coe_add, NonzeroDegree.mem, NonzeroDegree.ne_zero,
      add_comm] using
      rayExp_smul_negDilogNeg_pentagon β hβ d b.mem a.mem b.ne_zero a.ne_zero (c := c) hba
  simp only [dilogFactorProduct, List.map_append, List.map_cons, List.prod_append,
    List.prod_cons]
  rw [← mul_assoc (dilogFactor β hβ d a c) (dilogFactor β hβ d b c), hex]
  ac_rfl

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- The right adjacent pair of the exchanged triple is ordered. -/
theorem Antiordered.ordered_add_right (hβ : β.IsAlt) {a b : NonzeroDegree d}
    (hanti : Antiordered β d a b) : Ordered β d b (a + b) := by
  have hba : 0 ≤ β (b : Γ) (a : Γ) := by
    rw [← LinearMap.IsAlt.neg hβ (a : Γ) (b : Γ)]
    exact neg_nonneg.mpr hanti
  simpa only [ordered_iff, NonzeroDegree.coe_add, map_add,
    LinearMap.IsAlt.self_eq_zero hβ, add_zero] using hba

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- The left adjacent pair of the exchanged triple is ordered. -/
theorem Antiordered.ordered_add_left (hβ : β.IsAlt) {a b : NonzeroDegree d}
    (hanti : Antiordered β d a b) : Ordered β d (a + b) a := by
  have hba : 0 ≤ β (b : Γ) (a : Γ) := by
    rw [← LinearMap.IsAlt.neg hβ (a : Γ) (b : Γ)]
    exact neg_nonneg.mpr hanti
  simpa only [ordered_iff, NonzeroDegree.coe_add, map_add, LinearMap.add_apply,
    LinearMap.IsAlt.self_eq_zero hβ, zero_add] using hba

end Mei.SkewLieAlgebra

namespace Mei.SkewLieAlgebra

open PositiveDegrees

variable {R Γ : Type*} [CommRing R] [PartialOrder R] [AddCommGroup Γ]
  {d : PositiveDegrees Γ}

/-- In the zero-form case every pair of degrees is ordered, so a list of dilogarithm factors
needs no exchange. -/
theorem ordered_of_form_eq_zero (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hform : β = 0)
    (a b : NonzeroDegree d) : Ordered β d a b := by
  rw [ordered_iff, hform]
  simp

end Mei.SkewLieAlgebra
