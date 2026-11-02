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
coefficient `c` is a *dilogarithm factor*. The coefficient is not determined by the degree: the
normalized factor `Ψ[tn]^(s κ(tn))` of the ordinary binomial scattering input is the special
case at a positive multiple `t • n` of a primitive degree with `s, t > 0` and `c = s κ(tn)`,
where `κ` is the rational ray index of the degree with respect to the finite-index sublattice on
which the form is integral (`SkewLatticeDatum.sublattice.toAddSubgroup.rayIndex`, used in
`Mei.Geometry.ScatteringDiagram.Skew.Dilogarithm`). The ordering theory below is stated for an
arbitrary coefficient, because the exchange uses `c` only through the scalar equation
`c {a,b} = -1`; a normalized factor is obtained by instantiating `c` at its normalized
coefficient.

Ordering is read from the skew form: a pair `a, b` is ordered when `{a,b} ≥ 0` and antiordered
when `{a,b} ≤ 0`. The two readings overlap at `{a,b} = 0`; such a pair is collinear, its factors
commute (`SkewLieAlgebra.commute_rayExp_of_eq_zero`) and may be kept in a fixed tie order. For a
pair whose coefficient satisfies `c {a,b} = -1`, the pentagon identity of
`Mei.Geometry.ScatteringDiagram.Skew.Pentagon` rewrites the product `Ψ[a]^c Ψ[b]^c` as the
product `Ψ[b]^c Ψ[b+a]^c Ψ[a]^c`, and for an antiordered pair the replacement `b, b+a, a` has
both adjacent pairs ordered. This is the exchange used when ordering a finite product of
dilogarithm factors.

The file records the exchange for an arbitrary segment of a list, the orderedness of the
adjacent pairs of the exchanged triple, and the zero-form case, in which every pair is ordered
and no exchange is needed.

The rank-two wall-crossing formula of Nakanishi, *Cluster algebras and scattering
diagrams, Part III*, §5.2 (arXiv:2111.00800v6), and Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, §8.1 (arXiv:2503.03719v1),
applies this exchange repeatedly. The statements here are the segment exchange and the zero-form
base case; they retain the exact completed label, hence every finite truncation and the assembly
of the truncations.
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries

section Degrees

variable {Γ : Type*} [AddCommGroup Γ] {d : PositiveDegrees Γ}

/-- A nonzero allowed degree of `d`, used to index a dilogarithm factor. -/
abbrev DilogDegree (d : PositiveDegrees Γ) : Type _ := {n : Γ // n ∈ d.monoid ∧ n ≠ 0}

@[simp]
theorem DilogDegree.coe_mk (n : Γ) (hn : n ∈ d.monoid) (hn0 : n ≠ 0) :
    ((⟨n, hn, hn0⟩ : DilogDegree d) : Γ) = n := (rfl)

theorem DilogDegree.mem (n : DilogDegree d) : (n : Γ) ∈ d.monoid := n.property.1

theorem DilogDegree.ne_zero (n : DilogDegree d) : (n : Γ) ≠ 0 := n.property.2

/-- The sum of two dilogarithm degrees, which is a nonzero allowed degree because the degree is
positive on nonzero allowed degrees. -/
def DilogDegree.add (a b : DilogDegree d) : DilogDegree d :=
  ⟨(a : Γ) + (b : Γ), d.monoid.add_mem a.mem b.mem, d.add_ne_zero a.mem b.mem a.ne_zero⟩

@[simp]
theorem DilogDegree.coe_add (a b : DilogDegree d) :
    ((DilogDegree.add a b : DilogDegree d) : Γ) = (a : Γ) + (b : Γ) := (rfl)

end Degrees

variable {R Γ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [PartialOrder R] [IsOrderedAddMonoid R]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) (d : PositiveDegrees Γ)

/-- The dilogarithm factor `Ψ[n]^c` at a nonzero allowed degree `n` with coefficient `c`. The
normalized factor `Ψ[tn]^(s κ(tn))` of the ordinary binomial scattering input is the special case
at a positive multiple `t • n` of a primitive degree with `c = s κ(tn)`. -/
def dilogFactor (n : DilogDegree d) (c : R) : d.completedBCHGroup (positiveGrading β hβ d) :=
  rayExp β hβ n.mem n.ne_zero (c • negDilogNeg R)

omit [PartialOrder R] [IsOrderedAddMonoid R] in
/-- The defining ray label of a dilogarithm factor. -/
@[simp]
theorem dilogFactor_def (n : DilogDegree d) (c : R) :
    dilogFactor β hβ d n c = rayExp β hβ n.mem n.ne_zero (c • negDilogNeg R) := (rfl)

/-- The product of the dilogarithm factors of a finite list, all at the same coefficient. -/
def dilogFactorProduct (l : List (DilogDegree d)) (c : R) :
    d.completedBCHGroup (positiveGrading β hβ d) :=
  (l.map fun n => dilogFactor β hβ d n c).prod

omit [PartialOrder R] [IsOrderedAddMonoid R] in
@[simp]
theorem dilogFactorProduct_nil (c : R) : dilogFactorProduct β hβ d [] c = 1 := by
  simp [dilogFactorProduct]

omit [PartialOrder R] [IsOrderedAddMonoid R] in
@[simp]
theorem dilogFactorProduct_cons (a : DilogDegree d) (l : List (DilogDegree d)) (c : R) :
    dilogFactorProduct β hβ d (a :: l) c =
      dilogFactor β hβ d a c * dilogFactorProduct β hβ d l c := by
  simp [dilogFactorProduct]

/-- A pair of dilogarithm degrees is ordered when its skew pairing is nonnegative; this is the
adjacent-pair relation of an ordered sequence of degrees. -/
def Ordered (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (d : PositiveDegrees Γ)
    (a b : DilogDegree d) : Prop := 0 ≤ β (a : Γ) (b : Γ)

omit [Algebra ℚ R] [DecidableEq Γ] [IsOrderedAddMonoid R] in
@[simp]
theorem ordered_iff {a b : DilogDegree d} : Ordered β d a b ↔ 0 ≤ β (a : Γ) (b : Γ) := (Iff.rfl)

/-- A pair of dilogarithm degrees is antiordered when its skew pairing is nonpositive; this is the
adjacent-pair relation of an antiordered sequence of degrees. A collinear pair is both ordered and
antiordered; its factors commute and may be kept in a fixed tie order. -/
def Antiordered (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (d : PositiveDegrees Γ)
    (a b : DilogDegree d) : Prop := β (a : Γ) (b : Γ) ≤ 0

omit [Algebra ℚ R] [DecidableEq Γ] [IsOrderedAddMonoid R] in
@[simp]
theorem antiordered_iff {a b : DilogDegree d} : Antiordered β d a b ↔ β (a : Γ) (b : Γ) ≤ 0 :=
  (Iff.rfl)

omit [PartialOrder R] [IsOrderedAddMonoid R] in
/-- **Adjacent exchange.** If `c {a,b} = -1`, the product of `l₁ ++ a :: b :: l₂` is unchanged
when the adjacent pair `a, b` is replaced by the triple `b, b+a, a`. At `l₁ = l₂ = []` this is
`Ψ[a]^c Ψ[b]^c = Ψ[b]^c Ψ[b+a]^c Ψ[a]^c`, the pentagon identity of
`Mei.Geometry.ScatteringDiagram.Skew.Pentagon`; for an antiordered pair the replacement is the
ordered one of `ordered_of_antiordered_add`. -/
theorem dilogFactorProduct_append_cons_cons_eq_of_mul_form_eq_neg_one (hβ : β.IsAlt)
    (l₁ l₂ : List (DilogDegree d)) {a b : DilogDegree d} {c : R}
    (hc : c * β (a : Γ) (b : Γ) = -1) :
    dilogFactorProduct β hβ d (l₁ ++ a :: b :: l₂) c =
      dilogFactorProduct β hβ d (l₁ ++ b :: DilogDegree.add a b :: a :: l₂) c := by
  have hba : c * β (b : Γ) (a : Γ) = 1 := by
    rw [← hβ.neg (a : Γ) (b : Γ), mul_neg, hc, neg_neg]
  -- The pentagon is stated for the reversed pair, at the ray label of `b + a`; the subtype
  -- proofs of the summed degree are irrelevant, and `add_comm` reconciles the order.
  have hex : dilogFactor β hβ d a c * dilogFactor β hβ d b c =
      dilogFactor β hβ d b c * dilogFactor β hβ d (DilogDegree.add a b) c *
        dilogFactor β hβ d a c := by
    simpa only [dilogFactor, DilogDegree.coe_add, DilogDegree.mem, DilogDegree.ne_zero,
      add_comm] using
      rayExp_smul_negDilogNeg_pentagon β hβ d b.mem a.mem b.ne_zero a.ne_zero (c := c) hba
  simp only [dilogFactorProduct, List.map_append, List.map_cons, List.prod_append,
    List.prod_cons]
  rw [← mul_assoc (dilogFactor β hβ d a c) (dilogFactor β hβ d b c), hex]
  ac_rfl

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- The two adjacent pairs of the exchanged triple are ordered. -/
theorem ordered_of_antiordered_add (hβ : β.IsAlt) {a b : DilogDegree d}
    (hanti : Antiordered β d a b) :
    Ordered β d b (DilogDegree.add a b) ∧ Ordered β d (DilogDegree.add a b) a := by
  have hba : 0 ≤ β (b : Γ) (a : Γ) := by
    rw [← LinearMap.IsAlt.neg hβ (a : Γ) (b : Γ)]
    exact neg_nonneg.mpr hanti
  constructor
  · simpa only [ordered_iff, DilogDegree.coe_add, map_add,
      LinearMap.IsAlt.self_eq_zero hβ, add_zero] using hba
  · simpa only [ordered_iff, DilogDegree.coe_add, map_add, LinearMap.add_apply,
      LinearMap.IsAlt.self_eq_zero hβ, zero_add] using hba

end Mei.SkewLieAlgebra

namespace Mei.SkewLieAlgebra

variable {R Γ : Type*} [CommRing R] [PartialOrder R] [AddCommGroup Γ]
  {d : PositiveDegrees Γ}

/-- In the zero-form case every pair of degrees is ordered, so a list of dilogarithm factors
needs no exchange. -/
theorem ordered_of_form_eq_zero (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hform : β = 0)
    (a b : DilogDegree d) : Ordered β d a b := by
  rw [ordered_iff, hform]
  simp

end Mei.SkewLieAlgebra
