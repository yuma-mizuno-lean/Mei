/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Pentagon

/-!
# Ordered and antiordered products of normalized dilogarithm factors

In the completed skew group of a positively graded skew Lie algebra, a *normalized
dilogarithm factor* is a ray label `Ψ[n]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jn}/j²)`
at a nonzero allowed degree `n`. Such factors are the normalized positive factors of
the ordinary binomial scattering input.

Ordering is read from the skew form: a pair `a, b` is ordered when `{a,b} ≥ 0` and
antiordered when `{a,b} < 0`. For an antiordered pair whose normalization satisfies
`c {a,b} = -1`, the pentagon identity of `Mei.Geometry.ScatteringDiagram.Skew.Pentagon` rewrites the
product `Ψ[a]^c Ψ[b]^c` as the ordered product `Ψ[b]^c Ψ[b+a]^c Ψ[a]^c`. This is the
adjacent exchange used when ordering a finite product of normalized positive factors.
The file records the exchange for an arbitrary segment of a list, together with the
commutative case in which all pairings vanish; in that case the original product is
already ordered and no exchange is needed.

The rank-two wall-crossing formula of Nakanishi, *Cluster algebras and scattering
diagrams, Part III*, §5.2 (arXiv:2111.00800v6), and Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, §8.1 (arXiv:2503.03719v1),
applies this exchange repeatedly. The statements here are the single-exchange and
commutative base cases; they retain the exact completed label, hence every finite
truncation and the assembly of the truncations.
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries

section Degrees

variable {Γ : Type*} [AddCommGroup Γ] {d : PositiveDegrees Γ}

/-- A nonzero allowed degree of `d`, used to index a normalized dilogarithm factor. -/
abbrev DilogDegree (d : PositiveDegrees Γ) : Type _ := {n : Γ // n ∈ d.monoid ∧ n ≠ 0}

@[simp]
theorem DilogDegree.coe_mk (n : Γ) (hn : n ∈ d.monoid) (hn0 : n ≠ 0) :
    ((⟨n, hn, hn0⟩ : DilogDegree d) : Γ) = n := (rfl)

theorem DilogDegree.mem (n : DilogDegree d) : (n : Γ) ∈ d.monoid := n.property.1

theorem DilogDegree.ne_zero (n : DilogDegree d) : (n : Γ) ≠ 0 := n.property.2

/-- The sum of two dilogarithm degrees, with an explicit nonzero proof. -/
def DilogDegree.add (a b : DilogDegree d) (h : (a : Γ) + (b : Γ) ≠ 0) : DilogDegree d :=
  ⟨(a : Γ) + (b : Γ), d.monoid.add_mem a.mem b.mem, h⟩

@[simp]
theorem DilogDegree.coe_add (a b : DilogDegree d) (h : (a : Γ) + (b : Γ) ≠ 0) :
    ((DilogDegree.add a b h : DilogDegree d) : Γ) = (a : Γ) + (b : Γ) := (rfl)

/-- A pair whose pairing is nonzero has nonzero sum. -/
theorem add_ne_zero_of_form_ne_zero {R : Type*} [CommRing R]
    (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {a b : DilogDegree d}
    (h : β (a : Γ) (b : Γ) ≠ 0) : (a : Γ) + (b : Γ) ≠ 0 := by
  intro hzero
  have hb : (b : Γ) = -(a : Γ) := eq_neg_of_add_eq_zero_right hzero
  apply h
  rw [hb]
  simpa using (neg_eq_zero.mpr (LinearMap.IsAlt.self_eq_zero hβ (a : Γ)))

end Degrees

variable {R Γ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [PartialOrder R] [IsOrderedAddMonoid R]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) (d : PositiveDegrees Γ)

/-- The normalized dilogarithm factor `Ψ[n]^c` at a nonzero allowed degree `n`. -/
def dilogFactor (n : DilogDegree d) (c : R) : d.completedBCHGroup (positiveGrading β hβ d) :=
  rayExp β hβ n.mem n.ne_zero (c • negDilogNeg R)

omit [PartialOrder R] [IsOrderedAddMonoid R] in
/-- The defining ray label of a normalized dilogarithm factor. -/
@[simp]
theorem dilogFactor_def (n : DilogDegree d) (c : R) :
    dilogFactor β hβ d n c = rayExp β hβ n.mem n.ne_zero (c • negDilogNeg R) := (rfl)

/-- The product of the normalized dilogarithm factors of a finite list. -/
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

/-- A pair is ordered when its skew pairing is nonnegative. -/
def Ordered (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (d : PositiveDegrees Γ)
    (a b : DilogDegree d) : Prop := 0 ≤ β (a : Γ) (b : Γ)

/-- A pair is antiordered when its skew pairing is negative. -/
def Antiordered (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (d : PositiveDegrees Γ)
    (a b : DilogDegree d) : Prop := β (a : Γ) (b : Γ) < 0

omit [Algebra ℚ R] [DecidableEq Γ] [IsOrderedAddMonoid R] in
/-- The sum of an antiordered pair is a nonzero allowed degree. -/
def antiorderedAdd (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) (d : PositiveDegrees Γ)
    {a b : DilogDegree d} (h : Antiordered β d a b) : DilogDegree d :=
  DilogDegree.add a b (add_ne_zero_of_form_ne_zero β hβ h.ne)

omit [Algebra ℚ R] [DecidableEq Γ] [IsOrderedAddMonoid R] in
@[simp]
theorem coe_antiorderedAdd {a b : DilogDegree d} (h : Antiordered β d a b) :
    ((antiorderedAdd β hβ d h : DilogDegree d) : Γ) = (a : Γ) + (b : Γ) := (rfl)

omit [IsOrderedAddMonoid R] in
/-- **Adjacent exchange.** If `a, b` is antiordered and the common normalization
satisfies `c {a,b} = -1`, then `Ψ[a]^c Ψ[b]^c = Ψ[b]^c Ψ[b+a]^c Ψ[a]^c`. -/
theorem dilogFactor_mul_dilogFactor_eq_of_antiordered {a b : DilogDegree d}
    (hanti : Antiordered β d a b) {c : R} (hc : c * β (a : Γ) (b : Γ) = -1) :
    dilogFactor β hβ d a c * dilogFactor β hβ d b c =
      dilogFactor β hβ d b c * dilogFactor β hβ d (antiorderedAdd β hβ d hanti) c *
        dilogFactor β hβ d a c := by
  have hba : c * β (b : Γ) (a : Γ) = 1 := by
    rw [← hβ.neg (a : Γ) (b : Γ), mul_neg, hc, neg_neg]
  have hp := rayExp_smul_negDilogNeg_pentagon β hβ d b.mem a.mem b.ne_zero a.ne_zero
    (c := c) hba
  simpa only [dilogFactor, DilogDegree.coe_add, antiorderedAdd, add_comm] using hp

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- The two adjacent pairs of the exchanged triple are ordered. -/
theorem ordered_of_antiordered_add {a b : DilogDegree d} (hanti : Antiordered β d a b) :
    Ordered β d b (antiorderedAdd β hβ d hanti) ∧
      Ordered β d (antiorderedAdd β hβ d hanti) a := by
  have hba : 0 < β (b : Γ) (a : Γ) := by
    rw [← LinearMap.IsAlt.neg hβ (a : Γ) (b : Γ)]
    exact neg_pos.mpr hanti
  constructor
  · rw [Ordered, coe_antiorderedAdd β hβ d hanti]
    simpa [map_add, LinearMap.IsAlt.self_eq_zero hβ] using hba.le
  · rw [Ordered, coe_antiorderedAdd β hβ d hanti]
    simpa [map_add, LinearMap.IsAlt.self_eq_zero hβ] using hba.le

omit [IsOrderedAddMonoid R] in
/-- Replacing an antiordered adjacent pair by its ordered exchange preserves the
product of the whole finite list. -/
theorem dilogFactorProduct_append_cons_cons_eq_of_antiordered (l₁ l₂ : List (DilogDegree d))
    {a b : DilogDegree d} (hanti : Antiordered β d a b) {c : R}
    (hc : c * β (a : Γ) (b : Γ) = -1) :
    dilogFactorProduct β hβ d (l₁ ++ a :: b :: l₂) c =
      dilogFactorProduct β hβ d
        (l₁ ++ b :: antiorderedAdd β hβ d hanti :: a :: l₂) c := by
  simp only [dilogFactorProduct, List.map_append, List.map_cons, List.prod_append,
    List.prod_cons]
  rw [← mul_assoc (dilogFactor β hβ d a c) (dilogFactor β hβ d b c)]
  rw [dilogFactor_mul_dilogFactor_eq_of_antiordered β hβ d hanti hc]
  ac_rfl

omit [PartialOrder R] [IsOrderedAddMonoid R] in
/-- Factors whose skew pairing vanishes commute. -/
theorem dilogFactor_commute_of_form_eq_zero {a b : DilogDegree d}
    (h : β (a : Γ) (b : Γ) = 0) (c : R) :
    Commute (dilogFactor β hβ d a c) (dilogFactor β hβ d b c) :=
  commute_rayExp_of_eq_zero β hβ a.mem a.ne_zero b.mem b.ne_zero h _ _

end Mei.SkewLieAlgebra

namespace Mei.SkewLieAlgebra

variable {R Γ : Type*} [CommRing R] [PartialOrder R] [AddCommGroup Γ]
  {d : PositiveDegrees Γ}

/-- In the zero-form case every pair is ordered, so every list of normalized factors
is already an ordered factorization. -/
theorem ordered_of_form_eq_zero (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hform : β = 0)
    (a b : DilogDegree d) : Ordered β d a b := by
  rw [Ordered, hform]
  simp

end Mei.SkewLieAlgebra

