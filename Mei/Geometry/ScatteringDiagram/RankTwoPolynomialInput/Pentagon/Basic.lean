/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Binomial

/-!
# Rank-two polynomial inputs of type `A₂`

A rank-two polynomial input `I` is *of type `A₂`* at two lines `j₁, j₂` with exponents `n₁, n₂`
(`RankTwoPolynomialInput.IsTypeA₂`) when it has no other lines, both lines pass through the
origin, their wall functions are the binomials `1 + c₁ z^{n₁}` and `1 + c₂ z^{n₂}`, and the
cylinder normals `νᵢ = ν_{jᵢ} ∘ π` satisfy `ν₁(n₂) = -1` and `ν₂(n₁) = 1`. The
coefficients `c₁, c₂` are arbitrary.

The incoming diagram of such an input is a ray presentation of type `A₂`
(`RankTwoPolynomialInput.IsTypeA₂.isTypeA₂Presentation`,
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Binomial`). Hence adding the
half-hyperplane `{ν₁ + ν₂ = 0, ν₁ ≥ 0}`, the cylinder over the ray `ℝ_{≥0} π(-(n₁ + n₂))`,
cooriented by `ν₁ + ν₂` and labelled by the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}`, gives a
consistent outgoing completion of the input, the pentagon diagram
(`DirectedDiagram.IsTypeA₂Presentation.isOutgoingCompletion_pentagonDiagram`), which represents its
scattering class (`DirectedDiagram.IsTypeA₂Presentation.scat_eq_toClass_pentagonDiagram`). In the
discrete grouping its three nontrivial walls have the wall functions `1 + c₁ z^{n₁}`,
`1 + c₂ z^{n₂}` and `1 + c₁ c₂ z^{n₁ + n₂}` and all other walls have wall function `1`, when the
coefficient monoid `Q` contains `-n₁` and `-n₂`. If `c₁, c₂` lie in the image of a semiring map
`φ : S →+* R`, the pentagon diagram is a positive wall representative of the scattering class
for the image of `S[Q]`
(`RankTwoPolynomialInput.IsTypeA₂.exists_isPositiveWallRepresentative_scat`); for independent
variables over `ℚ` the grouped wall functions have coefficients in `ℕ[c₁, c₂]`.

This is the case of two binomial lines with unimodular pairing of Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, Theorem 9.9 (arXiv:2503.03719v1): the consistent
completion is the scattering diagram of type `A₂` of Gross–Pandharipande–Siebert, *Quivers, curves,
and the tropical vertex*, Example 1.6 (arXiv:0902.0779v3), and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Example 1.15 (arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput

open _root_.AddMonoidAlgebra

variable {L M ι : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι)

/-- A rank-two polynomial input is *of type `A₂`* at the lines `j₁, j₂` with exponents `n₁, n₂`
when every line is `j₁` or `j₂`, the wall functions of `j₁` and `j₂` have the single terms
`c₁ z^{n₁}` and `c₂ z^{n₂}`, both lines pass through the origin, and the cylinder normals satisfy
`ν_{j₁}(π(n₂)) = -1` and `ν_{j₂}(π(n₁)) = 1`. -/
structure IsTypeA₂ (j₁ j₂ : ι) (n₁ n₂ : L) : Prop where
  /-- Every line is one of the two. -/
  eq_or_eq (j : ι) : j = j₁ ∨ j = j₂
  /-- The only exponent of the first line is `n₁`. -/
  exponents_fst : I.exponents j₁ = {n₁}
  /-- The only exponent of the second line is `n₂`. -/
  exponents_snd : I.exponents j₂ = {n₂}
  /-- The first line passes through the origin. -/
  offset_fst : I.offset j₁ = 0
  /-- The second line passes through the origin. -/
  offset_snd : I.offset j₂ = 0
  /-- The first cylinder normal pairs to `-1` with the second exponent. -/
  wallNormal_fst_snd : I.wallNormal j₁ n₂ = -1
  /-- The second cylinder normal pairs to `1` with the first exponent. -/
  wallNormal_snd_fst : I.wallNormal j₂ n₁ = 1

namespace IsTypeA₂

variable {I} {j₁ j₂ : ι} {n₁ n₂ : L} (hA : I.IsTypeA₂ j₁ j₂ n₁ n₂)
include hA

/-- The exponent of the first line is `n₁`. -/
theorem mem_exponents_fst : n₁ ∈ I.exponents j₁ :=
  I.mem_exponents_of_eq_singleton hA.exponents_fst

/-- The exponent of the second line is `n₂`. -/
theorem mem_exponents_snd : n₂ ∈ I.exponents j₂ :=
  I.mem_exponents_of_eq_singleton hA.exponents_snd

/-- The first exponent is an allowed degree. -/
theorem mem_monoid_fst : n₁ ∈ d.monoid := I.mem_monoid_of_mem_exponents hA.mem_exponents_fst

/-- The second exponent is an allowed degree. -/
theorem mem_monoid_snd : n₂ ∈ d.monoid := I.mem_monoid_of_mem_exponents hA.mem_exponents_snd

/-- The first exponent is nonzero. -/
theorem ne_zero_fst : n₁ ≠ 0 := I.ne_zero_of_mem_exponents hA.mem_exponents_fst

/-- The second exponent is nonzero. -/
theorem ne_zero_snd : n₂ ≠ 0 := I.ne_zero_of_mem_exponents hA.mem_exponents_snd

/-- The first exponent is tangent to the first cylinder. -/
theorem wallNormal_fst_fst : I.wallNormal j₁ n₁ = 0 :=
  I.wallNormal_eq_zero_of_mem_exponents hA.mem_exponents_fst

/-- The second exponent is tangent to the second cylinder. -/
theorem wallNormal_snd_snd : I.wallNormal j₂ n₂ = 0 :=
  I.wallNormal_eq_zero_of_mem_exponents hA.mem_exponents_snd

/-- The coefficient variable `c₁` of the term `c₁ z^{n₁}` of the first line. -/
def fstVariable : I.Variable := ⟨j₁, n₁, hA.mem_exponents_fst⟩

/-- The coefficient variable `c₂` of the term `c₂ z^{n₂}` of the second line. -/
def sndVariable : I.Variable := ⟨j₂, n₂, hA.mem_exponents_snd⟩

/-- The first coefficient variable belongs to the first line and the exponent `n₁`. -/
theorem fstVariable_def : hA.fstVariable = ⟨j₁, n₁, hA.mem_exponents_fst⟩ := (rfl)

/-- The second coefficient variable belongs to the second line and the exponent `n₂`. -/
theorem sndVariable_def : hA.sndVariable = ⟨j₂, n₂, hA.mem_exponents_snd⟩ := (rfl)

section Diagram

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) (c : I.Variable → R)

local notation "ρ" => AddMonoidHom.id L

/-- The unsplit label of the first line is the binomial label of `1 + c₁ z^{n₁}`. -/
theorem initialLabel_fst : I.initialLabel c j₁ = binomialLabel d ρ (I.wallNormal j₁)
    hA.mem_monoid_fst hA.ne_zero_fst hA.wallNormal_fst_fst (c hA.fstVariable) :=
  (I.initialLabel_eq_binomialLabel c hA.exponents_fst).trans (by rw [fstVariable_def])

/-- The unsplit label of the second line is the binomial label of `1 + c₂ z^{n₂}`. -/
theorem initialLabel_snd : I.initialLabel c j₂ = binomialLabel d ρ (I.wallNormal j₂)
    hA.mem_monoid_snd hA.ne_zero_snd hA.wallNormal_snd_snd (c hA.sndVariable) :=
  (I.initialLabel_eq_binomialLabel c hA.exponents_snd).trans (by rw [sndVariable_def])

/-- The incoming diagram of an input of type `A₂` is a ray presentation of type `A₂`: the ray
presentation of the binomial labels of `1 + c₁ z^{n₁}` and `1 + c₂ z^{n₂}` on the two cylinders
`{ν₁ = 0}` and `{ν₂ = 0}` through the origin. -/
theorem isTypeA₂Presentation :
    (I.incomingDiagram h c).IsTypeA₂Presentation (I.initialLabel c) j₁ j₂ n₁ n₂
      (c hA.fstVariable) (c hA.sndVariable) where
  isRayFactorPresentation :=
    { (I.isRayFactorPresentation_incomingDiagram h c) with
      support x := by
        rw [I.incomingDiagram_support]
        rcases hA.eq_or_eq x.1 with he | he
        · rw [he, hA.offset_fst]
        · rw [he, hA.offset_snd] }
  commute_isolated x _ hx₁ hx₂ := (hx₁ ((hA.eq_or_eq x.1).resolve_right hx₂)).elim
  mem_monoid_fst := hA.mem_monoid_fst
  mem_monoid_snd := hA.mem_monoid_snd
  apply_fst_fst := hA.wallNormal_fst_fst
  apply_snd_snd := hA.wallNormal_snd_snd
  apply_fst_snd := hA.wallNormal_fst_snd
  apply_snd_fst := hA.wallNormal_snd_fst
  label_fst := hA.initialLabel_fst c
  label_snd := hA.initialLabel_snd c

end Diagram

end IsTypeA₂

end Mei.RankTwoPolynomialInput

/-! ### Positivity, needing the degree lattice in `Type`

The pentagon identity `Mei.binomialLabel_pentagon` is transported through `ℤ × ℤ`, so the
theorem below takes `L : Type`. -/

namespace Mei.RankTwoPolynomialInput.IsTypeA₂

open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

variable {L : Type} {M ι : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  {I : RankTwoPolynomialInput d M ι} {j₁ j₂ : ι} {n₁ n₂ : L} (hA : I.IsTypeA₂ j₁ j₂ n₁ n₂)
  {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap) (c : I.Variable → R)
  (Q : AddSubmonoid L) [Fact (d.monoid ≤ Q)] (hQ₁ : -n₁ ∈ Q) (hQ₂ : -n₂ ∈ Q)
  {S : Type*} [Semiring S] (φ : S →+* R)
  (hc₁ : c hA.fstVariable ∈ φ.rangeS) (hc₂ : c hA.sndVariable ∈ φ.rangeS)

local notation "ρ" => AddMonoidHom.id L
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ
local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

include hA hQ₁ hQ₂ hc₁ hc₂ in
/-- **Positivity of rank-two polynomial inputs of type `A₂`.** For a rank-two polynomial input of
type `A₂` whose coefficients `c₁, c₂` lie in the image of a semiring map `φ : S →+* R`, and a
coefficient monoid `Q` containing `-n₁` and `-n₂`, the outgoing scattering class of the incoming
diagram has a consistent outgoing representative, the pentagon diagram of
`IsTypeA₂.isTypeA₂Presentation`, whose grouped wall functions `1 + c₁ z^{n₁}`, `1 + c₂ z^{n₂}`,
`1 + c₁ c₂ z^{n₁ + n₂}` (and `1` on the remaining ray walls) are positive for the image of
`S[Q]`. -/
theorem exists_isPositiveWallRepresentative_scat [Module.Free ℤ L] :
    ∃ (κ : Type) (E : DirectedDiagram (d := d) h H (I.IncomingIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (I.incomingDiagram h c).wall E ∧
      E.toClass = (I.incomingDiagram h c).Scat (I.incomingDiagram_full h c) ∧
      E.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS
        I.projection :=
  -- The monomials `z^{-n₂}` and `z^{n₁}` are invertible, with `ν₁(-n₂) = ν₂(n₁) = 1` and
  -- `ν₂(-n₂) = 0`.
  (hA.isTypeA₂Presentation h c).exists_isPositiveWallRepresentative_scat Q I.projection φ hc₁ hc₂
    ⟨-n₂, hQ₂, by rw [neg_neg]; exact (Fact.out : d.monoid ≤ Q) hA.mem_monoid_snd,
      by simp [hA.wallNormal_fst_snd], by simp [hA.wallNormal_snd_snd]⟩
    ⟨n₁, (Fact.out : d.monoid ≤ Q) hA.mem_monoid_fst, hQ₁, hA.wallNormal_snd_fst⟩ hA.eq_or_eq

end Mei.RankTwoPolynomialInput.IsTypeA₂
