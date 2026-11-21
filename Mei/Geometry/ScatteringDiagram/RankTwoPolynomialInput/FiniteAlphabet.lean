/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Basic
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Grouping

/-!
# Finite alphabet lifts of rank-two polynomial inputs

Let `I` be a rank-two polynomial input on positive degree data `(L, P, δ)`, with projection
`π : L → M`, incoming lines `{ν_j = c_j}` with primitive tangents `m_j`, and terms
`c_{j,n} z^n`, and let `s` be a finite set of lines, for instance one containing the lines
`linesAtOrder k` with a term of degree at most `k`. The terms `α = (j, n)` of the lines `j ∈ s`
form the finite alphabet `M × ℤ^E` with the letters `v_α = (π n, e_α)`.

* The alphabet is again a rank-two polynomial input
  (`RankTwoPolynomialInput.alphabetPolynomialInput`), with the first projection to `M`, the same
  lines, tangents, coorientations and offsets, and the letters of the terms of the line `j ∈ s`
  as the exponents of the line `j`. The letters project to the projections of the exponents,
  `π(v_α) = π(n)`, so the projected directions are unchanged
  (`RankTwoPolynomialInput.projection_alphabetPolynomialInput_letter`).
* The line presentation (`RankTwoPolynomialInput.lineInput`) places the terms `c_{j,n} z^n` of
  the lines in `s` on the lines `{ν_j = c_j}` of `M`, for the tropical vertex Lie algebra of `L`
  projected to `M` by `π`. If the coefficients lie in the image of a semiring map
  `φ : S →+* R` and the coefficient monoid contains `±p` for a degree `p` with `ν_j(π p) = 1`
  for every line, its ray presentation is a positive wall representative for `π`
  (`RankTwoPolynomialInput.isPositiveWallRepresentative_lineInput_diagram`).
* The alphabet input (`RankTwoPolynomialInput.alphabetInput`) places the letters `v_α` on the
  same lines of `M`, for the first projection; it is `HyperplaneTermInput.finiteAlphabet` with
  `m_α = π n`. For an additive map `τ : M × ℤ^E → L` sending each letter `v_α` to the exponent
  `n`, its finite alphabet lift is the line presentation
  (`RankTwoPolynomialInput.liftFiniteAlphabet_alphabetInput`), so the pushforward along the lift
  sends the scattering class of the alphabet input to that of the line presentation
  (`RankTwoPolynomialInput.pushforward_scat_alphabetInput`). The letters have alphabet degree one,
  so a letter whose exponent has degree at least two contributes in strictly smaller alphabet
  degree (`PositiveDegrees.finiteAlphabet_degree_lt`).

The letters of the alphabet input are the exponents of the alphabet polynomial input
(`RankTwoPolynomialInput.alphabetInput_exponent_mem_exponents`). The line presentation lives in
the tropical vertex Lie algebra with tangent lattice `M`, while the incoming diagram of `I`
(`RankTwoPolynomialInput.incomingDiagram`) lives in the one with tangent lattice `L`, on the
cylinders over the lines; the two are not compared here.

This is the finite alphabet lift of Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, §9.2 and the proof of Theorem 9.9 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput

open _root_.AddMonoidAlgebra PositiveDegrees DirectedWall DirectedDiagram

universe u

variable {L M ι : Type u} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι) (s : Finset ι)

section Line

/-- The line presentation of the terms of the lines in a finite set `s`: the line `{ν_j = c_j}` of
`M` for every `j ∈ ι`, cooriented by `ν_j`, for the tropical vertex Lie algebra of `L` projected to
`M` by `π`, and the term `c_{j,n} z^n` of a line `j ∈ s` on the line `j` with exponent `n`. -/
def lineInput : HyperplaneTermInput d I.projection ι (Σ j : s, I.exponents j) where
  normal j := (I.normal j).toAddMonoidHom
  normal_ne_zero j h0 := (I.isPrimitive_normal j).ne_zero (LinearMap.toAddMonoidHom_injective h0)
  offset := I.offset
  wallIndex α := α.1.val
  exponent α := α.2
  exponent_mem α := I.mem_monoid_of_mem_exponents α.2.property
  exponent_ne_zero α := I.ne_zero_of_mem_exponents α.2.property
  normal_exponent α := by
    simpa [wallNormal_apply] using I.wallNormal_eq_zero_of_mem_exponents α.2.property

/-- The line `j` of the line presentation is cooriented by `ν_j`. -/
@[simp]
theorem lineInput_normal_apply (j : ι) (m : M) : (I.lineInput s).normal j m = I.normal j m := by
  simp [lineInput]

/-- The lines of the line presentation have the offsets of the input. -/
@[simp]
theorem lineInput_offset : (I.lineInput s).offset = I.offset := by
  simp [lineInput]

/-- The term `c_{j,n} z^n` of the line presentation lies on the line `j`. -/
@[simp]
theorem lineInput_wallIndex (α : Σ j : s, I.exponents j) : (I.lineInput s).wallIndex α = α.1 := by
  simp [lineInput]

/-- The term `c_{j,n} z^n` of the line presentation has the exponent `n`. -/
@[simp]
theorem lineInput_exponent (α : Σ j : s, I.exponents j) : (I.lineInput s).exponent α = α.2 := by
  simp [lineInput]

open scoped Mei.TropicalVertexCoefficientAction

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq ι] [DecidableEq L]
  [Module.Free ℤ L] [NormedAddCommGroup V] [NormedSpace ℝ V] {j : M →+ V}
  (g : TauCeti.Toric.IsIntegralLattice j) (c : (Σ j : s, I.exponents j) → R)
  (Q : AddSubmonoid L) [Fact (d.monoid ≤ Q)]

/-- **Positivity of the line presentation.** If the coefficients lie in the image of a semiring
map `φ : S →+* R` and `Q` contains `±p` for a degree `p` with `ν_j(π p) = 1` for every line `j`,
the ray presentation of the line presentation is a positive wall representative for the image of
`S[Q]` and the projection `π`. -/
theorem isPositiveWallRepresentative_lineInput_diagram
    (hQ : ∀ j, ∃ p ∈ Q, -p ∈ Q ∧ I.normal j (I.projection p) = 1)
    {S : Type*} [Semiring S] (φ : S →+* R) (hc : ∀ α, c α ∈ φ.rangeS) :
    ((I.lineInput s).diagram g c).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration (R := R) d Q).completedBCHAction d
        (tropicalVertexGrading (R := R) d I.projection)) (mapRingHom Q φ).rangeS I.projection :=
  (I.lineInput s).isPositiveWallRepresentative_diagram g c I.projection I.tangent
    (fun α => by simpa using I.exists_projection_eq_of_mem_exponents α.2.property) Q
    (by simpa using hQ) φ hc

end Line

/-- The exponents `m_α = π n` of the finite alphabet of the terms `α = (j, n)` of the lines in a
finite set `s`. -/
def alphabetExponent (α : Σ j : s, I.exponents j) : M :=
  I.projection α.2

/-- The exponent of the term `(j, n)` in the finite alphabet is `π n`. -/
@[simp]
theorem alphabetExponent_apply (α : Σ j : s, I.exponents j) :
    I.alphabetExponent s α = I.projection α.2 :=
  (rfl)

variable [DecidableEq ι] [DecidableEq L]

local notation "𝒅" => PositiveDegrees.finiteAlphabet (I.alphabetExponent s)
local notation "v" => PositiveDegrees.letter (I.alphabetExponent s)

section PolynomialInput

/-- The finite alphabet of the terms of the lines in `s` as a rank-two polynomial input: the first
projection `M × ℤ^E → M`, the lines, tangents, coorientations and offsets of `I`, and the letters
`v_α = (π n, e_α)` of the terms `α = (j, n)` of a line `j ∈ s` as the exponents of the line `j`.
The lines outside `s` have no exponents. -/
def alphabetPolynomialInput : RankTwoPolynomialInput 𝒅 M ι where
  projection := AddMonoidHom.fst _ _
  projection_surjective := Prod.fst_surjective
  finrank_eq_two := I.finrank_eq_two
  tangent := I.tangent
  isPrimitive_tangent := I.isPrimitive_tangent
  normal := I.normal
  isPrimitive_normal := I.isPrimitive_normal
  normal_tangent := I.normal_tangent
  offset := I.offset
  exponents j := (Finset.univ.filter fun α : Σ i : s, I.exponents i => α.1.val = j).map
    ⟨v, (linearIndependent_letter _).injective⟩
  mem_monoid_of_mem_exponents hn := by
    obtain ⟨α, -, rfl⟩ := Finset.mem_map.mp hn
    exact letter_mem _ α
  ne_zero_of_mem_exponents hn := by
    obtain ⟨α, -, rfl⟩ := Finset.mem_map.mp hn
    exact letter_ne_zero _ α
  exists_projection_eq_of_mem_exponents hn := by
    obtain ⟨α, hα, rfl⟩ := Finset.mem_map.mp hn
    obtain ⟨k, hk, he⟩ := I.exists_projection_eq_of_mem_exponents α.2.property
    exact ⟨k, hk, by simpa [← (Finset.mem_filter.mp hα).2] using he⟩
  finite_nontrivial _ := s.finite_toSet.subset fun j ⟨_, hn, _⟩ => by
    obtain ⟨α, hα, -⟩ := Finset.mem_map.mp hn
    simp [← (Finset.mem_filter.mp hα).2]

/-- The alphabet polynomial input projects to `M` by the first projection. -/
@[simp]
theorem alphabetPolynomialInput_projection :
    (I.alphabetPolynomialInput s).projection = AddMonoidHom.fst _ _ := by
  simp [alphabetPolynomialInput]

/-- The alphabet polynomial input has the tangents of `I`. -/
@[simp]
theorem alphabetPolynomialInput_tangent : (I.alphabetPolynomialInput s).tangent = I.tangent := by
  simp [alphabetPolynomialInput]

/-- The alphabet polynomial input has the coorientations of `I`. -/
@[simp]
theorem alphabetPolynomialInput_normal : (I.alphabetPolynomialInput s).normal = I.normal := by
  simp [alphabetPolynomialInput]

/-- The alphabet polynomial input has the offsets of `I`. -/
@[simp]
theorem alphabetPolynomialInput_offset : (I.alphabetPolynomialInput s).offset = I.offset := by
  simp [alphabetPolynomialInput]

/-- The exponents of the line `j` of the alphabet polynomial input are the letters of the terms
`α = (j, n)` with `j ∈ s`. -/
@[simp]
theorem mem_alphabetPolynomialInput_exponents {j : ι} {x : M × ((Σ i : s, I.exponents i) → ℤ)} :
    x ∈ (I.alphabetPolynomialInput s).exponents j ↔ ∃ α : Σ i : s, I.exponents i,
      α.1.val = j ∧ v α = x := by
  simp [alphabetPolynomialInput]

/-- **The finite alphabet leaves projected directions unchanged.** The letter `v_α` of the term
`α = (j, n)` projects to the projection `π n` of its exponent. -/
theorem projection_alphabetPolynomialInput_letter (α : Σ j : s, I.exponents j) :
    (I.alphabetPolynomialInput s).projection (v α) = I.projection α.2 := by
  simp

end PolynomialInput

section Alphabet

/-- The alphabet input of the lines in `s`: the lines `{ν_j = c_j}` of the line presentation, for
the first projection `M × ℤ^E → M`, and the term `α = (j, n)` of a line `j ∈ s` on the line `j`
with the letter `v_α = (π n, e_α)` as exponent (`HyperplaneTermInput.finiteAlphabet` with
`m_α = π n`). -/
def alphabetInput : HyperplaneTermInput 𝒅 (AddMonoidHom.fst M _) ι (Σ j : s, I.exponents j) :=
  HyperplaneTermInput.finiteAlphabet (I.lineInput s).normal (I.lineInput s).normal_ne_zero
    I.offset (fun α => α.1.val) (I.alphabetExponent s)
    fun α => by simpa using (I.lineInput s).normal_exponent α

/-- The alphabet input has the lines of the line presentation. -/
@[simp]
theorem alphabetInput_normal : (I.alphabetInput s).normal = (I.lineInput s).normal := by
  simp [alphabetInput]

/-- The lines of the alphabet input have the offsets of the input. -/
@[simp]
theorem alphabetInput_offset : (I.alphabetInput s).offset = I.offset := by
  simp [alphabetInput]

/-- The term `(j, n)` of the alphabet input lies on the line `j`. -/
@[simp]
theorem alphabetInput_wallIndex (α : Σ j : s, I.exponents j) :
    (I.alphabetInput s).wallIndex α = α.1 := by
  simp [alphabetInput]

/-- The term `α` of the alphabet input has the letter `v_α` as exponent. -/
@[simp]
theorem alphabetInput_exponent (α : Σ j : s, I.exponents j) :
    (I.alphabetInput s).exponent α = v α := by
  simp [alphabetInput]

/-- The exponent of a term of the alphabet input on the line `j` is an exponent of the line `j` of
the alphabet polynomial input. -/
theorem alphabetInput_exponent_mem_exponents (α : Σ j : s, I.exponents j) :
    (I.alphabetInput s).exponent α ∈
      (I.alphabetPolynomialInput s).exponents ((I.alphabetInput s).wallIndex α) :=
  (I.mem_alphabetPolynomialInput_exponents s).mpr ⟨α, by simp, by simp⟩

variable {I s} {τ : M × ((Σ j : s, I.exponents j) → ℤ) →+ L}
  (hτ : ∀ α, τ (letter (I.alphabetExponent s) α) = α.2)
include hτ

/-- A lift sending each letter `v_α` of the term `α = (j, n)` to `n` sends it to an allowed
degree. -/
theorem map_letter_mem_monoid (α : Σ j : s, I.exponents j) : τ (v α) ∈ d.monoid := by
  simpa [hτ] using I.mem_monoid_of_mem_exponents α.2.property

/-- A lift sending each letter `v_α` of the term `α = (j, n)` to `n` sends it to a nonzero
degree. -/
theorem map_letter_ne_zero (α : Σ j : s, I.exponents j) : τ (v α) ≠ 0 := by
  simpa [hτ] using I.ne_zero_of_mem_exponents α.2.property

/-- A lift sending each letter `v_α` of the term `α = (j, n)` to `n` is followed by `π` to the
exponent `π n` of the finite alphabet. -/
theorem projection_map_letter (α : Σ j : s, I.exponents j) :
    I.projection (τ (v α)) = I.alphabetExponent s α := by
  simp [hτ]

/-- Lifting the alphabet input along an additive map `τ` sending each letter `v_α` of the term
`α = (j, n)` to `n` gives the line presentation. -/
theorem liftFiniteAlphabet_alphabetInput :
    (I.alphabetInput s).liftFiniteAlphabet (map_letter_mem_monoid hτ) (map_letter_ne_zero hτ)
      (projection_map_letter hτ) = I.lineInput s :=
  HyperplaneTermInput.ext (by ext; simp) (by simp) (funext fun _ => by simp)
    (funext fun _ => by simp [hτ])

variable {R : Type u} {V : Type*} [CommRing R] [Algebra ℚ R] [Module.Free ℤ L] [Module.Free ℤ M]
  [DecidableEq M] [NormedAddCommGroup V] [NormedSpace ℝ V] {j : M →+ V}
  (g : TauCeti.Toric.IsIntegralLattice j) (c : (Σ j : s, I.exponents j) → R)

/-- Let `τ` send each letter `v_α` of the term `α = (j, n)` to `n`. Pushing forward the scattering
class of the alphabet input along the finite alphabet lift `τ` gives the scattering class of the
line presentation, with the same coefficients. -/
theorem pushforward_scat_alphabetInput :
    Class.pushforward (Pushforward.ofFiniteAlphabetLift (R := R) (g := g)
        (map_letter_mem_monoid hτ) (map_letter_ne_zero hτ) (projection_map_letter hτ))
      (((I.alphabetInput s).diagram g c).Scat fun _ => ofHyperplaneRayFactors_full ..) =
      ((I.lineInput s).diagram g c).Scat fun _ => ofHyperplaneRayFactors_full .. := by
  rw [← liftFiniteAlphabet_alphabetInput hτ]
  exact (I.alphabetInput s).pushforward_scat_liftFiniteAlphabet _ _ _ g c

end Alphabet

end Mei.RankTwoPolynomialInput
