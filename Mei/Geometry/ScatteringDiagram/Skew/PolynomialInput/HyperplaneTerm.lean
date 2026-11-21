/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Grouping

/-!
# BLM polynomial inputs as polynomial function walls on hyperplanes

Let `I` be a BLM polynomial input with unfrozen indices `I_uf`, exponents `w_i ∈ M = Hom(N, ℤ)`
and variables `p_{i,s}`, `1 ≤ s ≤ ℓ_i`, indexed by the set `E` of letters of the finite alphabet
lattice `M × ℤ^E`. Its initial wall functions `f_i = 1 + ∑_s p_{i,s} z^{s w_i}` are polynomial
function walls on hyperplanes (`HyperplaneTermInput`) in two ways. In both, the term `(i, s)` lies
on the hyperplane `i`, has coefficient `1` and has the letter `v_{i,s} = (s w_i, e_{(i,s)})` as
exponent, so that `z^{v_{i,s}}` stands for `p_{i,s} z^{s w_i}`.

* On the cylinders over the `e_i⊥` in the alphabet lattice, with `ρ = id`, the normals
  `(m, b) ↦ m(e_i)` and offsets `0` (`BLMPolynomialInput.toHyperplaneTermInput`). Its wall
  function on the hyperplane `i` is the tangent initial function
  (`BLMPolynomialInput.tangentInitialFunction_eq_toHyperplaneTermInput`), so the hyperplane `i`
  carries the initial label `exp(log(f_i) ∂_{e_i})`
  (`BLMPolynomialInput.label_toHyperplaneTermInput`), and its ray presentation is the incoming
  diagram of `I` (`BLMPolynomialInput.incomingDiagram_eq_diagram`). Hence the incoming diagram
  is a positive wall representative as soon as the coefficient monoid contains `±p` for a degree
  `p = (m, b)` with `m(e_i) = 1`, for each `i ∈ I_uf`
  (`BLMPolynomialInput.isPositiveWallRepresentative_incomingDiagram_of_exists`).
* On the hyperplanes `e_i⊥` of `M` itself, with `ρ` the first projection: the alphabet input
  `HyperplaneTermInput.finiteAlphabet` of the terms `p_{i,s} z^{s w_i}`, with `m_{i,s} = s w_i`
  and `c_{i,s} = 1` (`BLMPolynomialInput.alphabetInput`). Its normals pull back along the first
  projection to the normals of the cylinder input
  (`BLMPolynomialInput.comp_fst_alphabetInput_normal`). For positive degree data `(L, P, δ)`,
  a projection `π : L → M` and an additive map `τ` with `τ v_{i,s} ∈ P ∖ {0}` and
  `π (τ v_{i,s}) = s w_i`, the lifted input `HyperplaneTermInput.liftFiniteAlphabet` has the
  walls `1 + ∑_s z^{τ v_{i,s}}`. Its ray presentation is a positive wall representative for
  `π` when the coefficient monoid contains `±p` for a degree `p` with `(π p)(e_i) = 1`, for each
  `i ∈ I_uf` (`BLMPolynomialInput.isPositiveWallRepresentative_liftFiniteAlphabet_alphabetInput`).
  The pushforward of scattering classes along the lift is
  `HyperplaneTermInput.pushforward_scat_liftFiniteAlphabet`, applied to `I.alphabetInput`.

The two inputs live on different tangent lattices, `M × ℤ^E` and `M`, hence on different tropical
vertex Lie algebras; their diagrams are not compared here. No finite-index lattice change is
attached to a general BLM polynomial input, so the finite-index results of
`Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.FiniteIndex` are not specialized.

This is the finite-alphabet lift for BLM polynomial inputs in Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, §8.1 and §9.2 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra HyperplaneTermInput DirectedDiagram

section Cylinder

variable {N ι R V : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput) [DecidableEq ι]

local notation "Γ" => Module.Dual ℤ N × (I.Letter → ℤ)
local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent

-- An `abbrev`, so that the walls of its ray presentation are indexed by `IncomingIndex`.
/-- The initial walls of a polynomial input as polynomial function walls on the cylinders over
the `e_i⊥` in the alphabet lattice `M × ℤ^E`, with `ρ = id`: the hyperplane `i ∈ I_uf` has the
normal `(m, b) ↦ m(e_i)` and offset `0`, and the variable `p_{i,s}` is a term on it with the
letter `v_{i,s} = (s w_i, e_{(i,s)})` as exponent. -/
abbrev toHyperplaneTermInput :
    HyperplaneTermInput 𝒅 (AddMonoidHom.id Γ) B.unfrozenIndex I.Letter where
  normal := I.alphabetNormal
  normal_ne_zero := I.alphabetNormal_ne_zero
  offset _ := 0
  wallIndex := Sigma.fst
  exponent := PositiveDegrees.letter I.letterExponent
  exponent_mem := PositiveDegrees.letter_mem I.letterExponent
  exponent_ne_zero := PositiveDegrees.letter_ne_zero I.letterExponent
  normal_exponent α := I.alphabetNormal_letter_self α.1 α.2

/-- The hyperplanes of the cylinder input have the cylinder normals `(m, b) ↦ m(e_i)`. -/
@[simp]
theorem toHyperplaneTermInput_normal : I.toHyperplaneTermInput.normal = I.alphabetNormal :=
  (rfl)

/-- The hyperplanes of the cylinder input pass through the origin. -/
@[simp]
theorem toHyperplaneTermInput_offset : I.toHyperplaneTermInput.offset = fun _ => 0 :=
  (rfl)

/-- The variable `p_{i,s}` lies on the hyperplane `i`. -/
@[simp]
theorem toHyperplaneTermInput_wallIndex : I.toHyperplaneTermInput.wallIndex = Sigma.fst :=
  (rfl)

/-- The variable `p_{i,s}` has the letter `v_{i,s}` as exponent. -/
@[simp]
theorem toHyperplaneTermInput_exponent :
    I.toHyperplaneTermInput.exponent = PositiveDegrees.letter I.letterExponent :=
  (rfl)

variable [CommRing R]

/-- With unit coefficients, the wall function of the hyperplane `i` of the cylinder input is the
tangent initial function `1 + ∑_s z^{v_{i,s}}`. -/
theorem tangentInitialFunction_eq_toHyperplaneTermInput (i : B.unfrozenIndex) :
    I.tangentInitialFunction (R := R) i = 1 + ∑ α : I.toHyperplaneTermInput.Term i,
      single (I.toHyperplaneTermInput.tangentExponent (R := R) i α) (1 : R) := by
  refine mapDomain_injective Subtype.val_injective ?_
  have he : mapDomainRingHom R (AddSubmonoid.subtype _) (1 + ∑ α : I.toHyperplaneTermInput.Term i,
      single (I.toHyperplaneTermInput.tangentExponent (R := R) i α) (1 : R)) =
        I.initialFunction R i := by
    simp only [map_add, map_one, map_sum, mapDomainRingHom_apply, mapDomain_single,
      AddSubmonoid.subtype_apply, coe_tangentExponent, initialFunction_def]
    congr 1
    exact Fintype.sum_equiv (Equiv.sigmaSubtype i) _ _ fun α => by
      obtain ⟨⟨j, s⟩, rfl⟩ := α
      simp
  rw [mapDomain_tangentInitialFunction, ← he]
  simp only [mapDomainRingHom_apply, AddSubmonoid.coe_subtype]

variable [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R]

/-- With unit coefficients, the label of the hyperplane `i` of the cylinder input is the initial
label `exp(log(f_i) ∂_{e_i})`. -/
@[simp]
theorem label_toHyperplaneTermInput (i : B.unfrozenIndex) :
    I.toHyperplaneTermInput.label (fun _ => (1 : R)) i = I.initialLabel i := by
  simp only [label_def, initialLabel_def, I.tangentInitialFunction_eq_toHyperplaneTermInput]

variable [Module.Finite ℤ N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : Module.Dual ℤ N × (I.Letter → ℤ) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The incoming diagram of a polynomial input is the ray presentation of the cylinder input with
unit coefficients. -/
theorem incomingDiagram_eq_diagram [Module.Free ℤ N] :
    I.incomingDiagram (R := R) h = I.toHyperplaneTermInput.diagram h fun _ => (1 : R) := by
  ext x : 2
  apply DirectedWall.ext <;> simp [Set.ext_iff]

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid (Module.Dual ℤ N × (I.Letter → ℤ)))
  [Fact ((PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)]

/-- The incoming diagram of a polynomial input is a positive wall representative for the image
of `S[Q]` under any semiring map `φ : S →+* R` and the first projection, when `Q` contains `±p`
for a degree `p = (m, b)` with `m(e_i) = 1` at every unfrozen index `i`. -/
theorem isPositiveWallRepresentative_incomingDiagram_of_exists
    (hQ : ∀ i : B.unfrozenIndex, ∃ p ∈ Q, -p ∈ Q ∧ p.1 (B.basis i) = 1)
    {S : Type*} [Semiring S] (φ : S →+* R) :
    (I.incomingDiagram (R := R) h).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration (R := R) 𝒅 Q).completedBCHAction 𝒅
        (tropicalVertexGrading (R := R) 𝒅 (AddMonoidHom.id Γ)))
      (mapRingHom Q φ).rangeS (AddMonoidHom.fst _ _) := by
  let := Module.Free.of_basis B.basis
  rw [I.incomingDiagram_eq_diagram h]
  exact I.toHyperplaneTermInput.isPositiveWallRepresentative_diagram h _ (AddMonoidHom.fst _ _)
    I.exponent (fun α => by simpa using I.exists_letterExponent_eq_nsmul α) Q
    (by simpa using hQ) φ fun _ => ⟨1, map_one φ⟩

end Cylinder

section Alphabet

universe u

variable {N ι : Type u} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput) [DecidableEq ι]

local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent

/-- The alphabet input of a polynomial input: the hyperplanes `e_i⊥` of `M = Hom(N, ℤ)`, for
`i ∈ I_uf`, cooriented by the evaluation `m ↦ m(e_i)`, with the term `p_{i,s} z^{s w_i}` on the
hyperplane `i` and the letter `v_{i,s} = (s w_i, e_{(i,s)})` as exponent
(`HyperplaneTermInput.finiteAlphabet` with `m_{i,s} = s w_i`). -/
def alphabetInput :
    HyperplaneTermInput 𝒅 (AddMonoidHom.fst (Module.Dual ℤ N) (I.Letter → ℤ)) B.unfrozenIndex
      I.Letter :=
  finiteAlphabet (fun i : B.unfrozenIndex => (Module.Dual.eval ℤ N (B.basis i)).toAddMonoidHom)
    (fun i hi => by simpa using DFunLike.congr_fun hi (B.basis.coord i)) (fun _ => 0)
    (Sigma.fst : I.Letter → B.unfrozenIndex) I.letterExponent
    fun α : I.Letter => by simpa using I.letterExponent_apply_basis_self α.1 α.2

/-- The normal of the hyperplane `i` of the alphabet input is the evaluation at `e_i`. -/
@[simp]
theorem alphabetInput_normal_apply (i : B.unfrozenIndex) (m : Module.Dual ℤ N) :
    I.alphabetInput.normal i m = m (B.basis i) := by
  simp [alphabetInput]

/-- The hyperplanes of the alphabet input pass through the origin. -/
@[simp]
theorem alphabetInput_offset : I.alphabetInput.offset = fun _ => 0 := by
  simp [alphabetInput]

/-- The term `p_{i,s} z^{s w_i}` of the alphabet input lies on the hyperplane `i`. -/
@[simp]
theorem alphabetInput_wallIndex : I.alphabetInput.wallIndex = Sigma.fst := by
  simp [alphabetInput]

/-- The term `p_{i,s} z^{s w_i}` of the alphabet input has the letter `v_{i,s}` as exponent. -/
@[simp]
theorem alphabetInput_exponent :
    I.alphabetInput.exponent = PositiveDegrees.letter I.letterExponent := by
  simp [alphabetInput]

/-- The normals of the alphabet input pull back along the first projection
`M × ℤ^E → M` to the cylinder normals. -/
@[simp]
theorem comp_fst_alphabetInput_normal (i : B.unfrozenIndex) :
    (I.alphabetInput.normal i).comp (AddMonoidHom.fst _ _) = I.alphabetNormal i := by
  ext x
  simp

open scoped Mei.TropicalVertexCoefficientAction

variable {R L : Type u} {V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup L]
  [Module.Free ℤ L] [DecidableEq L] {f : PositiveDegrees L}
  {τ : Module.Dual ℤ N × (I.Letter → ℤ) →+ L}
  (hτ : ∀ α, τ (PositiveDegrees.letter I.letterExponent α) ∈ f.monoid)
  (hτ0 : ∀ α, τ (PositiveDegrees.letter I.letterExponent α) ≠ 0)
  {π : L →+ Module.Dual ℤ N} (hπ : ∀ α, π (τ (PositiveDegrees.letter I.letterExponent α)) =
    I.letterExponent α)
  [NormedAddCommGroup V] [NormedSpace ℝ V] {j : Module.Dual ℤ N →+ V}
  (g : TauCeti.Toric.IsIntegralLattice j)
  (Q : AddSubmonoid L) [Fact (f.monoid ≤ Q)]

/-- **Positivity of the lifted BLM walls.** Let `τ` send each letter `v_{i,s}` to a nonzero
allowed degree `n_{i,s}` of `(L, P, δ)` with `π n_{i,s} = s w_i`. If `Q` contains `±p` for a
degree `p` with `(π p)(e_i) = 1` at every unfrozen index `i`, then the ray presentation of the
lifted walls `1 + ∑_s z^{n_{i,s}}` is a positive wall representative for the image of `S[Q]`
under any semiring map `φ : S →+* R` and the projection `π`. -/
theorem isPositiveWallRepresentative_liftFiniteAlphabet_alphabetInput
    (hQ : ∀ i : B.unfrozenIndex, ∃ p ∈ Q, -p ∈ Q ∧ π p (B.basis i) = 1)
    {S : Type*} [Semiring S] (φ : S →+* R) :
    ((I.alphabetInput.liftFiniteAlphabet hτ hτ0 hπ).diagram g fun _ => (1 : R)
      ).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration (R := R) f Q).completedBCHAction f
        (tropicalVertexGrading (R := R) f π)) (mapRingHom Q φ).rangeS π :=
  I.alphabetInput.isPositiveWallRepresentative_liftFiniteAlphabet_diagram hτ hτ0 hπ g _
    I.exponent (fun α => by simpa using I.exists_letterExponent_eq_nsmul α) Q
    (by simpa using hQ) φ fun _ => ⟨1, map_one φ⟩

end Alphabet

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
