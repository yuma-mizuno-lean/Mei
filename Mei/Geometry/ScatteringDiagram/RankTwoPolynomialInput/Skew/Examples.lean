/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Skew.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.Examples

/-!
# The unimodular rank-two datum as a rank-two polynomial input of type `A₂`

Take the unimodular rank-two skew lattice datum on `N = ℤ × ℤ` with `{e₁, e₂} = 1`, `N° = N`,
both indices unfrozen and multipliers `(1, 1)`. Both principal characters `p₁*(eᵢ)` are nonzero
(`principalCharacter_unimodularRankTwo_ne_zero`), so for `ℓ = (1, 1)` the adapted polynomial input
with wall functions `1 + a₀ T` and `1 + a₁ T` is the rank-two polynomial input
`unimodularRankTwoInput` on the principal lattice `M° × N`, with projection `pr₁`, exponents
`r(e₁)` and `r(e₂)` and coefficients `a₀, a₁` (`rankTwoCoefficient_unimodularRankTwo_fst` and
`rankTwoCoefficient_unimodularRankTwo_snd`). Since `{e₁, e₂} = 1` it is of type `A₂`
(`isTypeA₂_unimodularRankTwoInput`). Hence the principal realization sends the outgoing scattering
class of the adapted input to the class of the pentagon diagram of
`Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Pentagon.Basic`
(`map_scat_unimodularRankTwo_eq_toClass_pentagonDiagram`). For the independent variables
`a₀, a₁` over `ℚ` and the full coefficient lattice, this class has a positive wall representative
whose grouped wall functions have coefficients in `ℕ[a₀, a₁]`
(`exists_isPositiveWallRepresentative_map_scat_unimodularRankTwo`). This is the scattering diagram
of type `A₂` of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Example 1.15 (arXiv:1411.1394v2), reached through Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams*, Theorem 9.9 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.Examples

open AdaptedBasis
open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

local notation "B" => unimodularRankTwoAdaptedBasis
local notation "𝒅" => unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ unimodularRankTwo.sublattice × unimodularRankTwo.unfrozen
local notation "e" => unimodularRankTwo.principalPositiveDegrees 𝒅

/-- Both principal characters `p₁*(e₁) = {e₁, -}` and `p₁*(e₂) = {e₂, -}` of the unimodular
rank-two datum are nonzero. -/
theorem principalCharacter_unimodularRankTwo_ne_zero (i : (B).unfrozenIndex) :
    unimodularRankTwo.principalCharacter ((B).unfrozenBasis i) ≠ 0 := by
  obtain ⟨i, hi⟩ := i
  intro h0
  -- Evaluate `p₁*(eᵢ) = {eᵢ, -}` at the other basis vector, where it is `±1`.
  have he (m : unimodularRankTwo.sublattice) :=
    congrArg (Int.cast : ℤ → ℚ) (DFunLike.congr_fun h0 m)
  fin_cases i
  · simpa using he ⟨(0, 1), by simp⟩
  · simpa using he ⟨(1, 0), by simp⟩

/-- The unimodular rank-two datum has rank two. -/
theorem nat_card_unimodularRankTwo : Nat.card (Fin 2) = 2 := by simp

/-- The adapted polynomial input of the unimodular rank-two datum with `ℓ = (1, 1)`, as a
rank-two polynomial input on the principal lattice `M° × N`. -/
abbrev unimodularRankTwoInput :
    RankTwoPolynomialInput e (Module.Dual ℤ unimodularRankTwo.sublattice) (B).unfrozenIndex :=
  (B).toRankTwoPolynomialInput (fun _ => 1) nat_card_unimodularRankTwo
    principalCharacter_unimodularRankTwo_ne_zero

/-- Every unfrozen index of the unimodular rank-two datum is one of the two. -/
theorem eq_unimodularRankTwoFst_or_eq_unimodularRankTwoSnd (i : (B).unfrozenIndex) :
    i = unimodularRankTwoFst ∨ i = unimodularRankTwoSnd := by
  obtain ⟨i, hi⟩ := i
  fin_cases i <;> simp

/-- The rank-two input of the unimodular datum is of type `A₂` at its two indices, with exponents
`r(e₁)` and `r(e₂)`. -/
theorem isTypeA₂_unimodularRankTwoInput :
    unimodularRankTwoInput.IsTypeA₂ unimodularRankTwoFst unimodularRankTwoSnd
      (unimodularRankTwo.principalEmbedding ((B).unfrozenBasis unimodularRankTwoFst))
      (unimodularRankTwo.principalEmbedding ((B).unfrozenBasis unimodularRankTwoSnd)) :=
  (B).isTypeA₂_toRankTwoPolynomialInput _ _ _ eq_unimodularRankTwoFst_or_eq_unimodularRankTwoSnd
    rfl rfl (by simp) (by simp)

variable {R : Type*} [CommRing R] (a : ∀ _ : (B).unfrozenIndex, Fin 1 → R)

/-- The coefficient of `z^{r(e₁)}` is `a₀`. -/
theorem rankTwoCoefficient_unimodularRankTwo_fst :
    (B).rankTwoCoefficient (fun _ => 1) nat_card_unimodularRankTwo
        principalCharacter_unimodularRankTwo_ne_zero a isTypeA₂_unimodularRankTwoInput.fstVariable =
      a unimodularRankTwoFst 0 := by
  rw [RankTwoPolynomialInput.IsTypeA₂.fstVariable_def]
  exact (B).rankTwoCoefficient_eq _ _ _ a 0 _ (by simp)

/-- The coefficient of `z^{r(e₂)}` is `a₁`. -/
theorem rankTwoCoefficient_unimodularRankTwo_snd :
    (B).rankTwoCoefficient (fun _ => 1) nat_card_unimodularRankTwo
        principalCharacter_unimodularRankTwo_ne_zero a isTypeA₂_unimodularRankTwoInput.sndVariable =
      a unimodularRankTwoSnd 0 := by
  rw [RankTwoPolynomialInput.IsTypeA₂.sndVariable_def]
  exact (B).rankTwoCoefficient_eq _ _ _ a 0 _ (by simp)

/-- The principal lattice `M° × N` of the unimodular rank-two datum is free. -/
instance moduleFree_principalLattice_unimodularRankTwo : Module.Free ℤ Lpr := by
  have := Module.Free.of_basis (B).sublatticeBasis
  have := Module.Finite.of_basis (B).sublatticeBasis
  have := Module.Free.of_basis (B).unfrozenBasis
  infer_instance

/-- The full coefficient lattice contains the principal positive monoid. -/
instance fact_principalPositiveDegrees_le_top_unimodularRankTwo :
    Fact ((e).monoid ≤ (⊤ : AddSubmonoid Lpr)) :=
  ⟨le_top⟩

variable [Algebra ℚ R] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : Lpr →+ V} (h : TauCeti.Toric.IsIntegralLattice latticeMap)

open scoped Classical in
/-- **The pentagon from the unimodular rank-two datum.** The principal realization sends the
outgoing scattering class of the adapted polynomial input `(e₁⊥, 1 + a₀ q^{e₁})`,
`(e₂⊥, 1 + a₁ q^{e₂})` to the class of the pentagon diagram of its rank-two input, whose single
outgoing wall carries the binomial label of `1 + a₀ a₁ z^{r(e₁) + r(e₂)}`. -/
theorem map_scat_unimodularRankTwo_eq_toClass_pentagonDiagram :
    DirectedDiagram.Class.map (unimodularRankTwo.principalGraphGradedLieHom 𝒅)
        (fun _ _ _ => unimodularRankTwo.principalGraphGradedLieHom_mem_wall 𝒅)
        (((B).adaptedPolynomialInput (fun _ => 1) a h).Scat
          ((B).adaptedPolynomialInput_full _ a h)) =
      (isTypeA₂_unimodularRankTwoInput.isTypeA₂Presentation h
        ((B).rankTwoCoefficient _ _ _ a)).pentagonDiagram.toClass :=
  ((B).map_scat_adaptedPolynomialInput _ nat_card_unimodularRankTwo
    principalCharacter_unimodularRankTwo_ne_zero a h).trans
    (DirectedDiagram.IsTypeA₂Presentation.scat_eq_toClass_pentagonDiagram _)

local notation "𝕜" => MvPolynomial unimodularRankTwoAdaptedBasis.unfrozenIndex ℚ

open scoped Classical in
/-- **Positivity for the unimodular rank-two datum.** For the independent variables `a₀, a₁` over
`ℚ`, the image under the principal realization of the outgoing scattering class of the adapted
polynomial input `(e₁⊥, 1 + a₀ q^{e₁})`, `(e₂⊥, 1 + a₁ q^{e₂})` has a representative whose
grouped wall functions have monomial coefficients in `ℕ[a₀, a₁]`, for the full coefficient
lattice `M° × N`. -/
theorem exists_isPositiveWallRepresentative_map_scat_unimodularRankTwo :
    ∃ (κ : Type) (E : DirectedDiagram (d := e) h
        (tropicalVertexWallSpaces (R := 𝕜) e (AddMonoidHom.id Lpr))
        (unimodularRankTwoInput.IncomingIndex ⊕ κ)),
      E.toClass = DirectedDiagram.Class.map (unimodularRankTwo.principalGraphGradedLieHom 𝒅)
        (fun _ _ _ => unimodularRankTwo.principalGraphGradedLieHom_mem_wall 𝒅)
        (((B).adaptedPolynomialInput (fun _ => 1) (fun i _ => MvPolynomial.X i) h).Scat
          ((B).adaptedPolynomialInput_full _ _ h)) ∧
      E.IsPositiveWallRepresentative
        ((TropicalVertexCoefficientAction.filtration (R := 𝕜) e
          (⊤ : AddSubmonoid Lpr)).completedBCHAction e
          (tropicalVertexGrading (R := 𝕜) e (AddMonoidHom.id Lpr)))
        (mapRingHom (⊤ : AddSubmonoid Lpr) (MvPolynomial.map (Nat.castRingHom ℚ))).rangeS
        unimodularRankTwoInput.projection := by
  obtain ⟨κ, E, -, hE, hpos⟩ :=
    isTypeA₂_unimodularRankTwoInput.exists_isPositiveWallRepresentative_scat h
      ((B).rankTwoCoefficient _ _ _ fun i _ => MvPolynomial.X i) ⊤ (AddSubmonoid.mem_top _)
      (AddSubmonoid.mem_top _) (MvPolynomial.map (Nat.castRingHom ℚ))
      ⟨MvPolynomial.X unimodularRankTwoFst, by
        rw [rankTwoCoefficient_unimodularRankTwo_fst, MvPolynomial.map_X]⟩
      ⟨MvPolynomial.X unimodularRankTwoSnd, by
        rw [rankTwoCoefficient_unimodularRankTwo_snd, MvPolynomial.map_X]⟩
  exact ⟨κ, E, hE.trans ((B).map_scat_adaptedPolynomialInput _ nat_card_unimodularRankTwo
    principalCharacter_unimodularRankTwo_ne_zero _ h).symm, hpos⟩

end Mei.SkewLatticeDatum.Examples
