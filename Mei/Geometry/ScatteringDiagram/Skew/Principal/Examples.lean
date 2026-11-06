/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Pentagon
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Positive adapted polynomial walls: forms vanishing on the unfrozen part, and type `A₂`
with isolated indices

Take `N = ℤ³` with the skew form `{x, y} = x₀ y₂ - x₂ y₀`, the unfrozen basis vectors `e₀, e₁`,
the frozen basis vector `e₂` and multipliers one. The form is nonzero, since `{e₀, e₂} = 1`, but
it vanishes on `N_uf = ℤ e₀ ⊕ ℤ e₁` (`frozenDatum_form_ne_zero`,
`frozenDatum_form_unfrozen_eq_zero`). With multiplicities `ℓ = (2, 2)` and independent
coefficients `aᵢₛ` the adapted polynomial input has the initial wall functions
`1 + aᵢ₀ q^{eᵢ} + aᵢ₁ (q^{eᵢ})^2` on the principal coefficient algebra.

* `exists_isPositiveWallRepresentative_frozenDatum`: for every integral lattice structure on
  `L_pr,ℝ`, the outgoing scattering class of this input has a representative whose grouped
  wall functions have monomial coefficients in `ℕ[aᵢₛ]`.
* `coe_completedPolynomialWallFunction_frozenDatum`: the grouped wall function at `eᵢ` is
  `1 + aᵢ₀ z^{r(eᵢ)} + aᵢ₁ z^{2 r(eᵢ)}`.
* `exists_isPositiveWallRepresentative_frozenDatum_binomial`,
  `coe_completedPolynomialWallFunction_frozenDatum_binomial`: the binomial input over `ℚ` with
  walls `(eᵢ⊥, 1 + q^{eᵢ})` has a representative of its scattering class whose grouped wall
  functions `1 + q^{eᵢ}` have natural-number coefficients.

For the unimodular rank-two datum `{e₁, e₂} = 1`, `N° = N`, with its standard adapted basis
(`isTypeA₂WithIsolated_unimodularRankTwoAdaptedBasis`), the form does not vanish on `N_uf`:

* `exists_isPositiveWallRepresentative_unimodularRankTwo`: over any commutative `ℚ`-algebra,
  the outgoing scattering class of the binomial input `(eᵢ⊥, 1 + q^{eᵢ})` is represented by the
  diagram of type `A₂` with the additional wall `{ν_{e₁} + ν_{e₂} = 0, ν_{e₁} ≥ 0}`, an outgoing
  completion whose grouped wall functions `1 + q^{e₁}`, `1 + q^{e₂}`, `1 + q^{e₁ + e₂}` have
  natural-number coefficients.
* `exists_isPositiveWallRepresentative_unimodularRankTwo_coefficient`: for independent variables
  `a₀, a₁ ∈ ℚ[a₀, a₁]`, the outgoing scattering class of the adapted polynomial input
  `(e₁⊥, 1 + a₀ q^{e₁})`, `(e₂⊥, 1 + a₁ q^{e₂})` is represented by the same configuration, with
  grouped wall functions `1 + a₀ q^{e₁}`, `1 + a₁ q^{e₂}` and `1 + a₀ a₁ q^{e₁ + e₂}`
  (`coe_pentagonWallFunction_unimodularRankTwo_inr`) whose monomial coefficients lie in
  `ℕ[a₀, a₁]`.

Take `N = ℤ³` with the skew form `{x, y} = x₀ y₁ - x₁ y₀`, every basis vector unfrozen and
multipliers one (`isolatedDatum`). The form is degenerate on `N_uf = N`, with `e₂` in its radical,
but does not vanish (`isolatedDatum_form_single_two`,
`isolatedDatum_form_single_zero_single_one`); its standard basis is of type `A₂` at `0, 1` with
the isolated index `2` (`isTypeA₂WithIsolated_isolatedBasis`).

* `exists_isPositiveWallRepresentative_isolated`: for independent variables `a₀, a₁, a₂`, the
  outgoing scattering class of the adapted polynomial input `(eᵢ⊥, 1 + aᵢ q^{eᵢ})` is represented
  by the input walls and the one additional wall `{ν_{e₀} + ν_{e₁} = 0, ν_{e₀} ≥ 0}`, with grouped
  wall functions `1 + aᵢ q^{eᵢ}` and `1 + a₀ a₁ q^{e₀ + e₁}` whose monomial coefficients lie in
  `ℕ[a₀, a₁, a₂]`.
* `coe_pentagonWallFunction_isolated_inl_isolatedThd`: the wall `e₂⊥`, which crosses all other
  walls, keeps its input function `1 + a₂ z^{r(e₂)}`.

The statements on `frozenDatum` are instances of
`Mei.SkewLatticeDatum.AdaptedBasis.exists_isPositiveWallRepresentative_of_forall_form_eq_zero`,
and those on the unimodular datum and on `isolatedDatum` of
`Mei.SkewLatticeDatum.AdaptedBasis.IsTypeA₂WithIsolated.exists_isPositiveWallRepresentative_scat`;
see Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Theorem 1.13
(arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.Examples

open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

/-- The skew form `{x, y} = x₀ y₂ - x₂ y₀` on `ℤ³`, pairing `e₀` with `e₂`. -/
def frozenForm : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => ((x 0 * y 2 - x 2 * y 0 : ℤ) : ℚ))
    (fun x x' y => by push_cast [Pi.add_apply]; ring)
    (fun c x y => by push_cast [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by push_cast [Pi.add_apply]; ring)
    (fun c x y => by push_cast [Pi.smul_apply, smul_eq_mul]; ring)

/-- The values of `frozenForm`. -/
@[simp]
theorem frozenForm_apply (x y : Fin 3 → ℤ) :
    frozenForm x y = ((x 0 * y 2 - x 2 * y 0 : ℤ) : ℚ) :=
  LinearMap.mk₂_apply ..

/-- The skew lattice datum on `ℤ³` with form `frozenForm`, unfrozen basis vectors `e₀, e₁`, frozen
basis vector `e₂` and multipliers one. -/
def frozenDatum : SkewLatticeDatum (Fin 3 → ℤ) :=
  ofBasis (Pi.basisFun ℤ (Fin 3)) {0, 1} (fun _ => 1) frozenForm (fun _ => one_pos)
    (fun x => by simp [mul_comm]) (fun _ _ _ => ⟨_, frozenForm_apply _ _⟩)
    (fun _ _ _ => ⟨_, frozenForm_apply _ _⟩)

/-- The standard basis of `ℤ³` as an adapted basis of `frozenDatum`. -/
def frozenBasis : frozenDatum.AdaptedBasis (Fin 3) :=
  AdaptedBasis.ofBasis ..

/-- The form of `frozenDatum` is `frozenForm`. -/
@[simp]
theorem frozenDatum_form : frozenDatum.form = frozenForm :=
  ofBasis_form ..

/-- The basis of `frozenBasis` is the standard basis. -/
@[simp]
theorem frozenBasis_basis : frozenBasis.basis = Pi.basisFun ℤ (Fin 3) :=
  AdaptedBasis.ofBasis_basis

/-- The unfrozen indices of `frozenBasis` are `0` and `1`. -/
@[simp]
theorem frozenBasis_unfrozenIndex : frozenBasis.unfrozenIndex = {0, 1} :=
  AdaptedBasis.ofBasis_unfrozenIndex

/-- The form of `frozenDatum` is not zero: `{e₀, e₂} = 1`. -/
theorem frozenDatum_form_ne_zero : frozenDatum.form ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun₂ h (Pi.single 0 1) (Pi.single 2 1)
  simp at h'

/-- The form of `frozenDatum` vanishes on the unfrozen sublattice `ℤ e₀ ⊕ ℤ e₁`. -/
theorem frozenDatum_form_unfrozen_eq_zero (n m : frozenDatum.unfrozen) :
    frozenDatum.form n m = 0 := by
  have hn := frozenBasis.mem_unfrozen_iff.mp n.2 2 (by simp)
  have hm := frozenBasis.mem_unfrozen_iff.mp m.2 2 (by simp)
  simp only [frozenBasis_basis, Pi.basisFun_repr] at hn hm
  simp [hn, hm]

local notation "𝒅" => frozenBasis.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ frozenDatum.sublattice × frozenDatum.unfrozen
local notation "Qpr" => frozenDatum.principalCoefficientMonoid 𝒅

/-- The principal positive monoid lies in the principal coefficient monoid. -/
instance : Fact ((frozenDatum.principalPositiveDegrees 𝒅).monoid ≤ Qpr) :=
  ⟨frozenDatum.principalPositiveDegrees_le_coefficientMonoid 𝒅⟩

/-- The principal lattice `M° × N_uf` of `frozenDatum` is free. -/
instance : Module.Free ℤ Lpr := by
  have := Module.Free.of_basis frozenBasis.sublatticeBasis
  have := Module.Finite.of_basis frozenBasis.sublatticeBasis
  have := Module.Free.of_basis frozenBasis.unfrozenBasis
  infer_instance

/-- The principal coefficient monoid contains every character `(χ, 0)`. -/
theorem mem_principalCoefficientMonoid_frozenDatum (χ : Module.Dual ℤ frozenDatum.sublattice) :
    ((χ, 0) : Lpr) ∈ Qpr := by
  simp

/-- The independent coefficients `aᵢₛ ∈ ℚ[a]`, `s < 2`, of the input. -/
def frozenCoefficient (i : frozenBasis.unfrozenIndex) (s : Fin 2) :
    MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ :=
  MvPolynomial.X (i, s)

local notation "F" A => TropicalVertexCoefficientAction.filtration (R := A)
  (frozenDatum.principalPositiveDegrees 𝒅) Qpr
local notation "σ" A => MonoidHom.comp (AlgFiltration.completedBCHAction (F A)
  (frozenDatum.principalPositiveDegrees 𝒅)
  (tropicalVertexGrading (R := A) (frozenDatum.principalPositiveDegrees 𝒅) (AddMonoidHom.id Lpr)))
  (GradedLieHom.completedMap (frozenDatum.principalGraphGradedLieHom (R := A) 𝒅))

variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : Lpr →+ V}
  (h : TauCeti.Toric.IsIntegralLattice p) [AddCommGroup M] (π : Lpr →+ M)

open scoped Classical in
/-- For every integral lattice structure on `L_pr,ℝ`, the outgoing scattering class of the
adapted polynomial input of `frozenDatum` with multiplicities `(2, 2)` and independent
coefficients has a representative whose grouped wall functions have monomial coefficients in
`ℕ[aᵢₛ]`. -/
theorem exists_isPositiveWallRepresentative_frozenDatum :
    ∃ (κ : Type) (E : DirectedDiagram (d := frozenDatum.principalPositiveDegrees 𝒅) h
        (frozenDatum.principalGraphWallSpaces
          (R := MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ) 𝒅) κ),
      E.toClass = (frozenBasis.adaptedPolynomialInput (fun _ => 2) frozenCoefficient h).Scat
        (frozenBasis.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative (σ (MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ))
        (mapRingHom Qpr (MvPolynomial.map (Nat.castRingHom ℚ))).rangeS π :=
  frozenBasis.exists_isPositiveWallRepresentative_of_forall_form_eq_zero _ _ Qpr h π
    frozenDatum_form_unfrozen_eq_zero mem_principalCoefficientMonoid_frozenDatum _
    fun i s => ⟨MvPolynomial.X (i, s), by simp [frozenCoefficient]⟩

open scoped Classical in
/-- The grouped wall function of the input wall at `eᵢ` is
`1 + aᵢ₀ z^{r(eᵢ)} + aᵢ₁ z^{2 r(eᵢ)}`. -/
theorem coe_completedPolynomialWallFunction_frozenDatum (i : frozenBasis.unfrozenIndex) :
    (frozenBasis.completedPolynomialWallFunction (fun _ => 2) frozenCoefficient Qpr i :
        (F (MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ)).completion) =
      (F (MvPolynomial (frozenBasis.unfrozenIndex × Fin 2) ℚ)).toCompletion
        (1 + single (frozenBasis.principalExponent Qpr i) (MvPolynomial.X (i, 0)) +
          single (2 • frozenBasis.principalExponent Qpr i) (MvPolynomial.X (i, 1))) := by
  simp only [AdaptedBasis.coe_completedPolynomialWallFunction, Fin.sum_univ_two, add_assoc,
    Fin.val_zero, Fin.val_one, zero_add, one_smul, one_add_one_eq_two, frozenCoefficient]

open scoped Classical in
/-- The binomial input over `ℚ`, with walls `(eᵢ⊥, 1 + q^{eᵢ})`: its outgoing scattering class
has a representative whose grouped wall functions have natural-number coefficients. -/
theorem exists_isPositiveWallRepresentative_frozenDatum_binomial :
    ∃ (κ : Type) (E : DirectedDiagram (d := frozenDatum.principalPositiveDegrees 𝒅) h
        (frozenDatum.principalGraphWallSpaces (R := ℚ) 𝒅) κ),
      E.toClass = (frozenBasis.adaptedPolynomialInput (fun _ => 1) (fun _ _ => (1 : ℚ)) h).Scat
        (frozenBasis.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative (σ ℚ) (mapRingHom Qpr (Nat.castRingHom ℚ)).rangeS π :=
  frozenBasis.exists_isPositiveWallRepresentative_of_forall_form_eq_zero _ _ Qpr h π
    frozenDatum_form_unfrozen_eq_zero mem_principalCoefficientMonoid_frozenDatum _
    fun _ _ => ⟨1, map_one _⟩

open scoped Classical in
/-- The grouped wall function of the binomial input at `eᵢ` is `1 + z^{r(eᵢ)}`. -/
theorem coe_completedPolynomialWallFunction_frozenDatum_binomial
    (i : frozenBasis.unfrozenIndex) :
    (frozenBasis.completedPolynomialWallFunction (fun _ => 1) (fun _ _ => (1 : ℚ)) Qpr i :
        (F ℚ).completion) =
      (F ℚ).toCompletion (1 + single (frozenBasis.principalExponent Qpr i) 1) := by
  simp

end Mei.SkewLatticeDatum.Examples

namespace Mei.SkewLatticeDatum.Examples

open AdaptedBasis
open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

/-- The standard basis of the unimodular rank-two datum, with `{e₁, e₂} = 1` and `N° = N`, is of
type `A₂` at its two indices, without isolated indices. -/
theorem isTypeA₂WithIsolated_unimodularRankTwoAdaptedBasis :
    unimodularRankTwoAdaptedBasis.IsTypeA₂WithIsolated unimodularRankTwoFst
      unimodularRankTwoSnd where
  form_eq_one := by simp
  multiplier_eq_one i := unimodularRankTwoAdaptedBasis_multiplier i
  form_eq_zero i hi₁ hi₂ := by
    obtain ⟨i, hi⟩ := i
    fin_cases i
    exacts [absurd rfl hi₁, absurd rfl hi₂]

local notation "𝒅" => unimodularRankTwoAdaptedBasis.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ unimodularRankTwo.sublattice × unimodularRankTwo.unfrozen
local notation "Qpr" => unimodularRankTwo.principalCoefficientMonoid 𝒅

/-- The principal positive monoid of the unimodular rank-two datum lies in its principal
coefficient monoid. -/
instance : Fact ((unimodularRankTwo.principalPositiveDegrees 𝒅).monoid ≤ Qpr) :=
  ⟨unimodularRankTwo.principalPositiveDegrees_le_coefficientMonoid 𝒅⟩

/-- The principal lattice `M° × N_uf` of the unimodular rank-two datum is free. -/
instance : Module.Free ℤ Lpr := by
  have := Module.Free.of_basis unimodularRankTwoAdaptedBasis.sublatticeBasis
  have := Module.Finite.of_basis unimodularRankTwoAdaptedBasis.sublatticeBasis
  have := Module.Free.of_basis unimodularRankTwoAdaptedBasis.unfrozenBasis
  infer_instance

local notation "σ" A => MonoidHom.comp (AlgFiltration.completedBCHAction
  (TropicalVertexCoefficientAction.filtration (R := A)
    (unimodularRankTwo.principalPositiveDegrees 𝒅) Qpr)
  (unimodularRankTwo.principalPositiveDegrees 𝒅)
  (tropicalVertexGrading (R := A) (unimodularRankTwo.principalPositiveDegrees 𝒅)
    (AddMonoidHom.id Lpr)))
  (GradedLieHom.completedMap (unimodularRankTwo.principalGraphGradedLieHom (R := A) 𝒅))

variable {R V M : Type*} [CommRing R] [Algebra ℚ R] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {p : Lpr →+ V} (h : TauCeti.Toric.IsIntegralLattice p) [AddCommGroup M] (π : Lpr →+ M)

open scoped Classical in
/-- **The cluster scattering diagram of type `A₂`.** For the unimodular rank-two datum with
`{e₁, e₂} = 1`, the outgoing scattering class of the ordinary binomial input
`(e₁⊥, 1 + q^{e₁})`, `(e₂⊥, 1 + q^{e₂})` on the principal lattice has a consistent outgoing
representative with the single additional wall `{ν_{e₁} + ν_{e₂} = 0, ν_{e₁} ≥ 0}`, whose
grouped wall functions `1 + q^{e₁}`, `1 + q^{e₂}` and `1 + q^{e₁ + e₂}` are positive for the image
of `ℕ[Q]`, `Q` the principal coefficient monoid. -/
theorem exists_isPositiveWallRepresentative_unimodularRankTwo :
    ∃ (κ : Type) (E : DirectedDiagram (d := unimodularRankTwo.principalPositiveDegrees 𝒅) h
        (unimodularRankTwo.principalGraphWallSpaces (R := R) 𝒅)
        (unimodularRankTwoAdaptedBasis.unfrozenIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (unimodularRankTwoAdaptedBasis.adaptedPolynomialInput
        (V := V) (fun _ => 1) (fun _ _ => (1 : R)) h).wall E ∧
      E.toClass = (unimodularRankTwoAdaptedBasis.adaptedPolynomialInput (fun _ => 1)
        (fun _ _ => (1 : R)) h).Scat
          (unimodularRankTwoAdaptedBasis.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative (σ R) (mapRingHom Qpr (Nat.castRingHom R)).rangeS π :=
  isTypeA₂WithIsolated_unimodularRankTwoAdaptedBasis.exists_isPositiveWallRepresentative_scat h
    (fun _ => (1 : R)) π Qpr
    (fun _ => (unimodularRankTwo.mem_principalCoefficientMonoid _ _).mpr (zero_mem _))
    (Nat.castRingHom R) fun _ => ⟨1, map_one _⟩

open scoped Classical in
/-- **The scattering diagram of type `A₂` with coefficients.** For the unimodular rank-two datum
and independent variables `a₀, a₁`, the outgoing scattering class of the adapted polynomial input
`(e₁⊥, 1 + a₀ q^{e₁})`, `(e₂⊥, 1 + a₁ q^{e₂})` has a consistent outgoing representative with the
single additional wall `{ν_{e₁} + ν_{e₂} = 0, ν_{e₁} ≥ 0}`, whose grouped wall functions
`1 + a₀ q^{e₁}`, `1 + a₁ q^{e₂}` and `1 + a₀ a₁ q^{e₁ + e₂}` have monomial coefficients in
`ℕ[a₀, a₁]`. -/
theorem exists_isPositiveWallRepresentative_unimodularRankTwo_coefficient :
    ∃ (κ : Type) (E : DirectedDiagram (d := unimodularRankTwo.principalPositiveDegrees 𝒅) h
        (unimodularRankTwo.principalGraphWallSpaces
          (R := MvPolynomial unimodularRankTwoAdaptedBasis.unfrozenIndex ℚ) 𝒅)
        (unimodularRankTwoAdaptedBasis.unfrozenIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (unimodularRankTwoAdaptedBasis.adaptedPolynomialInput
        (V := V) (fun _ => 1) (fun i _ => MvPolynomial.X i) h).wall E ∧
      E.toClass = (unimodularRankTwoAdaptedBasis.adaptedPolynomialInput (fun _ => 1)
        (fun i _ => MvPolynomial.X i) h).Scat
          (unimodularRankTwoAdaptedBasis.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative
        (σ (MvPolynomial unimodularRankTwoAdaptedBasis.unfrozenIndex ℚ))
        (mapRingHom Qpr (MvPolynomial.map (Nat.castRingHom ℚ))).rangeS π :=
  isTypeA₂WithIsolated_unimodularRankTwoAdaptedBasis.exists_isPositiveWallRepresentative_scat h
    MvPolynomial.X π Qpr
    (fun _ => (unimodularRankTwo.mem_principalCoefficientMonoid _ _).mpr (zero_mem _))
    (MvPolynomial.map (Nat.castRingHom ℚ))
    fun i => ⟨MvPolynomial.X i, MvPolynomial.map_X _ i⟩

open scoped Classical in
/-- The wall function of the outgoing wall of the pentagon diagram with the independent
coefficients `a₀, a₁` is `1 + a₀ a₁ z^{r(e₁ + e₂)}`: its coefficient is the product of the input
coefficients. -/
theorem coe_pentagonWallFunction_unimodularRankTwo_inr :
    (isTypeA₂WithIsolated_unimodularRankTwoAdaptedBasis.pentagonWallFunction MvPolynomial.X Qpr
        (.inr ())).val =
      1 + (TropicalVertexCoefficientAction.filtration
          (R := MvPolynomial unimodularRankTwoAdaptedBasis.unfrozenIndex ℚ)
          (unimodularRankTwo.principalPositiveDegrees 𝒅) Qpr).toCompletion
        (single (unimodularRankTwoAdaptedBasis.pentagonExponent Qpr unimodularRankTwoFst
          unimodularRankTwoSnd (.inr ()))
          (MvPolynomial.X unimodularRankTwoFst * MvPolynomial.X unimodularRankTwoSnd)) :=
  isTypeA₂WithIsolated_unimodularRankTwoAdaptedBasis.coe_pentagonWallFunction_inr _ _ ()

end Mei.SkewLatticeDatum.Examples

namespace Mei.SkewLatticeDatum.Examples

open AdaptedBasis
open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

/-- The skew form `{x, y} = x₀ y₁ - x₁ y₀` on `ℤ³`, pairing `e₀` with `e₁`. -/
def isolatedForm : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => ((x 0 * y 1 - x 1 * y 0 : ℤ) : ℚ))
    (fun x x' y => by push_cast [Pi.add_apply]; ring)
    (fun c x y => by push_cast [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by push_cast [Pi.add_apply]; ring)
    (fun c x y => by push_cast [Pi.smul_apply, smul_eq_mul]; ring)

/-- The values of `isolatedForm`. -/
@[simp]
theorem isolatedForm_apply (x y : Fin 3 → ℤ) :
    isolatedForm x y = ((x 0 * y 1 - x 1 * y 0 : ℤ) : ℚ) :=
  LinearMap.mk₂_apply ..

/-- The skew lattice datum on `ℤ³` with form `isolatedForm`, every basis vector unfrozen and
multipliers one. -/
def isolatedDatum : SkewLatticeDatum (Fin 3 → ℤ) :=
  ofBasis (Pi.basisFun ℤ (Fin 3)) Finset.univ (fun _ => 1) isolatedForm (fun _ => one_pos)
    (fun x => by simp [mul_comm]) (fun _ _ _ => ⟨_, isolatedForm_apply _ _⟩)
    (fun _ _ _ => ⟨_, isolatedForm_apply _ _⟩)

/-- The standard basis of `ℤ³` as an adapted basis of `isolatedDatum`. -/
def isolatedBasis : isolatedDatum.AdaptedBasis (Fin 3) :=
  AdaptedBasis.ofBasis ..

/-- The form of `isolatedDatum` is `isolatedForm`. -/
@[simp]
theorem isolatedDatum_form : isolatedDatum.form = isolatedForm :=
  ofBasis_form ..

/-- The basis of `isolatedBasis` is the standard basis. -/
@[simp]
theorem isolatedBasis_basis : isolatedBasis.basis = Pi.basisFun ℤ (Fin 3) :=
  AdaptedBasis.ofBasis_basis

/-- Every index of `isolatedBasis` is unfrozen. -/
@[simp]
theorem isolatedBasis_unfrozenIndex : isolatedBasis.unfrozenIndex = Finset.univ :=
  AdaptedBasis.ofBasis_unfrozenIndex

/-- The multipliers of `isolatedBasis` are one. -/
@[simp]
theorem isolatedBasis_multiplier : isolatedBasis.multiplier = fun _ => 1 :=
  AdaptedBasis.ofBasis_multiplier

/-- The unfrozen index `0` of `isolatedBasis`. -/
abbrev isolatedFst : isolatedBasis.unfrozenIndex := ⟨0, by simp⟩

/-- The unfrozen index `1` of `isolatedBasis`. -/
abbrev isolatedSnd : isolatedBasis.unfrozenIndex := ⟨1, by simp⟩

/-- The isolated unfrozen index `2` of `isolatedBasis`. -/
abbrev isolatedThd : isolatedBasis.unfrozenIndex := ⟨2, by simp⟩

/-- The form of `isolatedDatum` is degenerate on the unfrozen lattice `N_uf = ℤ³`: `e₂` pairs to
zero with every vector. -/
theorem isolatedDatum_form_single_two (y : Fin 3 → ℤ) :
    isolatedDatum.form (Pi.single 2 1) y = 0 := by
  simp

/-- The form of `isolatedDatum` does not vanish on `N_uf`: `{e₀, e₁} = 1`. -/
theorem isolatedDatum_form_single_zero_single_one :
    isolatedDatum.form (Pi.single 0 1) (Pi.single 1 1) = 1 := by
  simp

/-- The standard basis of `isolatedDatum` is of type `A₂` at `0, 1` with the isolated index
`2`. -/
theorem isTypeA₂WithIsolated_isolatedBasis :
    isolatedBasis.IsTypeA₂WithIsolated isolatedFst isolatedSnd where
  form_eq_one := by simp
  multiplier_eq_one i := congrFun isolatedBasis_multiplier i
  form_eq_zero i hi₁ hi₂ j := by
    obtain ⟨i, hi⟩ := i
    fin_cases i
    · exact absurd rfl hi₁
    · exact absurd rfl hi₂
    · simp

local notation "𝒅" => isolatedBasis.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ isolatedDatum.sublattice × isolatedDatum.unfrozen
local notation "Qpr" => isolatedDatum.principalCoefficientMonoid 𝒅
local notation "𝒜" => MvPolynomial isolatedBasis.unfrozenIndex ℚ

/-- The principal positive monoid of `isolatedDatum` lies in its principal coefficient monoid. -/
instance : Fact ((isolatedDatum.principalPositiveDegrees 𝒅).monoid ≤ Qpr) :=
  ⟨isolatedDatum.principalPositiveDegrees_le_coefficientMonoid 𝒅⟩

/-- The principal lattice `M° × N_uf` of `isolatedDatum` is free. -/
instance : Module.Free ℤ Lpr := by
  have := Module.Free.of_basis isolatedBasis.sublatticeBasis
  have := Module.Finite.of_basis isolatedBasis.sublatticeBasis
  have := Module.Free.of_basis isolatedBasis.unfrozenBasis
  infer_instance

local notation "F" => TropicalVertexCoefficientAction.filtration (R := 𝒜)
  (isolatedDatum.principalPositiveDegrees 𝒅) Qpr
local notation "σ" => MonoidHom.comp (AlgFiltration.completedBCHAction F
  (isolatedDatum.principalPositiveDegrees 𝒅)
  (tropicalVertexGrading (R := 𝒜) (isolatedDatum.principalPositiveDegrees 𝒅)
    (AddMonoidHom.id Lpr)))
  (GradedLieHom.completedMap (isolatedDatum.principalGraphGradedLieHom (R := 𝒜) 𝒅))

variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : Lpr →+ V}
  (h : TauCeti.Toric.IsIntegralLattice p) [AddCommGroup M] (π : Lpr →+ M)

open scoped Classical in
/-- **A degenerate form of rank three.** For `isolatedDatum`, with `{e₀, e₁} = 1` and `e₂` in the
radical of the form, and independent variables `a₀, a₁, a₂`, the outgoing scattering class of the
adapted polynomial input `(eᵢ⊥, 1 + aᵢ q^{eᵢ})`, `i = 0, 1, 2`, has a consistent outgoing
representative with the single additional wall `{ν_{e₀} + ν_{e₁} = 0, ν_{e₀} ≥ 0}`, whose grouped
wall functions `1 + aᵢ q^{eᵢ}` and `1 + a₀ a₁ q^{e₀ + e₁}` have monomial coefficients in
`ℕ[a₀, a₁, a₂]`. The hyperplane `e₂⊥` crosses the other walls without any correction. -/
theorem exists_isPositiveWallRepresentative_isolated :
    ∃ (κ : Type) (E : DirectedDiagram (d := isolatedDatum.principalPositiveDegrees 𝒅) h
        (isolatedDatum.principalGraphWallSpaces (R := 𝒜) 𝒅) (isolatedBasis.unfrozenIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (isolatedBasis.adaptedPolynomialInput
        (V := V) (fun _ => 1) (fun i _ => MvPolynomial.X i) h).wall E ∧
      E.toClass = (isolatedBasis.adaptedPolynomialInput (fun _ => 1)
        (fun i _ => MvPolynomial.X i) h).Scat (isolatedBasis.adaptedPolynomialInput_full _ _ h) ∧
      E.IsPositiveWallRepresentative σ
        (mapRingHom Qpr (MvPolynomial.map (Nat.castRingHom ℚ))).rangeS π :=
  isTypeA₂WithIsolated_isolatedBasis.exists_isPositiveWallRepresentative_scat h
    MvPolynomial.X π Qpr
    (fun _ => (isolatedDatum.mem_principalCoefficientMonoid _ _).mpr (zero_mem _))
    (MvPolynomial.map (Nat.castRingHom ℚ))
    fun i => ⟨MvPolynomial.X i, MvPolynomial.map_X _ i⟩

open scoped Classical in
/-- The wall function of the input wall at the isolated index `2` of the pentagon diagram of
`isolatedDatum` with the independent coefficients `a₀, a₁, a₂` is `1 + a₂ z^{r(e₂)}`: the
isolated wall keeps its input function. -/
theorem coe_pentagonWallFunction_isolated_inl_isolatedThd :
    (isTypeA₂WithIsolated_isolatedBasis.pentagonWallFunction MvPolynomial.X Qpr
        (.inl isolatedThd)).val =
      1 + (F).toCompletion (single (isolatedBasis.pentagonExponent Qpr isolatedFst isolatedSnd
        (.inl isolatedThd)) (MvPolynomial.X isolatedThd)) :=
  isTypeA₂WithIsolated_isolatedBasis.coe_pentagonWallFunction_inl _ _ _

end Mei.SkewLatticeDatum.Examples
