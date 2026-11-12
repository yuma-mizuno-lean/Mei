/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Pentagon.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Tropical

/-!
# Adapted polynomial inputs of rank two as rank-two polynomial inputs

Let `(eᵢ)` be an adapted basis of a skew lattice datum of rank two, indexed by `ι` with
`Nat.card ι = 2`, such that the principal character `p₁*(eᵢ) = {eᵢ, -}|_{N°}` is nonzero at every
unfrozen index `i`. On the principal lattice `L_pr = M° × N_uf` with the principal positive
degrees, the adapted polynomial input with wall functions `fᵢ = 1 + ∑_{s<ℓᵢ} aᵢₛ T^(s+1)` defines
a rank-two polynomial input (`AdaptedBasis.toRankTwoPolynomialInput`): the projection is
`π = pr₁ : L_pr → M°`, the line at `i` has as tangent the primitive generator `mᵢ` of the ray
`ℝ_{≥0} p₁*(eᵢ)` (`AdaptedBasis.principalTangent`), as coorientation the normalized normal
`κ(eᵢ)⟨eᵢ, -⟩` and offset `0`, and its exponents are `(s + 1) r(eᵢ)` for `s < ℓᵢ`, with
`r(eᵢ) = (p₁*(eᵢ), eᵢ)` the principal exponent. Its coefficient of `z^{(s+1) r(eᵢ)}` is `aᵢₛ`
(`AdaptedBasis.rankTwoCoefficient_mk_nsmul_principalEmbedding`).

The cylinder normal of the line `i` is the primitive principal normal `κ(eᵢ)νᵢ`, and the unsplit
label of the line `i` is the image of the adapted polynomial label at `i` under the
fixed-degree principal realization (`AdaptedBasis.initialLabel_toRankTwoPolynomialInput`). Since
that label lies on the principal ray of `r(eᵢ)`, the incoming diagram of the rank-two input is
the tropical vertex image of the adapted polynomial input with identity ray walls added, and the
two are equivalent (`AdaptedBasis.equivalent_map_adaptedPolynomialInput`). Hence the image of the
outgoing scattering class of the adapted polynomial input is the outgoing scattering class of the
rank-two input (`AdaptedBasis.map_scat_adaptedPolynomialInput`).

If the unfrozen indices are `i₁, i₂`, with `ℓ_{i₁} = ℓ_{i₂} = 1` and
`d_{i₁} {e_{i₁}, e_{i₂}} = d_{i₂} {e_{i₁}, e_{i₂}} = 1`, the rank-two input is of type `A₂` in
the sense of `Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Pentagon.Basic`
(`AdaptedBasis.isTypeA₂_toRankTwoPolynomialInput`), so its scattering class is represented by the
pentagon diagram.

For the zero form the principal characters vanish, so there is no such rank-two input when
`N_uf ≠ 0`. Instead, whenever the form vanishes on `N_uf` the adapted input and its tropical
vertex image are consistent (`AdaptedBasis.map_scat_adaptedPolynomialInput_of_forall_form_eq_zero`
in `Mei.Geometry.ScatteringDiagram.Skew.Principal.Tropical`).

The rank-two polynomial inputs are those of Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, Theorem 9.9 (arXiv:2503.03719v1), and the principal realization is that of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and Appendix B
(arXiv:1411.1394v2). The comparison of diagrams is
`DirectedDiagram.IsRayFactorPresentation.equivalent`.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open _root_.AddMonoidAlgebra PowerSeries

universe u

section General

variable {N : Type*} {ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N}
  (B : D.AdaptedBasis ι)

local notation "𝒅" => B.unfrozenBasis.positiveDegrees
local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "e" => D.principalPositiveDegrees 𝒅

section Tangent

variable [Finite ι]

/-- A nonzero principal character `p₁*(eᵢ)` is a positive multiple of a primitive vector of
`M°`. -/
theorem exists_isPrimitive_principalCharacter_eq_nsmul {i : B.unfrozenIndex}
    (hi : D.principalCharacter (B.unfrozenBasis i) ≠ 0) :
    ∃ m : Module.Dual ℤ D.sublattice, TauCeti.IsPrimitive m ∧
      ∃ k : ℕ, 0 < k ∧ D.principalCharacter (B.unfrozenBasis i) = k • m := by
  classical
  have := Module.Free.of_basis B.sublatticeBasis.dualBasis
  obtain ⟨k, m, hk, hm, he⟩ := TauCeti.exists_eq_zsmul_isPrimitive hi
  refine ⟨m, hm, k.toNat, by omega, ?_⟩
  rw [he, ← natCast_zsmul, Int.toNat_of_nonneg hk.le]

/-- The primitive generator `mᵢ` of the ray `ℝ_{≥0} p₁*(eᵢ)` of a nonzero principal
character. -/
def principalTangent {i : B.unfrozenIndex} (hi : D.principalCharacter (B.unfrozenBasis i) ≠ 0) :
    Module.Dual ℤ D.sublattice :=
  (B.exists_isPrimitive_principalCharacter_eq_nsmul hi).choose

/-- The primitive generator of the ray of `p₁*(eᵢ)` is primitive. -/
theorem isPrimitive_principalTangent {i : B.unfrozenIndex}
    (hi : D.principalCharacter (B.unfrozenBasis i) ≠ 0) :
    TauCeti.IsPrimitive (B.principalTangent hi) :=
  (B.exists_isPrimitive_principalCharacter_eq_nsmul hi).choose_spec.1

/-- The principal character `p₁*(eᵢ)` is a positive multiple of its primitive generator. -/
theorem exists_principalCharacter_eq_nsmul_principalTangent {i : B.unfrozenIndex}
    (hi : D.principalCharacter (B.unfrozenBasis i) ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ D.principalCharacter (B.unfrozenBasis i) = k • B.principalTangent hi :=
  (B.exists_isPrimitive_principalCharacter_eq_nsmul hi).choose_spec.2

end Tangent

section Exponent

/-- The multiples `k r(eᵢ)` of a principal exponent are distinct. -/
theorem nsmul_principalEmbedding_injective (i : B.unfrozenIndex) :
    Function.Injective fun k : ℕ => k • D.principalEmbedding (B.unfrozenBasis i) := by
  intro k l hkl
  have h := congrArg (fun x : Lpr => B.unfrozenBasis.repr x.2 i) hkl
  simpa using h

variable (ℓ : B.unfrozenIndex → ℕ)

/-- The exponents `(s + 1) r(eᵢ)`, `s < ℓᵢ`, of the adapted polynomial wall function at `i`. -/
def principalExponents (i : B.unfrozenIndex) : Finset Lpr :=
  Finset.univ.map ⟨fun s : Fin (ℓ i) => (s.val + 1) • D.principalEmbedding (B.unfrozenBasis i),
    fun s t hst => Fin.ext (by simpa using B.nsmul_principalEmbedding_injective i hst)⟩

/-- The exponents at `i` are the multiples `(s + 1) r(eᵢ)` with `s < ℓᵢ`. -/
theorem mem_principalExponents {i : B.unfrozenIndex} {n : Lpr} :
    n ∈ B.principalExponents ℓ i ↔
      ∃ s : Fin (ℓ i), (s.val + 1) • D.principalEmbedding (B.unfrozenBasis i) = n := by
  simp [principalExponents]

/-- The exponent `(s + 1) r(eᵢ)` with `s < ℓᵢ`. -/
theorem nsmul_principalEmbedding_mem_principalExponents (i : B.unfrozenIndex) (s : Fin (ℓ i)) :
    (s.val + 1) • D.principalEmbedding (B.unfrozenBasis i) ∈ B.principalExponents ℓ i :=
  (B.mem_principalExponents ℓ).mpr ⟨s, rfl⟩

/-- A line with `ℓᵢ = 1` has the single exponent `r(eᵢ)`. -/
theorem principalExponents_eq_singleton {i : B.unfrozenIndex} (hℓ : ℓ i = 1) :
    B.principalExponents ℓ i = {D.principalEmbedding (B.unfrozenBasis i)} := by
  ext n
  rw [mem_principalExponents, Finset.mem_singleton]
  constructor
  · rintro ⟨s, rfl⟩
    have hs : s.val = 0 := by
      have := s.isLt
      omega
    simp [hs]
  · rintro rfl
    exact ⟨⟨0, by omega⟩, by simp⟩

end Exponent

variable [Module.Free ℤ N] [Finite ι] (ℓ : B.unfrozenIndex → ℕ) (hrank : Nat.card ι = 2)
  (hχ : ∀ i : B.unfrozenIndex, D.principalCharacter (B.unfrozenBasis i) ≠ 0)

/-- The rank-two polynomial input of an adapted basis of rank two whose principal characters
`p₁*(eᵢ)` are nonzero at all unfrozen indices `i`, on the principal lattice `L_pr = M° × N_uf` with
the principal positive degrees. The projection is `π = pr₁ : L_pr → M°`; the line at `i` passes
through the origin, with tangent the primitive generator of `ℝ_{≥0} p₁*(eᵢ)` and coorientation
`κ(eᵢ)⟨eᵢ, -⟩`, and its exponents are `(s + 1) r(eᵢ)` for `s < ℓᵢ`. -/
def toRankTwoPolynomialInput :
    RankTwoPolynomialInput e (Module.Dual ℤ D.sublattice) B.unfrozenIndex where
  projection := AddMonoidHom.fst _ _
  projection_surjective := Prod.fst_surjective
  finrank_eq_two := by
    classical
    rw [Module.finrank_eq_nat_card_basis B.sublatticeBasis.dualBasis, hrank]
  tangent i := B.principalTangent (hχ i)
  isPrimitive_tangent i := B.isPrimitive_principalTangent (hχ i)
  normal i := D.projectedPrincipalNormal (B.unfrozenBasis i)
  isPrimitive_normal i := by
    obtain ⟨φ, hφ⟩ := B.exists_principalNormal_eq_one i
    exact TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ φ, by simpa using hφ⟩
  normal_tangent i := by
    obtain ⟨k, hk, he⟩ := B.exists_principalCharacter_eq_nsmul_principalTangent (hχ i)
    have h0 := D.principalCharacter_rayVector_self (B.unfrozenBasis i)
    rw [he, LinearMap.smul_apply, smul_eq_zero] at h0
    rw [projectedPrincipalNormal_apply]
    exact h0.resolve_left hk.ne'
  offset _ := 0
  exponents := B.principalExponents ℓ
  mem_monoid_of_mem_exponents {i n} hn := by
    obtain ⟨s, rfl⟩ := (B.mem_principalExponents ℓ).mp hn
    exact nsmul_mem (B.principalEmbedding_unfrozenBasis_mem i) _
  ne_zero_of_mem_exponents {i n} hn := by
    obtain ⟨s, rfl⟩ := (B.mem_principalExponents ℓ).mp hn
    exact fun h0 => s.val.succ_ne_zero
      (B.nsmul_principalEmbedding_injective i (h0.trans (zero_nsmul _).symm))
  exists_projection_eq_of_mem_exponents {i n} hn := by
    obtain ⟨s, rfl⟩ := (B.mem_principalExponents ℓ).mp hn
    obtain ⟨k, hk, he⟩ := B.exists_principalCharacter_eq_nsmul_principalTangent (hχ i)
    refine ⟨(s.val + 1) * k, Nat.mul_pos s.val.succ_pos hk, ?_⟩
    simp only [map_nsmul, AddMonoidHom.coe_fst, principalEmbedding_apply, he, smul_smul]
  finite_nontrivial _ := Set.toFinite _

local notation "I" => B.toRankTwoPolynomialInput ℓ hrank hχ

/-- The projection is the first projection `pr₁ : L_pr → M°`. -/
@[simp]
theorem toRankTwoPolynomialInput_projection : (I).projection = AddMonoidHom.fst _ _ := (rfl)

/-- The tangent of the line at `i` is the primitive generator of `ℝ_{≥0} p₁*(eᵢ)`. -/
@[simp]
theorem toRankTwoPolynomialInput_tangent (i : B.unfrozenIndex) :
    (I).tangent i = B.principalTangent (hχ i) := (rfl)

/-- The coorientation of the line at `i` is the normalized normal `κ(eᵢ)⟨eᵢ, -⟩`. -/
@[simp]
theorem toRankTwoPolynomialInput_normal (i : B.unfrozenIndex) :
    (I).normal i = D.projectedPrincipalNormal (B.unfrozenBasis i) := (rfl)

/-- The lines pass through the origin. -/
@[simp]
theorem toRankTwoPolynomialInput_offset (i : B.unfrozenIndex) : (I).offset i = 0 := (rfl)

/-- The exponents of the line at `i` are `(s + 1) r(eᵢ)` for `s < ℓᵢ`. -/
@[simp]
theorem toRankTwoPolynomialInput_exponents (i : B.unfrozenIndex) :
    (I).exponents i = B.principalExponents ℓ i := (rfl)

/-- The cylinder normal of the line at `i` is the primitive principal normal `κ(eᵢ)νᵢ`. -/
@[simp]
theorem wallNormal_toRankTwoPolynomialInput (i : B.unfrozenIndex) :
    (I).wallNormal i = (D.principalNormal (B.unfrozenBasis i)).toAddMonoidHom := by
  ext x
  simp [RankTwoPolynomialInput.wallNormal_apply]

/-- The exponent `(s + 1) r(eᵢ)` with `s < ℓᵢ` of the line at `i`. -/
theorem nsmul_principalEmbedding_mem_exponents (i : B.unfrozenIndex) (s : Fin (ℓ i)) :
    (s.val + 1) • D.principalEmbedding (B.unfrozenBasis i) ∈ (I).exponents i := by
  rw [toRankTwoPolynomialInput_exponents]
  exact B.nsmul_principalEmbedding_mem_principalExponents ℓ i s

/-- **The adapted input of type `A₂`.** Let the unfrozen indices be `i₁` and `i₂`, with
`ℓ_{i₁} = ℓ_{i₂} = 1` and `d_{i₁} {e_{i₁}, e_{i₂}} = d_{i₂} {e_{i₁}, e_{i₂}} = 1`. Then the
rank-two input is of type `A₂` at `i₁, i₂`, with exponents `r(e_{i₁})` and `r(e_{i₂})`. -/
theorem isTypeA₂_toRankTwoPolynomialInput {i₁ i₂ : B.unfrozenIndex}
    (hi : ∀ i, i = i₁ ∨ i = i₂) (hℓ₁ : ℓ i₁ = 1) (hℓ₂ : ℓ i₂ = 1)
    (h₁ : (B.multiplier i₁ : ℚ) * D.form (B.basis i₁) (B.basis i₂) = 1)
    (h₂ : (B.multiplier i₂ : ℚ) * D.form (B.basis i₁) (B.basis i₂) = 1) :
    (I).IsTypeA₂ i₁ i₂ (D.principalEmbedding (B.unfrozenBasis i₁))
      (D.principalEmbedding (B.unfrozenBasis i₂)) where
  eq_or_eq := hi
  exponents_fst := (B.toRankTwoPolynomialInput_exponents ℓ hrank hχ i₁).trans
    (B.principalExponents_eq_singleton ℓ hℓ₁)
  exponents_snd := (B.toRankTwoPolynomialInput_exponents ℓ hrank hχ i₂).trans
    (B.principalExponents_eq_singleton ℓ hℓ₂)
  offset_fst := B.toRankTwoPolynomialInput_offset ℓ hrank hχ i₁
  offset_snd := B.toRankTwoPolynomialInput_offset ℓ hrank hχ i₂
  wallNormal_fst_snd := by
    rw [wallNormal_toRankTwoPolynomialInput]
    apply Int.cast_injective (α := ℚ)
    rw [LinearMap.toAddMonoidHom_coe, cast_principalNormal_principalEmbedding, coe_unfrozenBasis,
      coe_unfrozenBasis, rayIndex_basis, D.form_swap, mul_neg, h₁]
    simp
  wallNormal_snd_fst := by
    rw [wallNormal_toRankTwoPolynomialInput]
    apply Int.cast_injective (α := ℚ)
    rw [LinearMap.toAddMonoidHom_coe, cast_principalNormal_principalEmbedding, coe_unfrozenBasis,
      coe_unfrozenBasis, rayIndex_basis, h₂]
    simp

variable {R : Type*} [CommRing R] (a : ∀ i, Fin (ℓ i) → R)

open Classical in
/-- The coefficient family of the adapted polynomial input: the coefficient of the term of degree
`(s + 1) r(eᵢ)` of the line at `i` is `aᵢₛ`. -/
def rankTwoCoefficient (x : (I).Variable) : R :=
  ∑ s : Fin (ℓ x.1),
    if (s.val + 1) • D.principalEmbedding (B.unfrozenBasis x.1) = x.2.val then a x.1 s else 0

/-- The coefficient of a term `z^n` of the line at `i` with `n = (s + 1) r(eᵢ)` is `aᵢₛ`. -/
theorem rankTwoCoefficient_eq {i : B.unfrozenIndex} (s : Fin (ℓ i)) {n : Lpr}
    (hn : n ∈ (I).exponents i) (hs : (s.val + 1) • D.principalEmbedding (B.unfrozenBasis i) = n) :
    B.rankTwoCoefficient ℓ hrank hχ a ⟨i, n, hn⟩ = a i s := by
  classical
  rw [rankTwoCoefficient, Fintype.sum_eq_single s fun t ht => ite_eq_right_iff.mpr fun hts =>
    (ht (Fin.ext (by simpa using B.nsmul_principalEmbedding_injective i (hts.trans hs.symm)))).elim]
  exact ite_eq_left_iff.mpr fun h => (h hs).elim

/-- The coefficient of the term `z^{(s + 1) r(eᵢ)}` of the line at `i` is `aᵢₛ`. -/
theorem rankTwoCoefficient_mk_nsmul_principalEmbedding (i : B.unfrozenIndex) (s : Fin (ℓ i)) :
    B.rankTwoCoefficient ℓ hrank hχ a
        ⟨i, _, B.nsmul_principalEmbedding_mem_exponents ℓ hrank hχ i s⟩ = a i s :=
  B.rankTwoCoefficient_eq ℓ hrank hχ a s _ rfl

local notation "ρ" => AddMonoidHom.id Lpr
local notation "χ" i => AddMonoidHom.comp (Int.castAddHom R)
  (RankTwoPolynomialInput.wallNormal (B.toRankTwoPolynomialInput ℓ hrank hχ) i)
local notation "G" i => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ (χ i))

/-- The principal exponent `r(eᵢ)` as a degree tangent to the cylinder of the line at `i`. -/
def tangentPrincipalExponent (i : B.unfrozenIndex) : tropicalTangentMonoid e ρ (χ i) :=
  ⟨D.principalEmbedding (B.unfrozenBasis i), (mem_tropicalTangentMonoid _ _ _ _).mpr
    ⟨B.principalEmbedding_unfrozenBasis_mem i, by
      simp [principalEmbedding_apply, -coe_unfrozenBasis]⟩⟩

/-- The tangent principal exponent is `r(eᵢ)`. -/
@[simp]
theorem coe_tangentPrincipalExponent (i : B.unfrozenIndex) :
    (B.tangentPrincipalExponent ℓ hrank hχ (R := R) i : Lpr) =
      D.principalEmbedding (B.unfrozenBasis i) := (rfl)

/-- The completed monomial `z^{r(eᵢ)}` lies in the first ideal of the tangent coefficient
algebra of the line at `i`. -/
theorem toCompletion_single_tangentPrincipalExponent_mem (i : B.unfrozenIndex) :
    (G i).toCompletion (single (B.tangentPrincipalExponent ℓ hrank hχ i) 1) ∈
      (G i).completionIdeal 1 :=
  D.toCompletion_single_principalEmbedding_mem_first 𝒅
    (B.unfrozenBasis_mem_positiveDegrees_monoid i) (B.unfrozenBasis.ne_zero i) _ _
    (B.coe_tangentPrincipalExponent ℓ hrank hχ i)

/-- The completed monomial `z^{r(eᵢ)}` of the tangent coefficient algebra of the line at `i`. -/
def tangentPrincipalMonomial (i : B.unfrozenIndex) : (G i).completionIdeal 1 :=
  ⟨_, B.toCompletion_single_tangentPrincipalExponent_mem ℓ hrank hχ i⟩

/-- The tangent principal monomial is the completion of `z^{r(eᵢ)}`. -/
@[simp]
theorem coe_tangentPrincipalMonomial (i : B.unfrozenIndex) :
    (B.tangentPrincipalMonomial ℓ hrank hχ (R := R) i : (G i).completion) =
      (G i).toCompletion (single (B.tangentPrincipalExponent ℓ hrank hχ i) 1) := (rfl)

/-- The tangent wall function of the line at `i` is `1 + ∑_{s<ℓᵢ} aᵢₛ z^{(s+1) r(eᵢ)}`. -/
theorem tangentInitialFunction_toRankTwoPolynomialInput (i : B.unfrozenIndex) :
    (I).tangentInitialFunction (B.rankTwoCoefficient ℓ hrank hχ a) i =
      1 + ∑ s : Fin (ℓ i),
        single ((s.val + 1) • B.tangentPrincipalExponent ℓ hrank hχ i) (a i s) := by
  rw [RankTwoPolynomialInput.tangentInitialFunction_def]
  congr 1
  refine (Fintype.sum_bijective
    (fun s => ⟨_, B.nsmul_principalEmbedding_mem_exponents ℓ hrank hχ i s⟩) ⟨fun s t hst => ?_,
      fun n => ?_⟩ _ _ fun s => ?_).symm
  · have hst' := B.nsmul_principalEmbedding_injective i (congrArg Subtype.val hst)
    exact Fin.ext (by simpa using hst')
  · have hn : (n : Lpr) ∈ B.principalExponents ℓ i := by
      rw [← B.toRankTwoPolynomialInput_exponents ℓ hrank hχ]
      exact n.property
    obtain ⟨s, hs⟩ := (B.mem_principalExponents ℓ).mp hn
    exact ⟨s, Subtype.ext hs⟩
  · rw [rankTwoCoefficient_mk_nsmul_principalEmbedding]
    exact congrArg (fun q => single q (a i s)) (Subtype.ext (by simp))

/-- The adapted polynomial wall function `fᵢ` evaluated at the completed monomial `z^{r(eᵢ)}` is
the completed wall function `1 + ∑_{s<ℓᵢ} aᵢₛ z^{(s+1) r(eᵢ)}` of the line at `i`. -/
theorem completedAeval_polynomialWallFunction (i : B.unfrozenIndex) :
    (G i).completedAeval (B.tangentPrincipalMonomial ℓ hrank hχ i)
        (B.polynomialWallFunction ℓ a i) =
      (G i).toCompletion ((I).tangentInitialFunction (B.rankTwoCoefficient ℓ hrank hχ a) i) :=
  (B.completedAeval_polynomialWallFunction_of_val_eq_toCompletion_single ℓ a
    (B.coe_tangentPrincipalMonomial ℓ hrank hχ i) i).trans
    (congrArg (G i).toCompletion (B.tangentInitialFunction_toRankTwoPolynomialInput ℓ hrank hχ a
      i).symm)

variable [Algebra ℚ R] [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

/-- The unsplit label of the line at `i` of the rank-two input is the image of the adapted
polynomial label at `i` under the fixed-degree principal realization. -/
theorem initialLabel_toRankTwoPolynomialInput (i : B.unfrozenIndex) :
    (I).initialLabel (B.rankTwoCoefficient ℓ hrank hχ a) i =
      (D.principalGraphGradedLieHom 𝒅).completedMap (B.polynomialWallLabel ℓ a i) := by
  refine (RankTwoPolynomialInput.initialLabel_def _ _ i).trans (Eq.trans ?_
    (B.principalGraphGradedLieHom_completedMap_polynomialWallLabel ℓ a i
      (by rw [wallNormal_toRankTwoPolynomialInput]) (B.tangentPrincipalExponent ℓ hrank hχ i)
      (B.coe_tangentPrincipalExponent ℓ hrank hχ i) (B.tangentPrincipalMonomial ℓ hrank hχ i)
      (B.coe_tangentPrincipalMonomial ℓ hrank hχ i)).symm)
  exact congrArg (fun x => (e).completedBCHExp _ (completedTropicalTangentField e ρ (χ i)
    ((G i).completedLog x)))
    (Subtype.ext (B.completedAeval_polynomialWallFunction ℓ hrank hχ a i)).symm

section Diagram

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : Module.Dual ℤ D.sublattice × D.unfrozen →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

local notation "f" => D.principalGraphGradedLieHom (R := R) 𝒅
local notation "hf" => fun _ _ _ => D.principalGraphGradedLieHom_mem_wall (R := R) 𝒅

/-- The tropical vertex image of the adapted polynomial input is equivalent to the incoming
diagram of the rank-two input: the incoming diagram is the ray presentation of the image labels,
which lie on the principal rays of the `r(eᵢ)`, so it only adds identity ray walls. -/
theorem equivalent_map_adaptedPolynomialInput :
    ((B.adaptedPolynomialInput ℓ a h).map f hf).Equivalent
      ((I).incomingDiagram h (B.rankTwoCoefficient ℓ hrank hχ a)) := by
  let := h.free
  let : HasUniqueDiv Lpr := .of_isTorsionFree ℤ _
  refine ((I).isRayFactorPresentation_incomingDiagram h _).equivalent (fun j => ?_) (fun j => ?_)
    (fun j => ?_)
  · ext x
    simp
  · simp
  · exact ((congrArg DirectedWall.label (DirectedDiagram.map_wall _ _ _ j)).trans
      ((DirectedWall.map_label ..).trans
        (congrArg (f).completedMap (B.adaptedPolynomialInput_label ℓ a h j)))).trans
      (B.initialLabel_toRankTwoPolynomialInput ℓ hrank hχ a j).symm

end Diagram

end General

section Universe

variable {N ι : Type u} [AddCommGroup N] [Module.Free ℤ N] {D : SkewLatticeDatum N}
  (B : D.AdaptedBasis ι) [Finite ι] (ℓ : B.unfrozenIndex → ℕ) (hrank : Nat.card ι = 2)
  (hχ : ∀ i : B.unfrozenIndex, D.principalCharacter (B.unfrozenBasis i) ≠ 0)
  {R V : Type*} [CommRing R] [Algebra ℚ R] (a : ∀ i, Fin (ℓ i) → R)
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  [Module.Free ℤ (Module.Dual ℤ D.sublattice × D.unfrozen)]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : Module.Dual ℤ D.sublattice × D.unfrozen →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

local notation "𝒅" => B.unfrozenBasis.positiveDegrees

/-- **Adapted polynomial inputs of rank two as rank-two polynomial inputs.** The fixed-degree
principal realization sends the outgoing scattering class of the adapted polynomial input to the
outgoing scattering class of the incoming diagram of the rank-two input. The lattice and the
index type of the adapted basis lie in one universe, the universe of the scattering classes. -/
theorem map_scat_adaptedPolynomialInput :
    DirectedDiagram.Class.map (D.principalGraphGradedLieHom 𝒅)
        (fun _ _ _ => D.principalGraphGradedLieHom_mem_wall 𝒅)
        ((B.adaptedPolynomialInput ℓ a h).Scat (B.adaptedPolynomialInput_full ℓ a h)) =
      ((B.toRankTwoPolynomialInput ℓ hrank hχ).incomingDiagram h
        (B.rankTwoCoefficient ℓ hrank hχ a)).Scat
        ((B.toRankTwoPolynomialInput ℓ hrank hχ).incomingDiagram_full h _) :=
  (DirectedDiagram.map_scat _ _ _ _).trans (DirectedDiagram.scat_eq_of_equivalent _ _
    (B.equivalent_map_adaptedPolynomialInput ℓ hrank hχ a h))

end Universe

end Mei.SkewLatticeDatum.AdaptedBasis
