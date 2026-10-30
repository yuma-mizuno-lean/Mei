/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.Principal
public import Mei.Algebra.PositiveDegrees.Basis
public import Mathlib.Data.Nat.Cast.Field

/-!
# The principal datum of a BLM polynomial input

Let `I` be a polynomial input in the sense of Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams* (arXiv:2503.03719v1, §8.1), on a skew lattice datum
`(N, N_uf, N°, {,})` with adapted basis `(e_j)_{j ∈ ι}`, multipliers `d_j`, multiplicities `ℓ_i`
and exponents `w_i ∈ M = Hom(N, ℤ)`, `ℓ_i w_i = d_i {e_i, -}`. Its scattering diagram lives in
`M_ℝ`, while the principal realization of a skew lattice datum (Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2) lives on
`M° ⊕ N_uf` with `M° = Hom(N°, ℤ)`. This file constructs a skew lattice datum whose
finite-index sublattice is identified with `N`, so that its character lattice `M°` is `M`, and
whose principal characters at the unfrozen basis vectors are the `w_i`.

With `Λ = ∏_{i ∈ I_uf} d_i`, put `d'_i = Λ ℓ_i / d_i` at unfrozen indices and `d'_j = 1` at frozen
ones. The new datum lives on `N' = ℤ^ι` with basis `ε_j`, unfrozen indices `I_uf`, multipliers
`d'_j` and the form determined by `{ε_j, ε_k}' = Λ {e_j, e_k} / (d'_j d'_k)`. The map
`N → N'°`, `e_j ↦ d'_j ε_j`, is an isomorphism (`principalSublatticeEquiv`), so `ε_j` is the
positive rational multiple `e_j / d'_j` of `e_j`. Under it:

* the new form restricts to `Λ {,}`, a positive multiple of BLM's `-ω_B = {,}`
  (`principalDatum_form_principalSublatticeEquiv`);
* the principal character `p₁*(ε_i) = {ε_i, -}'|_{N'°}` of an unfrozen basis vector is the
  exponent `w_i` (`dualMap_principalSublatticeEquiv_principalCharacter`).

The variables `p_{i,s}` of the input are the letters `v_{i,s} = (s w_i, e_{(i,s)})` of the finite
alphabet lattice `M × ℤ^E` (`Mei.PositiveDegrees.finiteAlphabet`). The lift
`T(m, b) = (m, ∑_{i,s} s b_{i,s} ε_i)` to the principal lattice `M'° × N'_uf` sends `v_{i,s}` to
`s r(ε_i)`, where `r(ε_i) = (p₁*(ε_i), ε_i)` is the principal exponent
(`principalLift_letter`). With the coordinate-sum degree `δ_pr` of the basis `(ε_i)` of `N'_uf`,
`T` is a positive degree map with identity cutoff modulus from the alphabet degrees `(P_E, δ_E)`
to the principal degrees (`principalFiniteAlphabetLift`), and `δ_E ≤ δ_pr ∘ T ≤ c δ_E` on `P_E`
whenever every `ℓ_i ≤ c` (`degree_principalLift_le`). This is the lattice part of the comparison
of BLM's diagram of the input with the principal realization in Burcroff–Lee–Mou, §8.1 and §9.2,
where `p_{i,s} z^{s w_i}` corresponds to `a_{i,s} t_i^s z^{s w_i}`.

## Main declarations

* `BLMPolynomialInput.principalMultiplier`: the multipliers `d'_j`.
* `BLMPolynomialInput.principalForm`: the rescaled form on `ℤ^ι`.
* `BLMPolynomialInput.principalDatum`, `BLMPolynomialInput.principalBasis`: the datum and its
  adapted basis `(ε_j)`.
* `BLMPolynomialInput.principalSublatticeEquiv`: the isomorphism `N ≃ N'°`.
* `BLMPolynomialInput.dualMap_principalSublatticeEquiv_principalCharacter`: `p₁*(ε_i) = w_i`
  in `M'° ≃ M`.
* `BLMPolynomialInput.principalLift`, `BLMPolynomialInput.principalFiniteAlphabetLift`: the lift
  `T` and its positive degree map.
* `BLMPolynomialInput.degree_principalLift_le`: `δ_pr ∘ T ≤ c δ_E` on `P_E`.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open Module

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput)

local notation "Λ" => ∏ i ∈ B.unfrozenIndex, B.multiplier i

section Multiplier

variable [DecidableEq ι]

/-- The multipliers `d'_j` of the principal datum: `Λ ℓ_j / d_j` at an unfrozen index and `1` at
a frozen one, where `Λ = ∏_{i ∈ I_uf} d_i`. -/
def principalMultiplier (j : ι) : ℕ :=
  if h : j ∈ B.unfrozenIndex then Λ / B.multiplier j * I.multiplicity ⟨j, h⟩ else 1

theorem principalMultiplier_pos (j : ι) : 0 < I.principalMultiplier j := by
  unfold principalMultiplier
  split_ifs with h
  · have hΛ : 0 < Λ :=
      Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (B.multiplier_pos i).ne')
    exact Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hΛ (Finset.dvd_prod_of_mem _ h))
      (B.multiplier_pos j)) (I.multiplicity_pos _)
  · exact one_pos

/-- At an unfrozen index, `d'_i = Λ ℓ_i / d_i`. -/
theorem cast_principalMultiplier (i : B.unfrozenIndex) :
    (I.principalMultiplier i : ℚ) = ((Λ : ℕ) : ℚ) * I.multiplicity i / B.multiplier i := by
  have hd : (B.multiplier i : ℚ) ≠ 0 := by exact_mod_cast (B.multiplier_pos i).ne'
  simp only [principalMultiplier, i.2, ↓reduceDIte, Nat.cast_mul,
    Nat.cast_div (Finset.dvd_prod_of_mem _ i.2) hd]
  ring

/-- At a frozen index, `d'_j = 1`. -/
theorem principalMultiplier_of_notMem {j : ι} (hj : j ∉ B.unfrozenIndex) :
    I.principalMultiplier j = 1 := by
  simp [principalMultiplier, hj]

/-- The map `N → ℤ^ι`, `e_j ↦ d'_j ε_j`, onto the finite-index sublattice of the principal
datum. -/
def principalInclusion : N →ₗ[ℤ] ι →₀ ℤ :=
  B.basis.constr ℤ fun j => I.principalMultiplier j • Finsupp.single j 1

@[simp]
theorem principalInclusion_basis (j : ι) :
    I.principalInclusion (B.basis j) = I.principalMultiplier j • Finsupp.single j 1 := by
  simp [principalInclusion]

end Multiplier

section Form

variable [DecidableEq ι] [Fintype ι]

/-- The product of all principal multipliers `d'_j`. -/
private def multiplierProd : ℕ :=
  ∏ j, I.principalMultiplier j

private theorem multiplierProd_ne_zero : (I.multiplierProd : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => (I.principalMultiplier_pos j).ne')

private theorem principalMultiplier_dvd_multiplierProd (j : ι) :
    I.principalMultiplier j ∣ I.multiplierProd :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

/-- The map `ℤ^ι → N`, `ε_j ↦ (∏_k d'_k / d'_j) e_j`: the integral multiple of the inverse of
`principalInclusion` used to transport the form. -/
private def principalScaling : (ι →₀ ℤ) →ₗ[ℤ] N :=
  Finsupp.linearCombination ℤ fun j => (I.multiplierProd / I.principalMultiplier j) • B.basis j

private theorem principalScaling_single (j : ι) :
    I.principalScaling (Finsupp.single j 1) =
      (I.multiplierProd / I.principalMultiplier j) • B.basis j := by
  simp [principalScaling]

private theorem principalScaling_principalInclusion (a : N) :
    I.principalScaling (I.principalInclusion a) = I.multiplierProd • a := by
  have h : I.principalScaling ∘ₗ I.principalInclusion = I.multiplierProd • LinearMap.id :=
    B.basis.ext fun j => by
      rw [LinearMap.comp_apply, principalInclusion_basis, map_nsmul, principalScaling_single,
        smul_smul, Nat.mul_div_cancel' (I.principalMultiplier_dvd_multiplierProd j),
        LinearMap.smul_apply, LinearMap.id_apply]
  exact LinearMap.congr_fun h a

/-- The skew form of the principal datum on `ℤ^ι`, determined by
`{ε_j, ε_k}' = Λ {e_j, e_k} / (d'_j d'_k)` (`principalForm_single_single`). -/
def principalForm : (ι →₀ ℤ) →ₗ[ℤ] (ι →₀ ℤ) →ₗ[ℤ] ℚ :=
  (((Λ : ℕ) : ℚ) / (I.multiplierProd : ℚ) ^ 2) •
    D.form.compl₁₂ I.principalScaling I.principalScaling

private theorem principalForm_apply (x y : ι →₀ ℤ) :
    I.principalForm x y = ((Λ : ℕ) : ℚ) / (I.multiplierProd : ℚ) ^ 2 *
      D.form (I.principalScaling x) (I.principalScaling y) := by
  simp [principalForm]

theorem isAlt_principalForm : I.principalForm.IsAlt := fun x => by
  simp [principalForm_apply]

private theorem cast_multiplierProd_div (j : ι) :
    ((I.multiplierProd / I.principalMultiplier j : ℕ) : ℚ) =
      I.multiplierProd / I.principalMultiplier j :=
  Nat.cast_div (I.principalMultiplier_dvd_multiplierProd j)
    (Nat.cast_ne_zero.mpr (I.principalMultiplier_pos j).ne')

/-- The principal form on basis vectors: `{ε_j, ε_k}' = Λ {e_j, e_k} / (d'_j d'_k)`. -/
theorem principalForm_single_single (j k : ι) :
    I.principalForm (Finsupp.single j 1) (Finsupp.single k 1) =
      ((Λ : ℕ) : ℚ) * D.form (B.basis j) (B.basis k) /
        (I.principalMultiplier j * I.principalMultiplier k) := by
  have hj : (I.principalMultiplier j : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (I.principalMultiplier_pos j).ne'
  have hk : (I.principalMultiplier k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (I.principalMultiplier_pos k).ne'
  have hP := I.multiplierProd_ne_zero
  simp only [principalForm_apply, principalScaling_single, map_nsmul, LinearMap.smul_apply,
    nsmul_eq_mul, cast_multiplierProd_div]
  field_simp

/-- On the image of `N`, the principal form is `Λ {,}`. -/
@[simp]
theorem principalForm_principalInclusion (a b : N) :
    I.principalForm (I.principalInclusion a) (I.principalInclusion b) =
      ((Λ : ℕ) : ℚ) * D.form a b := by
  have hP := I.multiplierProd_ne_zero
  simp only [principalForm_apply, principalScaling_principalInclusion, map_nsmul,
    LinearMap.smul_apply, nsmul_eq_mul]
  field_simp

/-- The principal form pairs `ε_j` with the image of `a ∈ N` by `Λ {e_j, a} / d'_j`. -/
theorem principalForm_single_principalInclusion (j : ι) (a : N) :
    I.principalForm (Finsupp.single j 1) (I.principalInclusion a) =
      ((Λ : ℕ) : ℚ) * D.form (B.basis j) a / I.principalMultiplier j := by
  have hj : (I.principalMultiplier j : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (I.principalMultiplier_pos j).ne'
  have hP := I.multiplierProd_ne_zero
  simp only [principalForm_apply, principalScaling_single, principalScaling_principalInclusion,
    map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, cast_multiplierProd_div]
  field_simp

/-- At an unfrozen index the principal form pairs `ε_i` with the image of `a ∈ N` by the
exponent `w_i(a)`. -/
theorem principalForm_single_principalInclusion_of_mem (i : B.unfrozenIndex) (a : N) :
    I.principalForm (Finsupp.single i 1) (I.principalInclusion a) = I.exponent i a := by
  have hd : (B.multiplier i : ℚ) ≠ 0 := by exact_mod_cast (B.multiplier_pos i).ne'
  have hℓ : (I.multiplicity i : ℚ) ≠ 0 := by exact_mod_cast (I.multiplicity_pos i).ne'
  have hΛ : ((Λ : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (B.multiplier_pos i).ne')
  rw [principalForm_single_principalInclusion, cast_principalMultiplier, cast_exponent_apply]
  field_simp

/-- At a frozen index the principal form pairs `ε_j` with `d'_i ε_i`, `i ∈ I_uf`, by the
integer `-d'_i w_i(e_j)`. -/
private theorem principalForm_single_principalInclusion_basis_of_notMem {j : ι}
    (hj : j ∉ B.unfrozenIndex) (i : B.unfrozenIndex) :
    I.principalForm (Finsupp.single j 1) (I.principalInclusion (B.basis i)) =
      -((I.principalMultiplier i : ℤ) * I.exponent i (B.basis j) : ℤ) := by
  have hd : (B.multiplier i : ℚ) ≠ 0 := by exact_mod_cast (B.multiplier_pos i).ne'
  have hℓ : (I.multiplicity i : ℚ) ≠ 0 := by exact_mod_cast (I.multiplicity_pos i).ne'
  rw [principalForm_single_principalInclusion, I.principalMultiplier_of_notMem hj, D.form_swap]
  push_cast
  rw [cast_principalMultiplier, cast_exponent_apply]
  field_simp
  push_cast
  ring

/-- The principal datum of a BLM polynomial input on `ℤ^ι`: unfrozen sublattice spanned by the
`ε_i`, `i ∈ I_uf`, finite-index sublattice spanned by the `d'_j ε_j` (the image of `N`), and the
form `principalForm`. -/
def principalDatum : SkewLatticeDatum (ι →₀ ℤ) :=
  SkewLatticeDatum.ofBasis Finsupp.basisSingleOne B.unfrozenIndex I.principalMultiplier
    I.principalForm I.principalMultiplier_pos I.isAlt_principalForm
    (fun i hi j => ⟨I.exponent ⟨i, hi⟩ (B.basis j), by
      rw [Finsupp.coe_basisSingleOne, ← I.principalInclusion_basis]
      exact I.principalForm_single_principalInclusion_of_mem ⟨i, hi⟩ _⟩)
    (fun i hi j => by
      rw [Finsupp.coe_basisSingleOne, ← I.principalInclusion_basis]
      by_cases hj : j ∈ B.unfrozenIndex
      · exact ⟨I.exponent ⟨j, hj⟩ (B.basis i),
          I.principalForm_single_principalInclusion_of_mem ⟨j, hj⟩ _⟩
      · exact ⟨_, I.principalForm_single_principalInclusion_basis_of_notMem hj ⟨i, hi⟩⟩)

@[simp]
theorem principalDatum_form : I.principalDatum.form = I.principalForm := by
  simp [principalDatum]

/-- The adapted basis `(ε_j)` of the principal datum, with the unfrozen indices of the input and
multipliers `d'_j`. -/
def principalBasis : I.principalDatum.AdaptedBasis ι :=
  AdaptedBasis.ofBasis _ _ _ _ _ _ _ _

@[simp]
theorem principalBasis_basis : I.principalBasis.basis = Finsupp.basisSingleOne := by
  simp [principalBasis]

@[simp]
theorem principalBasis_unfrozenIndex : I.principalBasis.unfrozenIndex = B.unfrozenIndex := by
  simp [principalBasis]

@[simp]
theorem principalBasis_multiplier : I.principalBasis.multiplier = I.principalMultiplier := by
  simp [principalBasis]

/-- The unfrozen basis vector `ε_i` of the principal datum. -/
theorem single_mem_principalDatum_unfrozen (i : B.unfrozenIndex) :
    Finsupp.single (i : ι) 1 ∈ I.principalDatum.unfrozen := by
  simpa using I.principalBasis.basis_mem_unfrozen ⟨i, by simp⟩

/-- The identification of `N` with the finite-index sublattice `N'°` of the principal datum,
`e_j ↦ d'_j ε_j`. -/
def principalSublatticeEquiv : N ≃ₗ[ℤ] I.principalDatum.sublattice :=
  B.basis.equiv I.principalBasis.sublatticeBasis (Equiv.refl ι)

@[simp]
theorem coe_principalSublatticeEquiv (a : N) :
    (I.principalSublatticeEquiv a : ι →₀ ℤ) = I.principalInclusion a := by
  have h : I.principalDatum.sublattice.subtype ∘ₗ I.principalSublatticeEquiv.toLinearMap =
      I.principalInclusion :=
    B.basis.ext fun j => by
      simp [principalSublatticeEquiv, Basis.equiv_apply, coe_sublatticeBasis]
  exact LinearMap.congr_fun h a

/-- The basis vector `e_j` corresponds to `d'_j ε_j`: the basis `(ε_j)` consists of the positive
rational multiples `e_j / d'_j`. -/
theorem principalSublatticeEquiv_basis (j : ι) :
    I.principalSublatticeEquiv (B.basis j) = I.principalBasis.sublatticeBasis j := by
  simp [principalSublatticeEquiv, Basis.equiv_apply]

/-- Under `N ≃ N'°`, the form of the principal datum is the positive multiple
`Λ {,}`, `Λ = ∏_{i ∈ I_uf} d_i`, of the original form, that is, of BLM's `-ω_B`. -/
theorem principalDatum_form_principalSublatticeEquiv (a b : N) :
    I.principalDatum.form (I.principalSublatticeEquiv a) (I.principalSublatticeEquiv b) =
      ((Λ : ℕ) : ℚ) * D.form a b := by
  simp

/-- The principal character `p₁*(ε_i)` of an unfrozen basis vector of the principal datum takes
the value `w_i(a)` on the image of `a ∈ N`. -/
@[simp]
theorem principalCharacter_principalSublatticeEquiv (i : B.unfrozenIndex) (a : N) :
    I.principalDatum.principalCharacter ⟨Finsupp.single (i : ι) 1,
        I.single_mem_principalDatum_unfrozen i⟩ (I.principalSublatticeEquiv a) =
      I.exponent i a := by
  apply Int.cast_injective (α := ℚ)
  simp [principalForm_single_principalInclusion_of_mem]

/-- Under `M'° = Hom(N'°, ℤ) ≃ Hom(N, ℤ) = M`, the principal character `p₁*(ε_i)` of an unfrozen
basis vector of the principal datum is the exponent `w_i` of the polynomial input. -/
theorem dualMap_principalSublatticeEquiv_principalCharacter (i : B.unfrozenIndex) :
    I.principalSublatticeEquiv.dualMap (I.principalDatum.principalCharacter
      ⟨Finsupp.single (i : ι) 1, I.single_mem_principalDatum_unfrozen i⟩) = I.exponent i :=
  LinearMap.ext fun a => by simp [LinearEquiv.dualMap_apply]

private theorem symm_dualMap_principalSublatticeEquiv_exponent (i : B.unfrozenIndex) :
    I.principalSublatticeEquiv.symm.dualMap (I.exponent i) =
      I.principalDatum.principalCharacter
        ⟨Finsupp.single (i : ι) 1, I.single_mem_principalDatum_unfrozen i⟩ := by
  rw [← LinearEquiv.dualMap_symm, LinearEquiv.symm_apply_eq,
    dualMap_principalSublatticeEquiv_principalCharacter]

/-- The unfrozen basis of the normalized principal datum consists of its standard
coordinate vectors. -/
@[simp]
theorem unfrozenBasis_principalBasis (i : B.unfrozenIndex) :
    I.principalBasis.unfrozenBasis ⟨i, by simp⟩ =
      ⟨Finsupp.single (i : ι) 1, I.single_mem_principalDatum_unfrozen i⟩ :=
  Subtype.ext (by simp [coe_unfrozenBasis])

section Lift

/-- The lift `T(m, b) = (m, ∑_{i,s} s b_{i,s} ε_i)` from the finite alphabet lattice `M × ℤ^E` of
the polynomial input, `E = {(i, s) | i ∈ I_uf, 1 ≤ s ≤ ℓ_i}`, to the principal lattice
`M'° × N'_uf` of its principal datum, where `M ≃ M'°` is dual to `principalSublatticeEquiv`. -/
def principalLift :
    Module.Dual ℤ N × (I.Letter → ℤ) →ₗ[ℤ]
      Module.Dual ℤ I.principalDatum.sublattice × I.principalDatum.unfrozen :=
  I.principalSublatticeEquiv.symm.dualMap.toLinearMap.prodMap
    (Fintype.linearCombination ℤ fun α : I.Letter =>
      ((α.2 : ℕ) + 1) • ⟨Finsupp.single (α.1 : ι) 1, I.single_mem_principalDatum_unfrozen α.1⟩)

/-- The lift in coordinates. -/
theorem principalLift_apply (x : Module.Dual ℤ N × (I.Letter → ℤ)) :
    I.principalLift x = (I.principalSublatticeEquiv.symm.dualMap x.1, ∑ α, x.2 α •
      ((α.2 : ℕ) + 1) • ⟨Finsupp.single (α.1 : ι) 1,
        I.single_mem_principalDatum_unfrozen α.1⟩) := by
  simp [principalLift, Fintype.linearCombination_apply]

/-- The lift sends the letter `v_{i,s} = (s w_i, e_{(i,s)})` of the variable `p_{i,s}` to `s`
times the principal exponent `r(ε_i) = (p₁*(ε_i), ε_i)`. -/
theorem principalLift_letter (α : I.Letter) :
    I.principalLift (PositiveDegrees.letter I.letterExponent α) =
      ((α.2 : ℕ) + 1) • I.principalDatum.principalEmbedding
        ⟨Finsupp.single (α.1 : ι) 1, I.single_mem_principalDatum_unfrozen α.1⟩ := by
  obtain ⟨i, s⟩ := α
  refine Prod.ext ?_ ?_
  · simp [principalLift, PositiveDegrees.letter_fst,
      symm_dualMap_principalSublatticeEquiv_exponent]
  · simp [principalLift, PositiveDegrees.letter_snd, Fintype.linearCombination_apply_single]

/-- The letter of `p_{i,s}` lifts to principal degree `s`, the coordinate sum in the basis
`(ε_i)` of `N'_uf`. -/
@[simp]
theorem degree_principalLift_letter (α : I.Letter) :
    (I.principalDatum.principalPositiveDegrees
        I.principalBasis.unfrozenBasis.positiveDegrees).degree
      (I.principalLift (PositiveDegrees.letter I.letterExponent α)) = (α.2 : ℕ) + 1 := by
  rw [principalLift_letter, map_nsmul, principalEmbedding_apply, PositiveDegrees.graph_degree,
    ← unfrozenBasis_principalBasis, Module.Basis.positiveDegrees_degree, Basis.repr_self]
  simp [Finsupp.single_apply]

/-- The lift of every letter is an allowed principal degree.
See `principalLift_letter_ne_zero` for nonzeroness. -/
@[simp]
theorem principalLift_letter_mem (α : I.Letter) :
    I.principalLift (PositiveDegrees.letter I.letterExponent α) ∈
      (I.principalDatum.principalPositiveDegrees
        I.principalBasis.unfrozenBasis.positiveDegrees).monoid := by
  rw [principalLift_letter]
  refine nsmul_mem ?_ _
  simp only [principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
  refine ⟨?_, rfl⟩
  rw [← unfrozenBasis_principalBasis, Module.Basis.mem_positiveDegrees_monoid, Basis.repr_self]
  exact fun j => by simp [Finsupp.single_apply, apply_ite]

/-- The lift of a letter is nonzero. -/
@[simp]
theorem principalLift_letter_ne_zero (α : I.Letter) :
    I.principalLift (PositiveDegrees.letter I.letterExponent α) ≠ 0 := fun h => by
  have hd := I.degree_principalLift_letter α
  rw [h, map_zero] at hd
  omega

/-- The principal lift as a positive degree map from the finite alphabet of the polynomial input
to the principal positive degrees of its principal datum, with identity cutoff modulus
(`PositiveDegrees.finiteAlphabetLift`). In particular the alphabet degree is at most the
principal degree of the lift (`PositiveDegrees.finiteAlphabet_degree_le`). -/
def principalFiniteAlphabetLift :
    PositiveDegreeMap (PositiveDegrees.finiteAlphabet I.letterExponent)
      (I.principalDatum.principalPositiveDegrees I.principalBasis.unfrozenBasis.positiveDegrees) :=
  PositiveDegrees.finiteAlphabetLift I.letterExponent (τ := I.principalLift.toAddMonoidHom)
    I.principalLift_letter_mem I.principalLift_letter_ne_zero

@[simp]
theorem principalFiniteAlphabetLift_apply (x : Module.Dual ℤ N × (I.Letter → ℤ)) :
    I.principalFiniteAlphabetLift x = I.principalLift x :=
  PositiveDegrees.finiteAlphabetLift_apply _ _ _ x

@[simp]
theorem principalFiniteAlphabetLift_modulus (k : ℕ) :
    I.principalFiniteAlphabetLift.modulus k = k :=
  PositiveDegrees.finiteAlphabetLift_modulus _ _ _ k

/-- If every multiplicity is at most `c`, the principal degree of the lift of an allowed
alphabet degree is at most `c` times its alphabet degree; with the lower bound
`PositiveDegrees.finiteAlphabet_degree_le`, `δ_E ≤ δ_pr ∘ T ≤ ℓ_max δ_E` on `P_E`. -/
theorem degree_principalLift_le {c : ℕ} (hc : ∀ i, I.multiplicity i ≤ c)
    {x : Module.Dual ℤ N × (I.Letter → ℤ)}
    (hx : x ∈ (PositiveDegrees.finiteAlphabet I.letterExponent).monoid) :
    (I.principalDatum.principalPositiveDegrees
        I.principalBasis.unfrozenBasis.positiveDegrees).degree (I.principalLift x) ≤
      c * (PositiveDegrees.finiteAlphabet I.letterExponent).degree x := by
  obtain ⟨hpos, hsum⟩ := (PositiveDegrees.mem_finiteAlphabet_monoid I.letterExponent).mp hx
  have h := PositiveDegrees.degree_map_eq_sum I.letterExponent
    (e := I.principalDatum.principalPositiveDegrees I.principalBasis.unfrozenBasis.positiveDegrees)
    (τ := I.principalLift.toAddMonoidHom) hsum
  simp only [LinearMap.toAddMonoidHom_coe, degree_principalLift_letter] at h
  rw [h, PositiveDegrees.finiteAlphabet_degree, Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  have hs : (α.2 : ℕ) + 1 ≤ c := (Nat.succ_le_of_lt α.2.2).trans (hc α.1)
  have hs' : ((α.2 : ℕ) + 1 : ℤ) ≤ c := by exact_mod_cast hs
  nlinarith [hpos α]

end Lift

end Form

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
