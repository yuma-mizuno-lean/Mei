/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Data.ZMod.Basic

/-!
# Rank-two skew lattice data

On `N = ℤ × ℤ` take the skew form with `{e₁, e₂} = 1`, every vector unfrozen, and the
sublattice `N° = ℤ e₁ ⊕ 2ℤ e₂` of the multipliers `d = (1, 2)`. Both integrality conditions
hold, the standard basis with multipliers `(1, 2)` is an adapted basis, the ray indices of `N°`
are `κ(e₁) = 1` and `κ(e₂) = 2`, and the integral functional `{-, κ(e₂) e₂}` is `a ↦ 2 a₁`.

The unimodular variant takes `N° = N`. Its standard basis provides a universal pair with
skew pairing one for transporting rank-two identities.

On the datum with `d = (1, 2)`, the multiplicities `ℓ = (1, 2)` give a polynomial input of a
generalized cluster scattering diagram in the sense of Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, Definition 8.2, with primitive exponents
`w₁ = e₂*` and `w₂ = -e₁*`. With `ℓ₂ = 1` the exponent at the second index would be the
imprimitive vector `-2 e₁*`.
-/

public section

namespace Mei.SkewLatticeDatum.Examples

/-- The skew form `{x, y} = x₁ y₂ - x₂ y₁` on `ℤ × ℤ`, with rational values. -/
def rankTwoForm : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => ((x.1 * y.2 - x.2 * y.1 : ℤ) : ℚ))
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

@[simp]
theorem rankTwoForm_apply (x y : ℤ × ℤ) :
    rankTwoForm x y = ((x.1 * y.2 - x.2 * y.1 : ℤ) : ℚ) :=
  (rfl)

/-- The unimodular rank-two skew lattice datum with `{e₁, e₂} = 1`, all vectors unfrozen,
and `N° = N = ℤ × ℤ`. -/
def unimodularRankTwo : SkewLatticeDatum (ℤ × ℤ) where
  unfrozen := ⊤
  unfrozen_saturated _ _ _ := Or.inr Submodule.mem_top
  sublattice := ⊤
  finiteIndex_sublattice := by
    simpa only [Submodule.top_toAddSubgroup] using
      (inferInstance : (⊤ : AddSubgroup (ℤ × ℤ)).FiniteIndex)
  form := rankTwoForm
  isAlt_form x := by simp [mul_comm]
  integral_unfrozen_sublattice a _ b _ := ⟨_, rankTwoForm_apply a b⟩
  integral_unfrozen_inf_sublattice a b _ := ⟨_, rankTwoForm_apply a b⟩

@[simp]
theorem unimodularRankTwo_unfrozen : unimodularRankTwo.unfrozen = ⊤ :=
  (rfl)

@[simp]
theorem unimodularRankTwo_sublattice : unimodularRankTwo.sublattice = ⊤ :=
  (rfl)

@[simp]
theorem unimodularRankTwo_form : unimodularRankTwo.form = rankTwoForm :=
  (rfl)

/-- The sublattice `ℤ e₁ ⊕ 2ℤ e₂` of vectors with even second coordinate, the kernel of the
parity of the second coordinate. -/
def evenSnd : Submodule ℤ (ℤ × ℤ) :=
  ((Int.castAddHom (ZMod 2)).comp (AddMonoidHom.snd ℤ ℤ)).ker.toIntSubmodule

@[simp]
theorem mem_evenSnd {x : ℤ × ℤ} : x ∈ evenSnd ↔ (2 : ℤ) ∣ x.2 := by
  rw [evenSnd, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe,
    AddMonoidHom.mem_ker]
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The rank-two skew lattice datum with `{e₁, e₂} = 1`, all vectors unfrozen and
`N° = ℤ e₁ ⊕ 2ℤ e₂`. -/
def rankTwo : SkewLatticeDatum (ℤ × ℤ) where
  unfrozen := ⊤
  unfrozen_saturated _ _ _ := Or.inr Submodule.mem_top
  sublattice := evenSnd
  finiteIndex_sublattice := AddSubgroup.finiteIndex_ker _
  form := rankTwoForm
  isAlt_form x := by simp [mul_comm]
  integral_unfrozen_sublattice a _ b _ := ⟨_, rankTwoForm_apply a b⟩
  integral_unfrozen_inf_sublattice a b _ := ⟨_, rankTwoForm_apply a b⟩

@[simp]
theorem rankTwo_unfrozen : rankTwo.unfrozen = ⊤ :=
  (rfl)

@[simp]
theorem rankTwo_sublattice : rankTwo.sublattice = evenSnd :=
  (rfl)

@[simp]
theorem rankTwo_form : rankTwo.form = rankTwoForm :=
  (rfl)

/-- The standard basis of `ℤ × ℤ`, with both indices unfrozen and multipliers `(1, 2)`, is an
adapted basis of the rank-two datum. -/
noncomputable def rankTwoAdaptedBasis : rankTwo.AdaptedBasis (Fin 2) where
  basis := Module.Basis.finTwoProd ℤ
  unfrozenIndex := Finset.univ
  multiplier := ![1, 2]
  multiplier_pos i := by fin_cases i <;> simp
  unfrozen_eq_span := by
    rw [Finset.coe_univ, Set.image_univ, Module.Basis.span_eq, rankTwo_unfrozen]
  sublattice_eq_span := by
    ext x
    rw [Submodule.mem_span_range_iff_exists_fun, rankTwo_sublattice, mem_evenSnd]
    simp only [Fin.sum_univ_two, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨![x.1, k], Prod.ext ?_ ?_⟩ <;> simp [hk, mul_comm]
    · rintro ⟨c, rfl⟩
      simp

@[simp]
theorem rankTwoAdaptedBasis_basis : rankTwoAdaptedBasis.basis = Module.Basis.finTwoProd ℤ :=
  (rfl)

@[simp]
theorem rankTwoAdaptedBasis_multiplier : rankTwoAdaptedBasis.multiplier = ![1, 2] :=
  (rfl)

/-- The ray index of `e₁` is `1`, since `e₁ ∈ N°`. -/
theorem rayIndex_fst : rankTwo.sublattice.toAddSubgroup.rayIndex (1, 0) = 1 := by
  simpa using rankTwoAdaptedBasis.rayIndex_basis 0

/-- The ray index of `e₂` is `2`, since `e₂ ∉ N°` and `2 e₂ ∈ N°`. -/
theorem rayIndex_snd : rankTwo.sublattice.toAddSubgroup.rayIndex (0, 1) = 2 := by
  simpa using rankTwoAdaptedBasis.rayIndex_basis 1

/-- The integral functional `{-, κ(e₂) e₂}` sends `a` to `2 a₁`. -/
theorem normal_snd_apply (a : ℤ × ℤ) :
    rankTwo.normal (0, 1) (by simp) a = 2 * a.1 := by
  apply Int.cast_injective (α := ℚ)
  rw [cast_normal_apply, rayIndex_snd]
  simp

/-- The polynomial input on the rank-two datum with `{e₁, e₂} = 1` and multipliers `d = (1, 2)`
with multiplicities `ℓ = (1, 2)`. Its exponents are `w₁ = d₁ {e₁, -} / ℓ₁ = e₂*` and
`w₂ = d₂ {e₂, -} / ℓ₂ = -e₁*`, so its initial functions are `1 + p_{1,1} z^{e₂*}` and
`1 + p_{2,1} z^{-e₁*} + p_{2,2} z^{-2e₁*}`. -/
noncomputable def rankTwoBLMPolynomialInput : rankTwoAdaptedBasis.BLMPolynomialInput where
  multiplicity i := ![1, 2] i.1
  multiplicity_pos i := by
    obtain ⟨i, -⟩ := i
    fin_cases i <;> simp
  exponent i := ![LinearMap.snd ℤ ℤ ℤ, -LinearMap.fst ℤ ℤ ℤ] i.1
  multiplicity_mul_exponent i a := by
    obtain ⟨i, -⟩ := i
    fin_cases i <;> simp
  isPrimitive_exponent i := by
    obtain ⟨i, -⟩ := i
    fin_cases i
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.applyₗ (0, 1), by simp⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.applyₗ (-1, 0), by simp⟩
  eq_one_of_dvd_multiplier k hk := by
    simpa using hk 0
  eq_zero_of_form_eq_zero v _ hv := by
    have h₁ := hv (1, 0)
    have h₂ := hv (0, 1)
    simp only [rankTwo_form, rankTwoForm_apply, Int.cast_eq_zero] at h₁ h₂
    ext <;> simp_all

@[simp]
theorem rankTwoBLMPolynomialInput_multiplicity (i : rankTwoAdaptedBasis.unfrozenIndex) :
    rankTwoBLMPolynomialInput.multiplicity i = ![1, 2] i.1 :=
  (rfl)

@[simp]
theorem rankTwoBLMPolynomialInput_exponent (i : rankTwoAdaptedBasis.unfrozenIndex) :
    rankTwoBLMPolynomialInput.exponent i = ![LinearMap.snd ℤ ℤ ℤ, -LinearMap.fst ℤ ℤ ℤ] i.1 :=
  (rfl)

end Mei.SkewLatticeDatum.Examples
