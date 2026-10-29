/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.AdaptedBasis
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Data.ZMod.Basic

/-!
# A rank-two skew lattice datum

On `N = ℤ × ℤ` take the skew form with `{e₁, e₂} = 1`, every vector unfrozen, and the
sublattice `N° = ℤ e₁ ⊕ 2ℤ e₂` of the multipliers `d = (1, 2)`. Both integrality conditions
hold, the standard basis with multipliers `(1, 2)` is an adapted basis, the ray indices of `N°`
are `κ(e₁) = 1` and `κ(e₂) = 2`, and the integral functional `{-, κ(e₂) e₂}` is `a ↦ 2 a₁`.
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

end Mei.SkewLatticeDatum.Examples
