/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# A rank-two skew lattice datum

On `N = ℤ × ℤ` take the skew form with `{e₁, e₂} = 1`, every vector unfrozen, and the
sublattice `N° = ℤ e₁ ⊕ 2ℤ e₂` of the multipliers `d = (1, 2)`. Both integrality conditions
hold, the ray indices of `N°` are `κ(e₁) = 1` and `κ(e₂) = 2`, and the integral functional
`{-, κ(e₂) e₂}` is `a ↦ 2 a₁`.
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

/-- The ray index of `e₁` is `1`, since `e₁ ∈ N°`. -/
theorem rayIndex_fst : rankTwo.sublattice.toAddSubgroup.rayIndex (1, 0) = 1 := by
  rw [AddSubgroup.rayIndex_of_isPrimitive _
      (TauCeti.isPrimitive_def.2 ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩),
    Nat.cast_eq_one, AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff]
  simp

/-- The ray index of `e₂` is `2`, since `e₂ ∉ N°` and `2 e₂ ∈ N°`. -/
theorem rayIndex_snd : rankTwo.sublattice.toAddSubgroup.rayIndex (0, 1) = 2 := by
  rw [AddSubgroup.rayIndex_of_isPrimitive _
    (TauCeti.isPrimitive_def.2 ⟨LinearMap.snd ℤ ℤ ℤ, rfl⟩)]
  have : addOrderOf (((0, 1) : ℤ × ℤ) : (ℤ × ℤ) ⧸ rankTwo.sublattice.toAddSubgroup) = 2 := by
    apply addOrderOf_eq_prime
    · rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      simp
    · rw [Ne, QuotientAddGroup.eq_zero_iff]
      simp
  rw [this, Nat.cast_ofNat]

/-- The integral functional `{-, κ(e₂) e₂}` sends `a` to `2 a₁`. -/
theorem normal_snd_apply (a : ℤ × ℤ) :
    rankTwo.normal (0, 1) (by simp) a = 2 * a.1 := by
  apply Int.cast_injective (α := ℚ)
  rw [cast_normal_apply, rayIndex_snd]
  simp

end Mei.SkewLatticeDatum.Examples
