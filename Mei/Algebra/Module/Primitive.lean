/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Module.Primitive

/-!
# Uniqueness of primitive directions

Two primitive vectors in a torsion-free integer module with equal positive integer
multiples coincide. This gives uniqueness of primitive representatives of rational
rays without choosing a real realization of the lattice.

We use `TauCeti.IsPrimitive`, defined by an integer-valued functional taking value one.
-/

public section

namespace TauCeti.IsPrimitive

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Integer multiples of a primitive vector have distinct multipliers, even when
the ambient module has torsion. -/
theorem zsmul_left_injective {v : M} (hv : TauCeti.IsPrimitive v) :
    Function.Injective (fun a : ℤ => a • v) := by
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hv
  intro a b h
  have := congrArg f h
  simpa only [map_zsmul, hf, zsmul_eq_mul, mul_one, Int.cast_id] using this

/-- Primitive vectors with equal positive integer multiples are equal. -/
theorem eq_of_pos_zsmul_eq [HasUniqueDiv M] {v w : M} (hv : TauCeti.IsPrimitive v)
    (hw : TauCeti.IsPrimitive w) {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : a • v = b • w) : v = w := by
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hv
  obtain ⟨g, hg⟩ := TauCeti.isPrimitive_def.mp hw
  have hf' := congrArg f h
  have hg' := congrArg g h
  simp only [map_zsmul, hf, hg, zsmul_eq_mul, mul_one] at hf' hg'
  have hab : a = b := le_antisymm
    (Int.le_of_dvd hb ⟨g v, hg'.symm⟩) (Int.le_of_dvd ha ⟨f w, hf'⟩)
  exact zsmul_right_injective ha.ne' (hab ▸ h)

end TauCeti.IsPrimitive
