/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Integer characters with the same kernel

Nonzero integer-valued characters with the same kernel are rationally proportional:
some nonzero integer multiples agree. This detects proportional integral normals
without choosing a basis or extending scalars to a field.
-/

public section

namespace AddMonoidHom

variable {A : Type*} [AddGroup A]

/-- Nonzero integer characters with the same kernel have equal nonzero integer multiples. -/
theorem exists_ne_zero_zsmul_eq_of_ker_eq (f g : A →+ ℤ) (hf : f ≠ 0)
    (hker : f.ker = g.ker) :
    ∃ c e : ℤ, c ≠ 0 ∧ e ≠ 0 ∧ c • f = e • g := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  have hfa : f a ≠ 0 := ha
  have hga : g a ≠ 0 := by
    intro h
    have hm : a ∈ f.ker := by
      rw [hker]
      exact AddMonoidHom.mem_ker.mpr h
    exact hfa (AddMonoidHom.mem_ker.mp hm)
  refine ⟨g a, f a, hga, hfa, ?_⟩
  ext x
  have hx : f a • x - f x • a ∈ f.ker := by
    simp [AddMonoidHom.mem_ker, mul_comm]
  have hg := AddMonoidHom.mem_ker.mp (hker ▸ hx)
  have hg' : f a * g x = f x * g a := by
    simpa only [map_sub, map_zsmul, Int.zsmul_eq_mul, sub_eq_zero] using hg
  simpa only [AddMonoidHom.zsmul_apply, Int.zsmul_eq_mul, mul_comm] using hg'.symm

end AddMonoidHom
