/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Integer characters

Nonzero integer-valued characters with the same kernel are rationally proportional:
some nonzero integer multiples agree. This detects proportional integral normals
without choosing a basis or extending scalars to a field. Kernel containment
also gives proportionality when the second character can vanish. For two
characters, contracting against a vector outside their common kernel detects
every character annihilating both that kernel and the vector. Characters on a
product with two integer factors are determined by their coordinate restrictions.
-/

public section

namespace AddMonoidHom

/-- An integer character on a product with two integer factors is determined
by its restriction to the first factor and its values on the two coordinate vectors. -/
theorem apply_prod_int_int {Λ : Type*} [AddMonoid Λ]
    (m : (Λ × ℤ × ℤ) →+ ℤ) (v : Λ) (c l : ℤ) :
    m (v, c, l) = m (v, 0, 0) + c * m (0, 1, 0) + l * m (0, 0, 1) := by
  have hc := ((m.comp (AddMonoidHom.inr Λ (ℤ × ℤ))).comp
    (AddMonoidHom.inl ℤ ℤ)).map_zsmul c (1 : ℤ)
  have hl := ((m.comp (AddMonoidHom.inr Λ (ℤ × ℤ))).comp
    (AddMonoidHom.inr ℤ ℤ)).map_zsmul l (1 : ℤ)
  have hc' : m (0, c, 0) = c * m (0, 1, 0) := by simpa using hc
  have hl' : m (0, 0, l) = l * m (0, 0, 1) := by simpa using hl
  rw [← hc', ← hl', ← map_add, ← map_add]
  simp

variable {A : Type*} [AddGroup A]

/-- If the kernel of an integer character is contained in that of another,
then a nonzero integer multiple of the latter is a multiple of the former.
The second character is allowed to be zero. -/
theorem exists_ne_zero_zsmul_eq_of_ker_le (f g : A →+ ℤ) (hf : f ≠ 0)
    (hker : f.ker ≤ g.ker) :
    ∃ c d : ℤ, c ≠ 0 ∧ c • g = d • f := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  refine ⟨f a, g a, ha, ?_⟩
  ext x
  have hx : f a • x - f x • a ∈ f.ker := by
    simp [AddMonoidHom.mem_ker, mul_comm]
  have hg := AddMonoidHom.mem_ker.mp (hker hx)
  simpa only [map_sub, map_zsmul, AddMonoidHom.zsmul_apply, Int.zsmul_eq_mul,
    sub_eq_zero, mul_comm (f x)] using hg

/-- Nonzero integer characters with the same kernel have equal nonzero integer multiples. -/
theorem exists_ne_zero_zsmul_eq_of_ker_eq (f g : A →+ ℤ) (hf : f ≠ 0)
    (hker : f.ker = g.ker) :
    ∃ c e : ℤ, c ≠ 0 ∧ e ≠ 0 ∧ c • f = e • g := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  have hga : g a ≠ 0 := by
    intro h
    have hm : a ∈ f.ker := hker ▸ AddMonoidHom.mem_ker.mpr h
    exact ha (AddMonoidHom.mem_ker.mp hm)
  obtain ⟨c, d, hc, hcd⟩ := f.exists_ne_zero_zsmul_eq_of_ker_le g hf hker.le
  have hd : d ≠ 0 := by
    intro hd
    have hv : c * g a = 0 := by simpa [hd] using DFunLike.congr_fun hcd a
    exact hga ((Int.mul_eq_zero.mp hv).resolve_left hc)
  exact ⟨d, c, hd, hc, hcd.symm⟩

/-- A character annihilating the common kernel of two characters and a vector
outside it annihilates the kernel of their contraction at that vector. -/
theorem ker_zsmul_sub_zsmul_le_of_inf_ker_le (f g m : A →+ ℤ) (v : A)
    (hv : v ∉ f.ker ⊓ g.ker) (hm : f.ker ⊓ g.ker ≤ m.ker) (hmv : m v = 0) :
    (f v • g - g v • f).ker ≤ m.ker := by
  have step (f g : A →+ ℤ) (hv : f v ≠ 0) (hm : f.ker ⊓ g.ker ≤ m.ker) :
      (f v • g - g v • f).ker ≤ m.ker := by
    intro x hx
    have hx' : f v * g x - g v * f x = 0 := by
      simpa only [AddMonoidHom.mem_ker, sub_apply, zsmul_apply, Int.zsmul_eq_mul] using hx
    have hz : f v • x - f x • v ∈ f.ker ⊓ g.ker := by
      constructor
      · exact AddMonoidHom.mem_ker.mpr (by simp [mul_comm])
      · apply AddMonoidHom.mem_ker.mpr
        simpa only [map_sub, map_zsmul, Int.zsmul_eq_mul, mul_comm (f x)] using hx'
    have hz' := AddMonoidHom.mem_ker.mp (hm hz)
    have hprod : f v * m x = 0 := by simpa [hmv] using hz'
    exact AddMonoidHom.mem_ker.mpr ((Int.mul_eq_zero.mp hprod).resolve_left hv)
  by_cases hf : f v = 0
  · have hg : g v ≠ 0 := fun hg => hv ⟨hf, hg⟩
    intro x hx
    apply step g f hg (by simpa only [inf_comm] using hm)
    apply AddMonoidHom.mem_ker.mpr
    have hx' : f v * g x = g v * f x := by
      simpa only [AddMonoidHom.mem_ker, sub_apply, zsmul_apply, Int.zsmul_eq_mul,
        sub_eq_zero] using hx
    simpa only [sub_apply, zsmul_apply, Int.zsmul_eq_mul, sub_eq_zero] using hx'.symm
  · exact step f g hf hm

end AddMonoidHom
