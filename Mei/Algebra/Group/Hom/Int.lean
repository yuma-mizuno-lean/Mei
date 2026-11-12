/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Group.Hom.Int
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Integer characters

Nonzero integer-valued characters with the same kernel are rationally proportional:
some nonzero integer multiples agree. This detects proportional integral normals
without choosing a basis or extending scalars to a field. Kernel containment
also gives proportionality when the second character can vanish. For two
characters, contracting against a vector outside their common kernel detects
every character annihilating both that kernel and the vector. Characters on a
product with an integer factor are determined by their coordinate restrictions.
-/

public section

namespace AddMonoidHom

/-- An integer character on a product with an integer factor is determined
by its restriction to the first factor and its value on the integer generator. -/
theorem apply_prod_int {Λ : Type*} [AddMonoid Λ] (m : (Λ × ℤ) →+ ℤ) (v : Λ) (c : ℤ) :
    m (v, c) = m (v, 0) + c * m (0, 1) := by
  have hc := (m.comp (AddMonoidHom.inr Λ ℤ)).map_zsmul c (1 : ℤ)
  have hc' : m (0, c) = c * m (0, 1) := by simpa using hc
  rw [← hc', ← map_add]
  simp

variable {A : Type*} [AddGroup A]

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
