/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Products and powers of left ideals

When the fourth power of a left ideal vanishes, every product of four of its elements
is zero. This allows polynomial identities in such elements to truncate at degree three,
even in a noncommutative semiring. Surjective homomorphisms preserve products and
powers of left ideals, so nilpotency bounds descend to quotient rings. These
statements extend Mathlib's `Ideal.map_mul` and `Ideal.map_pow` beyond commutative
targets, using `Ideal.mem_map_iff_of_surjective`.

In a free module with a chosen basis, an element is an ideal multiple of the
whole module exactly when all its basis coefficients lie in the ideal.
-/

public section

namespace Ideal

variable {A : Type*} [Semiring A]

/-- Every element of a nilpotent left ideal is nilpotent. -/
theorem isNilpotent_of_mem (I : Ideal A) (hI : IsNilpotent I) {x : A} (hx : x ∈ I) :
    IsNilpotent x := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl hx⟩

/-- A product of four elements of a left ideal vanishes if its fourth power is bottom. -/
theorem mul_four_eq_zero_of_pow_eq_bot (I : Ideal A) (hI : I ^ 4 = ⊥)
    {a b c d : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I) :
    a * b * c * d = 0 := by
  have h := Ideal.mul_mem_mul (Ideal.mul_mem_mul (Ideal.mul_mem_mul ha hb) hc) hd
  -- Expand the fixed numeral power with the left-associated ideal-power convention.
  have he : ((I * I) * I) * I = I ^ 4 := by
    simp only [show (4 : ℕ) = 3 + 1 from rfl, Submodule.pow_succ,
      show (3 : ℕ) = 2 + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
      Submodule.pow_zero, Ideal.one_eq_top, Ideal.top_mul]
  rwa [he, hI, Ideal.mem_bot] at h

end Ideal

namespace Ideal

variable {A B : Type*} [Semiring A] [Semiring B]

/-- Surjective ring homomorphisms preserve products of left ideals, including
in noncommutative semirings. -/
theorem map_mul_of_surjective (I J : Ideal A) (f : A →+* B)
    (hf : Function.Surjective f) : (I * J).map f = I.map f * J.map f := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, mul_le]
    intro a ha b hb
    simpa only [mem_comap, map_mul] using
      mul_mem_mul (mem_map_of_mem f ha) (mem_map_of_mem f hb)
  · apply mul_le.mpr
    intro a ha b hb
    obtain ⟨a, ha', rfl⟩ := (mem_map_iff_of_surjective f hf).mp ha
    obtain ⟨b, hb', rfl⟩ := (mem_map_iff_of_surjective f hf).mp hb
    exact (map_mul f a b) ▸ mem_map_of_mem f (mul_mem_mul ha' hb')

/-- Surjective ring homomorphisms preserve powers of left ideals, including
in noncommutative semirings. -/
theorem map_pow_of_surjective (I : Ideal A) (f : A →+* B)
    (hf : Function.Surjective f) (n : ℕ) : (I ^ n).map f = I.map f ^ n := by
  induction n with
  | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, map_top]
  | succ n ih => rw [Submodule.pow_succ, map_mul_of_surjective _ _ f hf, ih,
      Submodule.pow_succ]

end Ideal

namespace Module.Basis

variable {ι S W : Type*} [Semiring S] [AddCommMonoid W] [Module S W]
  (c : Basis ι S W)

/-- Ideal multiples of a free module are detected by its basis coefficients. -/
theorem mem_ideal_smul_top_iff_repr_mem (I : Ideal S) [I.IsTwoSided] (x : W) :
    x ∈ I • (⊤ : Submodule S W) ↔ ∀ i, c.repr x i ∈ I := by
  rw [← c.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [← Finsupp.linearCombination_apply, c.repr_linearCombination] using ha
  · intro hx
    exact ⟨c.repr x, hx, c.linearCombination_repr x⟩

end Module.Basis
