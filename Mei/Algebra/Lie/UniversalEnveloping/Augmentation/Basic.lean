/-
Copyright (c) 2026 The Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic

/-!
# Augmentation generators and powers

A Lie-generating family generates the augmentation ideal. A word in canonical
Lie generators belongs to the augmentation power indexed by its length. This gives
augmentation-power bounds for words from any family of Lie algebra elements,
without weights or a Lie-generation assumption. Representations sending Lie
generators into an ideal preserve the corresponding powers.

This refines the canonical-generator description in
`TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic`.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

universe u v w

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {S : Type w} (e : S → L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Lie-generating family generates the augmentation as a left ideal. -/
theorem augmentation_eq_span_generators
    (he : LieSubalgebra.lieSpan R L (Set.range e) = ⊤) :
    J = Ideal.span (Set.range (fun s => ι (e s))) := by
  rw [TauCeti.UniversalEnvelopingAlgebra.augmentation_toIdeal_eq_span_range_ι]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ LieSubalgebra.lieSpan R L (Set.range e) := by rw [he]; trivial
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact Ideal.subset_span ⟨s, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul r x _ hx =>
      simpa using Submodule.smul_of_tower_mem (Ideal.span (Set.range (fun s => ι (e s)) )) r hx
    | lie x y _ _ hx hy =>
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      exact sub_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)
  · apply Ideal.span_mono
    rintro _ ⟨s, rfl⟩
    exact ⟨e s, rfl⟩

/-- A word in canonical Lie generators belongs to the augmentation power indexed by its length. -/
theorem prod_mem_augmentation_pow (l : List S) :
    (l.map (fun s => ι (e s))).prod ∈ J ^ l.length := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.length_nil, Submodule.pow_zero,
      Ideal.one_eq_top, Submodule.mem_top]
  | cons s l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Ideal.IsTwoSided.pow_succ]
    exact Ideal.mul_mem_mul
      (TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation R L (e s)) ih

end Mei.UniversalEnvelopingAlgebra

namespace AlgHom

variable {R L A : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [Semiring A] [Algebra R A]

/-- An enveloping representation sending Lie generators into an ideal sends each
augmentation power into the corresponding ideal power. -/
theorem map_mem_augmentation_pow (f : UniversalEnvelopingAlgebra R L →ₐ[R] A)
    (I : Ideal A) (hf : ∀ x : L, f (UniversalEnvelopingAlgebra.ι R x) ∈ I)
    (n : ℕ) {a : UniversalEnvelopingAlgebra R L}
    (ha : a ∈ (TauCeti.HopfIdeal.augmentation R
      (UniversalEnvelopingAlgebra R L)).toIdeal ^ n) : f a ∈ I ^ n := by
  have h (k : ℕ) : (TauCeti.HopfIdeal.augmentation R
      (UniversalEnvelopingAlgebra R L)).toIdeal ^ k ≤ (I ^ k).comap f := by
    induction k with
    | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, Ideal.comap_top, le_refl]
    | succ k ih =>
      rw [Submodule.pow_succ]
      apply Ideal.mul_le.mpr
      intro u hu v hv
      have hv' : f v ∈ I := by
        have hgen : (TauCeti.HopfIdeal.augmentation R
            (UniversalEnvelopingAlgebra R L)).toIdeal ≤ I.comap f := by
          rw [TauCeti.UniversalEnvelopingAlgebra.augmentation_toIdeal_eq_span_range_ι,
            Ideal.span_le]
          rintro _ ⟨x, rfl⟩
          exact hf x
        exact hgen hv
      have hu' : f u ∈ I ^ k := ih hu
      simpa only [Ideal.mem_comap, map_mul, Submodule.pow_succ] using
        Ideal.mul_mem_mul hu' hv'
  exact h n ha

end AlgHom
