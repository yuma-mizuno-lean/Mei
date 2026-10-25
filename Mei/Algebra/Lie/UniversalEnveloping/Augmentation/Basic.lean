/-
Copyright (c) 2026 The Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic

/-!
# Products in augmentation powers

A word in canonical Lie generators belongs to the augmentation power indexed by
its length. This gives augmentation-power bounds for words from any family of
Lie algebra elements, without weights or a Lie-generation assumption.

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
