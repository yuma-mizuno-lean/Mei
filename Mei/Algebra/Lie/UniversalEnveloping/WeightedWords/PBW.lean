/-
Copyright (c) 2026 The Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.WeightedWords.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Weighted.Basic

/-!
# Augmentation cofinality for weighted PBW ideals

For an ordered Lie basis with bracket-compatible weights, the weighted word ideal
is the existing weighted PBW ideal. Consequently bounded positive weights give
explicit cofinal bounds between the weighted PBW filtration and augmentation
powers. No field hypothesis is needed.

The identification uses `Module.Basis.pbwMonomial_mem_weightedPBWFiltration`
and `Module.Basis.weightedPBWFiltration_def` from Tau Ceti's weighted PBW theory.
-/

public section

namespace Module.Basis

variable {R L S : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder S] (b : Basis S R L) (weight : S → ℕ)
  (hbracket : ∀ i j k, weight k < weight i + weight j → b.repr ⁅b i, b j⁆ k = 0)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)

open Mei.UniversalEnvelopingAlgebra

/-- Weighted word ideals agree with the weighted PBW ideals when straightening
does not decrease weight. -/
theorem weightedWordIdeal_eq_weightedPBWIdeal (n : ℕ) :
    weightedWordIdeal (R := R) b weight n = b.weightedPBWIdeal weight hbracket n := by
  apply le_antisymm
  · rw [weightedWordIdeal_le_iff]
    intro l hl
    rw [mem_weightedPBWIdeal_iff]
    simpa only [TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_def,
      List.map_map, Function.comp_def] using
      b.pbwMonomial_mem_weightedPBWFiltration weight hbracket l hl
  · intro a ha
    rw [mem_weightedPBWIdeal_iff, weightedPBWFiltration_def] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f, hf, rfl⟩ := ha
      rw [pbwBasis_apply]
      have hw : n ≤ ((f.toMultiset.sort (· ≤ ·)).map weight).sum := by
        simpa only [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq,
          ← Finsupp.weight_toFinsupp, Finsupp.toMultiset_toFinsupp, Set.mem_ofPred_eq] using hf
      simpa only [TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_def,
      List.map_map, Function.comp_def] using
        prod_mem_weightedWordIdeal (R := R) b weight n _ hw
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | smul r a _ ha => exact Submodule.smul_of_tower_mem _ r ha

/-- Positive basis weights put augmentation powers inside the weighted PBW ideals. -/
theorem augmentation_pow_le_weightedPBWIdeal (hpos : ∀ s, 1 ≤ weight s) (k : ℕ) :
    J ^ k ≤ b.weightedPBWIdeal weight hbracket k := by
  rw [← weightedWordIdeal_eq_weightedPBWIdeal]
  apply augmentation_pow_le_weightedWordIdeal b _ weight hpos
  apply eq_top_iff.mpr
  intro x _
  apply LieSubalgebra.submodule_span_le_lieSpan
  rw [b.span_eq]
  trivial

/-- Bounded basis weights give the explicit reverse cofinality modulus. -/
theorem weightedPBWIdeal_le_augmentation_pow (B : ℕ) (hbound : ∀ s, weight s ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    b.weightedPBWIdeal weight hbracket (B * (k - 1) + 1) ≤ J ^ k := by
  rw [← weightedWordIdeal_eq_weightedPBWIdeal]
  exact weightedWordIdeal_le_augmentation_pow b weight B hbound hk

end Module.Basis
