/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Augmentation.Basic
public import Mei.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import Mei.Algebra.Order.BigOperators.Ring.List
public import Mei.RingTheory.GradedAlgebra.Generators
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic

/-!
# Cofinality of the degree and augmentation filtrations

A homogeneous Lie-generating family with degrees bounded above by `B` makes every degree
strictly greater than `B * (k - 1)` lie in the `k`-th augmentation power. The generators need
not be a basis or a finite family. Together with the forward inclusion for positive gradings,
this gives cofinality of the degree and augmentation filtrations.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L S : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)

variable [DecidableEq Γ] (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] (d : Γ →+ ℤ)

/-- A bounded homogeneous Lie-generating family puts sufficiently high degree in any
prescribed augmentation power. -/
theorem degreeFiltration_le_augmentation_pow (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (e : S → L) (deg : S → Γ) (he : LieSubalgebra.lieSpan R L (Set.range e) = ⊤)
    (hhom : ∀ s, e s ∈ ℒ (deg s)) (B : ℕ) (hb : ∀ s, d (deg s) ≤ (B : ℤ)) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal (B * (k - 1) + 1) ≤ J ^ k := by
  have hgen : Algebra.adjoin R (Set.range (fun s => ι R (e s))) = ⊤ := by
    simpa only [← Set.range_comp, Function.comp_def] using
      TauCeti.UniversalEnvelopingAlgebra.adjoin_image_ι_eq_top R L he
  rw [Mei.UniversalEnvelopingAlgebra.degreeFiltration_ideal,
    GradedAlgebra.degreeIdeal_le_iff]
  intro n hn x hx
  have hspan : homogeneousSubmodule ℒ n ≤ (J ^ k).restrictScalars R := by
    rw [Mei.GradedAlgebra.grade_eq_span_words (homogeneousSubmodule ℒ)
      (fun s => ι R (e s)) deg hgen (fun s => ι_mem_homogeneousSubmodule ℒ (hhom s)) n]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have hlen : k ≤ l.length := by
      rw [← hl, map_list_sum, List.map_map] at hn
      have h := List.le_length_of_sum_ge (l.map (fun s => d (deg s))) B k
        (fun x hx => by obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; exact hb s) hn
      simpa only [List.length_map] using h
    apply Ideal.pow_le_pow_right hlen
    exact prod_mem_augmentation_pow e l
  exact hspan hx

/-- Under positivity and a bounded homogeneous generating family, the two ideal families are
mutually cofinal in the reverse-inclusion order on ideals. -/
theorem degreeFiltration_augmentation_isCofinalFor
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (e : S → L) (deg : S → Γ)
    (he : LieSubalgebra.lieSpan R L (Set.range e) = ⊤) (hhom : ∀ s, e s ∈ ℒ (deg s))
    (B : ℕ) (hb : ∀ s, d (deg s) ≤ (B : ℤ)) :
    IsCofinalFor (Set.range fun k : ℕ => OrderDual.toDual (J ^ k))
        (Set.range fun n : ℕ => OrderDual.toDual
          ((degreeFiltration ℒ d (fun i hi => hpos i hi.le)).ideal n)) ∧
      IsCofinalFor (Set.range fun n : ℕ => OrderDual.toDual
          ((degreeFiltration ℒ d (fun i hi => hpos i hi.le)).ideal n))
        (Set.range fun k : ℕ => OrderDual.toDual (J ^ k)) := by
  constructor
  · rintro _ ⟨k, rfl⟩
    refine ⟨_, ⟨B * (k - 1) + 1, rfl⟩, ?_⟩
    exact degreeFiltration_le_augmentation_pow ℒ d (fun i hi => hpos i hi.le)
      e deg he hhom B hb k
  · rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, augmentation_pow_le_degreeFiltration ℒ d hpos k⟩

end Mei.UniversalEnvelopingAlgebra
