/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import Mei.RingTheory.GradedAlgebra.Generators
public import Mei.RingTheory.Ideal.List
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

private theorem length_ge_of_degree_ge (d : Γ →+ ℤ) (deg : S → Γ) (B k : ℕ)
    (hb : ∀ s, d (deg s) ≤ (B : ℤ)) (l : List S)
    (hl : (B * (k - 1) + 1 : ℕ) ≤ d (l.map deg).sum) : k ≤ l.length := by
  by_contra h
  have hlen : l.length ≤ k - 1 := by omega
  have hs : d (l.map deg).sum ≤ (B : ℤ) * l.length := by
    have h := List.sum_le_length_nsmul (l.map (fun s => d (deg s))) (B : ℤ)
      (fun x hx => by obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx; exact hb s)
    simpa only [map_list_sum, List.map_map, Function.comp_def, List.length_map,
      nsmul_eq_mul, mul_comm] using h
  have hbound := hs.trans
    (mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hlen) (Int.natCast_nonneg B))
  push_cast at hl
  omega

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
    apply Ideal.pow_le_pow_right (length_ge_of_degree_ge d deg B k hb l ?_)
    · simpa only [List.length_map] using Ideal.list_prod_mem_pow J
        (l.map (fun s => ι R (e s))) (fun a ha => by
          obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
          exact TauCeti.HopfIdeal.mem_toIdeal.mpr
            (TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation R L (e s)))
    · simpa only [hl] using hn
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
