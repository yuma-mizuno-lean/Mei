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
public import TauCeti.Algebra.Lie.UniversalEnveloping.Cofinality

/-!
# Cofinality of the degree and augmentation filtrations

A homogeneous Lie-generating family with degrees bounded above by `B` makes every degree
strictly greater than `B * (k - 1)` lie in the `k`-th augmentation power. The generators need
not be a basis or a finite family. Together with the forward inclusion for positive gradings,
this gives cofinality of the degree and augmentation filtrations.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra (augmentation_pow_le_degreeFiltration degreeFiltration
  homogeneousSubmodule ι_mem_homogeneousSubmodule)

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L S : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)

variable [DecidableEq Γ] (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] (d : Γ →+ ℤ)

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
    exact TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_le_augmentation_pow ℒ d
      (fun i hi => hpos i hi.le)
      e deg he hhom B hb k
  · rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, augmentation_pow_le_degreeFiltration ℒ d hpos k⟩

end Mei.UniversalEnvelopingAlgebra
