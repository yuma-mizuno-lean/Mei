/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.DegreeMap
public import Mei.Algebra.Lie.UniversalEnveloping.DegreeFiltration

/-!
# Degree reflection by the canonical enveloping map

When the canonical Lie map into an enveloping algebra is injective, it reflects
the degree filtration. Quotienting by a degree ideal therefore kills precisely
the Lie elements supported above the same cutoff. Injectivity is explicit here,
so any available embedding theorem can supply it.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  [DecidableEq Γ] (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] (d : Γ →+ ℤ)

/-- The preimage of an enveloping degree ideal is the corresponding Lie degree tail,
provided the canonical enveloping map is injective. -/
theorem comap_degreeFiltration_ι (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (hι : Function.Injective (ι R : L → _root_.UniversalEnvelopingAlgebra R L)) (k : ℕ) :
    (((degreeFiltration ℒ d hneg).ideal k).restrictScalars R).comap
        (ι R : L →ₗ⁅R⁆ _root_.UniversalEnvelopingAlgebra R L).toLinearMap =
      Mei.DirectSum.degreeTail ℒ d k := by
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.degreeIdeal_restrictScalars]
  exact LinearMap.comap_degreeTail_eq_of_injective _ ℒ (homogeneousSubmodule ℒ)
    hι (fun _ _ hx => ι_mem_homogeneousSubmodule ℒ hx) d k

end Mei.UniversalEnvelopingAlgebra
