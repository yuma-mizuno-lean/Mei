/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import Mei.Algebra.Lie.UniversalEnveloping.Grading
public import Mei.RingTheory.Ideal.Operations

/-!
# Euler derivations and augmentation quotients

Lifted grading derivations preserve the enveloping degree filtration. For a
positive Lie grading, the image of the augmentation ideal in each degree
quotient is nilpotent.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

open TauCeti.UniversalEnvelopingAlgebra (degreeFiltration mem_degreeFiltration_ideal_iff
  augmentation_pow_le_degreeFiltration)

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ) [DecidableEq Γ] [GradedLieAlgebra ℒ]

/-- Every lifted grading derivation preserves the integral degree filtration. -/
theorem euler_mem_degreeFiltration (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (φ : Γ →+ R)
    {k : ℕ} {a : _root_.UniversalEnvelopingAlgebra R L}
    (ha : a ∈ (degreeFiltration ℒ d hneg).ideal k) :
    (TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L
      (LieDerivation.ofGrading ℒ φ) :
        Module.End R (_root_.UniversalEnvelopingAlgebra R L)) a ∈
      (degreeFiltration ℒ d hneg).ideal k := by
  rw [mem_degreeFiltration_ideal_iff] at ha ⊢
  intro n hn
  rw [euler_component ℒ φ, ha n hn, smul_zero]

/-- The augmentation image in the order-`k` degree quotient has vanishing
`(k + 1)`st power for a strictly positive Lie grading. -/
theorem augmentation_map_quotient_pow_eq_bot
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (k : ℕ) :
    let F := degreeFiltration ℒ d (fun n hn => hpos n hn.le)
    let J := (TauCeti.HopfIdeal.augmentation R (_root_.UniversalEnvelopingAlgebra R L)).toIdeal
    (J.map (Ideal.Quotient.mk (F.ideal (k + 1)))) ^ (k + 1) = ⊥ := by
  dsimp only
  rw [← Ideal.map_pow_of_surjective _ _ Ideal.Quotient.mk_surjective]
  apply eq_bot_iff.mpr
  calc
    _ ≤ Ideal.map (Ideal.Quotient.mk _) ((degreeFiltration ℒ d
        (fun n hn => hpos n hn.le)).ideal (k + 1)) :=
      Ideal.map_mono (augmentation_pow_le_degreeFiltration ℒ d hpos (k + 1))
    _ = ⊥ := Ideal.map_quotient_self _

end Mei.UniversalEnvelopingAlgebra
