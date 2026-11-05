/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Action
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.TwistedAction

/-!
# Ray automorphisms induce the identity on associated graded coefficients

Conjugation by any unit scalar series changes a positive coefficient of order
`k` only in order `k + 1`. The constant coefficient of the series is an arbitrary
unit; it need not equal one. The same assertion holds for reverse crossings.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)
  (P : AddSubmonoid Γ) (δ : Γ →+ ℤ) (hδ : ∀ p ∈ P, 0 ≤ δ p)

local notation "F" => positiveFiltration q β P δ hδ

/-- A positive ray automorphism is the identity modulo the next ideal order. -/
theorem completedRayAction_sub_mem (n : P) (hn : 0 < δ n)
    (H : (PowerSeries R)ˣ) (k : ℕ) {a : (F).completion}
    (ha : a ∈ (F).completionIdeal k) :
    completedRayAction q β P δ hδ n hn H a - a ∈ (F).completionIdeal (k + 1) := by
  have h := (F).completedTwistedSeriesAction_sub_mem
    (completedRayGenerator q β P δ hδ n hn) (1 : R) H k ha
  simpa only [AlgFiltration.completedTwistedSeriesAction_apply, PowerSeries.rescale_one,
    RingHom.id_apply, completedRayAction, AlgFiltration.completedSeriesAction_apply] using h

/-- Reverse ray crossings also act trivially modulo the next ideal order. -/
theorem completedRayAction_symm_sub_mem (n : P) (hn : 0 < δ n)
    (H : (PowerSeries R)ˣ) (k : ℕ) {a : (F).completion}
    (ha : a ∈ (F).completionIdeal k) :
    (completedRayAction q β P δ hδ n hn H).symm a - a ∈
      (F).completionIdeal (k + 1) := by
  simpa only [map_inv, AlgEquiv.aut_inv] using
    completedRayAction_sub_mem q β P δ hδ n hn (H⁻¹) k ha

end Mei.QuantumMonoidAlgebra
