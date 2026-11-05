/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Inclusion
public import Mei.LinearAlgebra.GradedModule.Shifted.Overlap

/-!
# Images and intersections of global coefficient charts

The image of any translated chart consists exactly of global coefficients
whose ambient components vanish outside that translate. Equality of global
images therefore supplies the compatibility for the existing overlap descent.
When two translates have a translated intersection, their global chart images
intersect in exactly that chart. Neither comparability nor finite support of
coefficients is assumed.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

/-- Membership in one global chart is exactly vanishing outside its translated support. -/
theorem mem_range_toShiftedDirectLimitOfChart_iff (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) (x : d.ShiftedDirectLimit ℳ) :
    x ∈ LinearMap.range (d.toShiftedDirectLimitOfChart ℳ p s hp) ↔
      ∀ u, u - p ∉ d.monoid → d.shiftedDirectLimitComponents ℳ x u = 0 := by
  constructor
  · rintro ⟨a, rfl⟩ u hu
    rw [shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]
    exact d.shiftedHomogeneousComponent_eq_zero ℳ p hu a
  · intro hx
    refine ⟨d.shiftedCoefficientsOfComponents ℳ p (d.shiftedDirectLimitComponents ℳ x) hx, ?_⟩
    apply d.shiftedDirectLimitComponents_injective ℳ
    funext u
    rw [shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
      shiftedHomogeneousComponent_ofComponents]

/-- Equality in the global coefficient module implies unique descent to a translated overlap. -/
theorem existsUnique_shiftedCoefficients_overlap_of_global_eq (p q r : Γ)
    (hrp : r - p ∈ d.monoid) (hrq : r - q ∈ d.monoid)
    (s t : Multiset d.monoid)
    (hps : p - d.coefficientOrigin s ∈ d.monoid)
    (hqt : q - d.coefficientOrigin t ∈ d.monoid)
    (hinter : ∀ u, u - r ∈ d.monoid ↔ u - p ∈ d.monoid ∧ u - q ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) (y : d.ShiftedCoefficients ℳ q)
    (hxy : d.toShiftedDirectLimitOfChart ℳ p s hps x =
      d.toShiftedDirectLimitOfChart ℳ q t hqt y) :
    ∃! z : d.ShiftedCoefficients ℳ r,
      d.shiftedCompletedInclusion ℳ r p hrp z = x ∧
        d.shiftedCompletedInclusion ℳ r q hrq z = y := by
  apply d.existsUnique_shiftedCoefficients_overlap ℳ p q r hrp hrq hinter x y
  intro u
  simpa only [shiftedDirectLimitComponents_toShiftedDirectLimitOfChart] using
    congrArg (fun a => d.shiftedDirectLimitComponents ℳ a u) hxy

/-- The image of a translated intersection is the intersection of the global chart images. -/
theorem range_toShiftedDirectLimitOfChart_eq_inf (p q r : Γ)
    (s t v : Multiset d.monoid)
    (hps : p - d.coefficientOrigin s ∈ d.monoid)
    (hqt : q - d.coefficientOrigin t ∈ d.monoid)
    (hrv : r - d.coefficientOrigin v ∈ d.monoid)
    (hinter : ∀ u, u - r ∈ d.monoid ↔ u - p ∈ d.monoid ∧ u - q ∈ d.monoid) :
    LinearMap.range (d.toShiftedDirectLimitOfChart ℳ r v hrv) =
      LinearMap.range (d.toShiftedDirectLimitOfChart ℳ p s hps) ⊓
        LinearMap.range (d.toShiftedDirectLimitOfChart ℳ q t hqt) := by
  have hr : r - r ∈ d.monoid := by simp
  obtain ⟨hrp, hrq⟩ := (hinter r).mp hr
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨d.shiftedCompletedInclusion ℳ r p hrp a,
      d.toShiftedDirectLimitOfChart_inclusion ℳ r p hrp v s hrv hps a⟩,
      ⟨d.shiftedCompletedInclusion ℳ r q hrq a,
        d.toShiftedDirectLimitOfChart_inclusion ℳ r q hrq v t hrv hqt a⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨c, hc, _⟩ := d.existsUnique_shiftedCoefficients_overlap_of_global_eq ℳ p q r
      hrp hrq s t hps hqt hinter a b (ha.trans hb.symm)
    refine ⟨c, ?_⟩
    rw [← d.toShiftedDirectLimitOfChart_inclusion ℳ r p hrp v s hrv hps c, hc.1]
    exact ha

end Mei.PositiveDegrees
