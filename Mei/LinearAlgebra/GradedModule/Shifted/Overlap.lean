/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Reconstruction
public import Mei.LinearAlgebra.GradedModule.Shifted.Inclusion

/-!
# Descent on intersections of translated coefficient supports

If the intersection of two translates is another translate, completed coefficients
with the same ambient homogeneous components descend uniquely to that intersection.
The two original origins need not be comparable. Equality after inclusion in a
common larger translate suffices; no injectivity of finite quotient inclusions is
assumed. This describes an intersection of supports, without asserting that such a
translate exists for every positive monoid.
-/

public section

open TauCeti (PositiveDegrees)
noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

/-- A coefficient belongs to a smaller translated support precisely when its other
ambient components vanish. -/
theorem mem_range_shiftedCompletedInclusion_iff (r p : Γ) (hrp : r - p ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    x ∈ LinearMap.range (d.shiftedCompletedInclusion ℳ r p hrp) ↔
      ∀ u, u - r ∉ d.monoid → d.shiftedHomogeneousComponent ℳ p u x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ u hu
    rw [shiftedHomogeneousComponent_inclusion]
    exact d.shiftedHomogeneousComponent_eq_zero ℳ r hu y
  · intro hx
    refine ⟨d.shiftedCoefficientsOfComponents ℳ r
      (fun u => d.shiftedHomogeneousComponent ℳ p u x) hx, ?_⟩
    apply d.shiftedCoefficients_ext ℳ p
    intro u
    rw [shiftedHomogeneousComponent_inclusion, shiftedHomogeneousComponent_ofComponents]

/-- Compatible coefficient families descend uniquely to a translated intersection,
including when the two origins are not comparable. -/
theorem existsUnique_shiftedCoefficients_overlap (p q r : Γ)
    (hrp : r - p ∈ d.monoid) (hrq : r - q ∈ d.monoid)
    (hinter : ∀ u, u - r ∈ d.monoid ↔ u - p ∈ d.monoid ∧ u - q ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) (y : d.ShiftedCoefficients ℳ q)
    (hxy : ∀ u, d.shiftedHomogeneousComponent ℳ p u x =
      d.shiftedHomogeneousComponent ℳ q u y) :
    ∃! z : d.ShiftedCoefficients ℳ r,
      d.shiftedCompletedInclusion ℳ r p hrp z = x ∧
        d.shiftedCompletedInclusion ℳ r q hrq z = y := by
  have hx : ∀ u, u - r ∉ d.monoid → d.shiftedHomogeneousComponent ℳ p u x = 0 := by
    intro u hu
    by_cases hp : u - p ∈ d.monoid
    · rw [hxy]
      exact d.shiftedHomogeneousComponent_eq_zero ℳ q
        (fun hq => hu ((hinter u).mpr ⟨hp, hq⟩)) y
    · exact d.shiftedHomogeneousComponent_eq_zero ℳ p hp x
  obtain ⟨z, hz⟩ := (d.mem_range_shiftedCompletedInclusion_iff ℳ r p hrp x).mpr hx
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · apply d.shiftedCoefficients_ext ℳ q
    intro u
    rw [shiftedHomogeneousComponent_inclusion]
    have hz' := congrArg (d.shiftedHomogeneousComponent ℳ p u) hz
    rw [shiftedHomogeneousComponent_inclusion] at hz'
    exact hz'.trans (hxy u)
  · intro w hw
    exact d.shiftedCompletedInclusion_injective ℳ r p hrp (hw.1.trans hz.symm)

/-- Equality in a common larger support is the compatibility needed for overlap descent. -/
theorem existsUnique_shiftedCoefficients_overlap_of_inclusion_eq (p q r s : Γ)
    (hrp : r - p ∈ d.monoid) (hrq : r - q ∈ d.monoid)
    (hps : p - s ∈ d.monoid) (hqs : q - s ∈ d.monoid)
    (hinter : ∀ u, u - r ∈ d.monoid ↔ u - p ∈ d.monoid ∧ u - q ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) (y : d.ShiftedCoefficients ℳ q)
    (hxy : d.shiftedCompletedInclusion ℳ p s hps x =
      d.shiftedCompletedInclusion ℳ q s hqs y) :
    ∃! z : d.ShiftedCoefficients ℳ r,
      d.shiftedCompletedInclusion ℳ r p hrp z = x ∧
        d.shiftedCompletedInclusion ℳ r q hrq z = y := by
  apply d.existsUnique_shiftedCoefficients_overlap ℳ p q r hrp hrq hinter x y
  intro u
  simpa only [shiftedHomogeneousComponent_inclusion] using
    congrArg (d.shiftedHomogeneousComponent ℳ s u) hxy

/-- Inside a common containing translate, the intersection of the two inclusion
ranges is the inclusion range of their translated intersection. -/
theorem range_shiftedCompletedInclusion_eq_inf (p q r s : Γ)
    (hps : p - s ∈ d.monoid) (hqs : q - s ∈ d.monoid)
    (hrs : r - s ∈ d.monoid)
    (hinter : ∀ u, u - r ∈ d.monoid ↔ u - p ∈ d.monoid ∧ u - q ∈ d.monoid) :
    LinearMap.range (d.shiftedCompletedInclusion ℳ r s hrs) =
      LinearMap.range (d.shiftedCompletedInclusion ℳ p s hps) ⊓
        LinearMap.range (d.shiftedCompletedInclusion ℳ q s hqs) := by
  ext x
  rw [Submodule.mem_inf, mem_range_shiftedCompletedInclusion_iff,
    mem_range_shiftedCompletedInclusion_iff, mem_range_shiftedCompletedInclusion_iff]
  constructor
  · intro hx
    constructor
    · intro u hu
      exact hx u (fun hr => hu ((hinter u).mp hr).1)
    · intro u hu
      exact hx u (fun hr => hu ((hinter u).mp hr).2)
  · rintro ⟨hp, hq⟩ u hu
    by_cases hup : u - p ∈ d.monoid
    · exact hq u (fun huq => hu ((hinter u).mpr ⟨hup, huq⟩))
    · exact hp u hup

end TauCeti.PositiveDegrees
