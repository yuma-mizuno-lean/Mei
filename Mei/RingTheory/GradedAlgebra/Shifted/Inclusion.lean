/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.Inclusion

/-!
# Products commute with inclusions of translated coefficient supports

Including each factor in a containing translated support includes their completed
product in the sum of the containing translates.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A) [SetLike.GradedMul 𝒜]

/-- Enlarging both translated supports commutes with their completed product. -/
theorem shiftedCompletedInclusion_shiftedCompletionMul (p q r s : Γ)
    (hpr : p - r ∈ d.monoid) (hqs : q - s ∈ d.monoid)
    (hpqrs : p + q - (r + s) ∈ d.monoid)
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q) :
    d.shiftedCompletedInclusion 𝒜 (p + q) (r + s) hpqrs
        (d.shiftedCompletionMul 𝒜 p q x y) =
      d.shiftedCompletionMul 𝒜 r s
        (d.shiftedCompletedInclusion 𝒜 p r hpr x)
        (d.shiftedCompletedInclusion 𝒜 q s hqs y) := by
  apply (d.shiftedFiltration 𝒜 (r + s)).completion_ext
  intro k
  obtain ⟨u, hu⟩ := ((d.shiftedFiltration 𝒜 p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 p).projection k x)
  obtain ⟨v, hv⟩ := ((d.shiftedFiltration 𝒜 q).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 q).projection k y)
  have hru : Submodule.Quotient.mk (shiftedSupportInclusion 𝒜 d.monoid p r hpr u) =
      (d.shiftedFiltration 𝒜 r).projection k (d.shiftedCompletedInclusion 𝒜 p r hpr x) := by
    rw [projection_shiftedCompletedInclusion, ← hu, Submodule.mkQ_apply,
      shiftedQuotientMap_mk]
  have hsv : Submodule.Quotient.mk (shiftedSupportInclusion 𝒜 d.monoid q s hqs v) =
      (d.shiftedFiltration 𝒜 s).projection k (d.shiftedCompletedInclusion 𝒜 q s hqs y) := by
    rw [projection_shiftedCompletedInclusion, ← hv, Submodule.mkQ_apply,
      shiftedQuotientMap_mk]
  rw [projection_shiftedCompletedInclusion,
    d.projection_shiftedCompletionMul 𝒜 p q k x y u v hu hv, shiftedQuotientMap_mk,
    d.projection_shiftedCompletionMul 𝒜 r s k _ _
      (shiftedSupportInclusion 𝒜 d.monoid p r hpr u)
      (shiftedSupportInclusion 𝒜 d.monoid q s hqs v) hru hsv]
  congr 1
  apply Subtype.ext
  simp only [coe_shiftedSupportInclusion, coe_shiftedMul]

end Mei.PositiveDegrees
