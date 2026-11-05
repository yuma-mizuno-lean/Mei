/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Embedding
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.FiniteSupport

/-!
# Finite coefficients inside the global algebra

When positive differences span the ambient group, the original graded algebra
is exactly the part of the global coefficient algebra whose ambient homogeneous
components have finite support. Thus genuine infinite coefficient families cannot
come from an ordinary graded coefficient.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A) [GradedAlgebra 𝒜]
  (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)

/-- Embedding the recovered finite coefficient returns the given global coefficient. -/
@[simp]
theorem toShiftedDirectLimitAlgHom_finiteCoefficientOfShiftedDirectLimit
    (x : d.ShiftedDirectLimit 𝒜)
    (hx : Set.Finite {u | d.shiftedDirectLimitComponents 𝒜 x u ≠ 0}) :
    d.toShiftedDirectLimitAlgHom 𝒜 hspan (d.finiteCoefficientOfShiftedDirectLimit 𝒜 x hx) = x := by
  apply d.shiftedDirectLimitComponents_injective 𝒜
  funext u
  rw [shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom,
    decompose_finiteCoefficientOfShiftedDirectLimit]

/-- The image of the original graded algebra consists exactly of the finite component families. -/
theorem mem_range_toShiftedDirectLimitAlgHom_iff (x : d.ShiftedDirectLimit 𝒜) :
    x ∈ (d.toShiftedDirectLimitAlgHom 𝒜 hspan).range ↔
      Set.Finite {u | d.shiftedDirectLimitComponents 𝒜 x u ≠ 0} := by
  constructor
  · rintro ⟨a, rfl⟩
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom] using
      (DirectSum.decompose 𝒜 a).finite_support
  · intro hx
    exact ⟨d.finiteCoefficientOfShiftedDirectLimit 𝒜 x hx,
      d.toShiftedDirectLimitAlgHom_finiteCoefficientOfShiftedDirectLimit 𝒜 hspan x hx⟩

/-- Recovering the original finite coefficient is inverse to the algebra embedding. -/
@[simp]
theorem finiteCoefficientOfShiftedDirectLimit_toShiftedDirectLimitAlgHom (a : A)
    (ha : Set.Finite {u | d.shiftedDirectLimitComponents 𝒜
      (d.toShiftedDirectLimitAlgHom 𝒜 hspan a) u ≠ 0}) :
    d.finiteCoefficientOfShiftedDirectLimit 𝒜 (d.toShiftedDirectLimitAlgHom 𝒜 hspan a) ha = a := by
  apply d.toShiftedDirectLimitAlgHom_injective 𝒜 hspan
  exact d.toShiftedDirectLimitAlgHom_finiteCoefficientOfShiftedDirectLimit 𝒜 hspan _ ha

end Mei.PositiveDegrees
