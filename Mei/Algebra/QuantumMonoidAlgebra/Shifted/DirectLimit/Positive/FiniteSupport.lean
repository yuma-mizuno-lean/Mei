/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Positive.Support
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.FiniteSupport

/-!
# Finite positive coefficients inside their completion

An element of the positive completed quantum algebra comes from an ordinary
positive coefficient precisely when its ambient homogeneous components have
finite support. Reconstruction in the original graded module preserves positive
support and is inverse to the original completion map. No spanning condition on
the positive monoid is required.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => d.ShiftedDirectLimit (grade q β)

/-- Completing an ordinary positive coefficient preserves its ambient decomposition. -/
theorem shiftedDirectLimitComponents_positiveCompletionToDirectLimit_toCompletion
    (a : positiveSubalgebra q β d.monoid) (u : Γ) :
    d.shiftedDirectLimitComponents (grade q β)
        (positiveCompletionToDirectLimit q β d ((F).toCompletion a)) u =
      DirectSum.decompose (grade q β) (a : QuantumMonoidAlgebra q β) u := by
  rw [shiftedDirectLimitComponents_positiveCompletionToDirectLimit,
    positiveCompletionShiftEquiv_toCompletion, PositiveDegrees.shiftedHomogeneousComponent_of]
  simp only [coe_positiveShiftEquiv, monomial_zero, one_mul]

/-- Recover the ordinary positive coefficient of a completed element with finite ambient support. -/
def finitePositiveCoefficientOfCompletion (x : (F).completion)
    (hx : Set.Finite {u | d.shiftedDirectLimitComponents (grade q β)
      (positiveCompletionToDirectLimit q β d x) u ≠ 0}) : positiveSubalgebra q β d.monoid :=
  ⟨d.finiteCoefficientOfShiftedDirectLimit (grade q β) (positiveCompletionToDirectLimit q β d x) hx,
    by
      apply (mem_supportedSubalgebra_iff (grade q β) d.monoid _).mpr
      intro u hu
      have hs := (mem_range_positiveCompletionToDirectLimit_iff q β d
        (positiveCompletionToDirectLimit q β d x)).mp ⟨x, rfl⟩ u hu
      have hc := d.decompose_finiteCoefficientOfShiftedDirectLimit (grade q β)
        (positiveCompletionToDirectLimit q β d x) hx u
      exact congrArg (fun a : grade q β u => (a : QuantumMonoidAlgebra q β)) (hc.trans hs)⟩

/-- Completing the recovered finite positive coefficient returns the given completed element. -/
@[simp]
theorem toCompletion_finitePositiveCoefficientOfCompletion (x : (F).completion)
    (hx : Set.Finite {u | d.shiftedDirectLimitComponents (grade q β)
      (positiveCompletionToDirectLimit q β d x) u ≠ 0}) :
    (F).toCompletion (finitePositiveCoefficientOfCompletion q β d x hx) = x := by
  apply positiveCompletionToDirectLimit_injective q β d
  apply d.shiftedDirectLimitComponents_injective (grade q β)
  funext u
  rw [shiftedDirectLimitComponents_positiveCompletionToDirectLimit_toCompletion]
  exact d.decompose_finiteCoefficientOfShiftedDirectLimit (grade q β)
    (positiveCompletionToDirectLimit q β d x) hx u

/-- Ordinary positive coefficients are exactly the finite-support elements of their completion. -/
theorem mem_range_toCompletion_iff_finite_ambient_support (x : (F).completion) :
    x ∈ (F).toCompletion.range ↔
      Set.Finite {u | d.shiftedDirectLimitComponents (grade q β)
        (positiveCompletionToDirectLimit q β d x) u ≠ 0} := by
  constructor
  · rintro ⟨a, rfl⟩
    -- Expose the completion map value in the range witness.
    change Set.Finite {u | d.shiftedDirectLimitComponents (grade q β)
      (positiveCompletionToDirectLimit q β d ((F).toCompletion a)) u ≠ 0}
    simpa only [shiftedDirectLimitComponents_positiveCompletionToDirectLimit_toCompletion] using
      (DirectSum.decompose (grade q β) (a : QuantumMonoidAlgebra q β)).finite_support
  · intro hx
    exact ⟨finitePositiveCoefficientOfCompletion q β d x hx,
      toCompletion_finitePositiveCoefficientOfCompletion q β d x hx⟩

/-- Finite positive reconstruction returns every original positive coefficient unchanged. -/
@[simp]
theorem finitePositiveCoefficientOfCompletion_toCompletion
    (a : positiveSubalgebra q β d.monoid)
    (ha : Set.Finite {u | d.shiftedDirectLimitComponents (grade q β)
      (positiveCompletionToDirectLimit q β d ((F).toCompletion a)) u ≠ 0}) :
    finitePositiveCoefficientOfCompletion q β d ((F).toCompletion a) ha = a := by
  apply Subtype.ext
  apply (DirectSum.decompose (grade q β)).injective
  apply DFinsupp.ext
  intro u
  exact (d.decompose_finiteCoefficientOfShiftedDirectLimit (grade q β)
    (positiveCompletionToDirectLimit q β d ((F).toCompletion a)) ha u).trans
      (shiftedDirectLimitComponents_positiveCompletionToDirectLimit_toCompletion q β d a u)

end Mei.QuantumMonoidAlgebra
