/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Positive.Basic
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Support

/-!
# Positive completion as the positive global coefficient subalgebra

The positive completed quantum algebra maps onto exactly the global coefficients
supported in the positive monoid. Combining this image description with its
existing injectivity gives an algebra equivalence with the positive coefficient
subalgebra. This identification allows arbitrary bilinear forms and does not
require positive differences to span the ambient group.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => d.ShiftedDirectLimit (grade q β)

/-- The positive completion image is exactly the positive global coefficient subalgebra. -/
theorem range_positiveCompletionToDirectLimit :
    (positiveCompletionToDirectLimit q β d).range =
      d.positiveCoefficientSubalgebra (grade q β) := by
  ext x
  -- Subalgebra membership is membership in its underlying submodule.
  change x ∈ (positiveCompletionToDirectLimit q β d).range ↔
    x ∈ (d.positiveCoefficientSubalgebra (grade q β)).toSubmodule
  rw [PositiveDegrees.positiveCoefficientSubalgebra_toSubmodule]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨positiveCompletionShiftEquiv q β d 0 a,
      (positiveCompletionToDirectLimit_apply q β d a).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨(positiveCompletionShiftEquiv q β d 0).symm a, ?_⟩
    -- The range witness is the underlying value of the inverse algebra equivalence.
    change positiveCompletionToDirectLimit q β d
      ((positiveCompletionShiftEquiv q β d 0).symm a) = x
    rw [positiveCompletionToDirectLimit_apply, LinearEquiv.apply_symm_apply]
    exact ha

/-- Global coefficients come from the positive completion exactly when their support is positive. -/
theorem mem_range_positiveCompletionToDirectLimit_iff (x : G) :
    x ∈ (positiveCompletionToDirectLimit q β d).range ↔
      ∀ u, u ∉ d.monoid → d.shiftedDirectLimitComponents (grade q β) x u = 0 := by
  rw [range_positiveCompletionToDirectLimit, PositiveDegrees.mem_positiveCoefficientSubalgebra_iff]

/-- The completed positive algebra is the positive-support subalgebra of global coefficients. -/
def positiveCompletionEquivPositiveCoefficients :
    (F).completion ≃ₐ[R] d.positiveCoefficientSubalgebra (grade q β) :=
  (AlgEquiv.ofInjective (positiveCompletionToDirectLimit q β d)
    (positiveCompletionToDirectLimit_injective q β d)).trans
      (Subalgebra.equivOfEq _ _ (range_positiveCompletionToDirectLimit q β d))

/-- The equivalence to the positive subalgebra has the original global embedding as its value. -/
@[simp]
theorem coe_positiveCompletionEquivPositiveCoefficients (a : (F).completion) :
    (positiveCompletionEquivPositiveCoefficients q β d a : G) =
      positiveCompletionToDirectLimit q β d a := by
  -- This application only projects the defining map record and its unchanged underlying function.
  rfl

/-- Recovering a positive completion and embedding it globally returns the original coefficient. -/
@[simp]
theorem positiveCompletionToDirectLimit_equiv_symm
    (x : d.positiveCoefficientSubalgebra (grade q β)) :
    positiveCompletionToDirectLimit q β d
        ((positiveCompletionEquivPositiveCoefficients q β d).symm x) = (x : G) := by
  rw [← coe_positiveCompletionEquivPositiveCoefficients, AlgEquiv.apply_symm_apply]

end Mei.QuantumMonoidAlgebra
