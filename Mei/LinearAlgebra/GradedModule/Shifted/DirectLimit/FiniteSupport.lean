/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component

/-!
# Reconstructing finite global coefficient families

A global coefficient with finitely many nonzero ambient components determines
an ordinary graded module element with exactly those components. Reconstruction
is inverse to the ordinary coefficient inclusion and needs no multiplication.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

/-- Recover an ordinary graded coefficient from a global coefficient with finite support. -/
def finiteCoefficientOfShiftedDirectLimit (x : d.ShiftedDirectLimit ℳ)
    (hx : Set.Finite {u | d.shiftedDirectLimitComponents ℳ x u ≠ 0}) : M :=
  (DirectSum.decompose ℳ).symm
    (DFinsupp.mk hx.toFinset (fun u => d.shiftedDirectLimitComponents ℳ x u))

/-- Reconstruction preserves every ambient homogeneous component. -/
@[simp]
theorem decompose_finiteCoefficientOfShiftedDirectLimit (x : d.ShiftedDirectLimit ℳ)
    (hx : Set.Finite {u | d.shiftedDirectLimitComponents ℳ x u ≠ 0}) (u : Γ) :
    DirectSum.decompose ℳ (d.finiteCoefficientOfShiftedDirectLimit ℳ x hx) u =
      d.shiftedDirectLimitComponents ℳ x u := by
  classical
  simp only [finiteCoefficientOfShiftedDirectLimit, Equiv.apply_symm_apply, DFinsupp.mk_apply,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  split_ifs with hu
  · rfl
  · exact (not_not.mp hu).symm

/-- Reconstruction is the finite sum of all nonzero ambient homogeneous pieces. -/
theorem finiteCoefficientOfShiftedDirectLimit_eq_sum (x : d.ShiftedDirectLimit ℳ)
    (hx : Set.Finite {u | d.shiftedDirectLimitComponents ℳ x u ≠ 0}) :
    d.finiteCoefficientOfShiftedDirectLimit ℳ x hx =
      ∑ u ∈ hx.toFinset, (d.shiftedDirectLimitComponents ℳ x u : M) := by
  classical
  have hs : (DirectSum.decompose ℳ (d.finiteCoefficientOfShiftedDirectLimit ℳ x hx)).support =
      hx.toFinset := by
    ext u
    simp only [DFinsupp.mem_support_iff, decompose_finiteCoefficientOfShiftedDirectLimit,
      Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have h := (DirectSum.sum_support_decompose ℳ
    (d.finiteCoefficientOfShiftedDirectLimit ℳ x hx)).symm
  simpa only [hs, decompose_finiteCoefficientOfShiftedDirectLimit] using h

end Mei.PositiveDegrees
