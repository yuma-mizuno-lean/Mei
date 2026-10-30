/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic

/-!
# Erasing a propagation step that fixes its decoration

A homogeneous propagation history retains its final weight when a step with
equal incoming and outgoing decorations is omitted. The two shorter tuples are
obtained by `Fin.removeNth`, so all other maps and selected degrees retain their
order. No homogeneity or nonvanishing assumption on the incoming decoration is
needed. This is an algebraic contraction of the coefficient history, independent
of any geometric realization of its encounters.

We use `homogeneousHistoryStage` and its component-propagation equations.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Omitting a step whose whole decoration is unchanged preserves the final
weight of a homogeneous history. No other map or selected degree is changed. -/
theorem homogeneousHistory_removeNth {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (r : Fin (n + 1) → ι) (a : M)
    (j : Fin (n + 1))
    (hfix : homogeneousHistoryStage ℳ T r j.castSucc a =
      homogeneousHistoryStage ℳ T r j.succ a) :
    homogeneousHistory ℳ T r a =
      homogeneousHistory ℳ (j.removeNth T) (j.removeNth r) a := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simpa only [Fin.castSucc_zero, homogeneousHistoryStage_zero,
      homogeneousHistoryStage_succ, homogeneousHistoryStage_last,
      homogeneousHistory_zero, LinearMap.id_apply] using hfix
  | succ n ih =>
    revert hfix
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hfix
      simpa only [Fin.castSucc_zero, homogeneousHistoryStage_zero,
        homogeneousHistoryStage_succ, homogeneousHistoryStage_zero,
        Fin.removeNth_zero, Fin.tail_def] using hfix
    · intro hfix
      have htail : homogeneousHistoryStage ℳ (fun i => T i.succ)
          (fun i => r i.succ) j.castSucc a =
        homogeneousHistoryStage ℳ (fun i => T i.succ)
          (fun i => r i.succ) j.succ a := by
        simpa only [← Fin.succ_castSucc, homogeneousHistoryStage_succ] using hfix
      conv_lhs => rw [homogeneousHistory_succ_apply]
      conv_rhs => rw [homogeneousHistory_succ_apply]
      simp only [Fin.removeNth, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      rw [ih (fun i => T i.succ) (fun i => r i.succ) j htail]
      rfl

end Mei
