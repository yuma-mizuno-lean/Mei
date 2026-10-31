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

When every map fixes the same-degree component of each homogeneous input, an
encounter with equal adjacent degrees fixes its decoration, and a history of
constant degree fixes its input.

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
      rw [ih (fun i => T i.succ) (fun i => r i.succ) j htail]
      have hT : j.removeNth (fun i => T i.succ) = fun i => j.succ.removeNth T i.succ := by
        funext i
        simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ]
      have hr : j.removeNth (fun i => r i.succ) = fun i => j.succ.removeNth r i.succ := by
        funext i
        simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ]
      rw [hT, hr, Fin.removeNth_apply, Fin.removeNth_apply, Fin.succ_succAbove_zero]

section DecomposeSelf

variable {ℳ} {n : ℕ} {T : Fin n → Module.End R M}
  (hT : ∀ j s x, x ∈ ℳ s → (DirectSum.decompose ℳ (T j x) s : M) = x)
include hT

/-- If every map fixes the same-degree component of each homogeneous input,
an encounter whose two recorded degrees coincide leaves the whole decoration
unchanged. The incoming segment has degree `r₀`. -/
theorem homogeneousHistoryStage_castSucc_eq_succ_of_decompose_self
    (r : Fin n → ι) {r₀ : ι} {a : M} (ha : a ∈ ℳ r₀) (j : Fin n)
    (hj : r j = Fin.snoc (α := fun _ => ι) r r₀ j.succ) :
    homogeneousHistoryStage ℳ T r j.castSucc a = homogeneousHistoryStage ℳ T r j.succ a := by
  rw [homogeneousHistoryStage_castSucc_apply]
  apply hT
  rw [hj]
  exact homogeneousHistoryStage_mem_snoc ℳ T r r₀ ⟨a, ha⟩ j.succ

/-- If every map fixes the same-degree component of each homogeneous input,
every segment of a constant-degree history carries its incoming decoration. -/
theorem homogeneousHistoryStage_const_of_decompose_self {r : ι} {a : M} (ha : a ∈ ℳ r)
    (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T (fun _ => r) j a = a := by
  induction j using Fin.reverseInduction with
  | last => simp only [homogeneousHistoryStage_last, LinearMap.id_apply]
  | cast j ih =>
    rw [homogeneousHistoryStage_castSucc_eq_succ_of_decompose_self hT (fun _ => r) ha j (by
      refine Fin.lastCases ?_ (fun i => ?_) j.succ <;> simp), ih]

/-- If every map fixes the same-degree component of each homogeneous input,
a constant-degree history fixes its input. -/
theorem homogeneousHistory_const_of_decompose_self {r : ι} {a : M} (ha : a ∈ ℳ r) :
    homogeneousHistory ℳ T (fun _ => r) a = a := by
  simpa only [homogeneousHistoryStage_zero] using
    homogeneousHistoryStage_const_of_decompose_self hT ha 0

end DecomposeSelf

end Mei
