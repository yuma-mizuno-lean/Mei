/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Erasure
import Mathlib.Data.Finset.Max

/-!
# The last degree change of a homogeneous history

Suppose propagation fixes the same-degree component of every homogeneous input.
The encounters after the last degree change then preserve the whole decoration.
Decompose each history into its constant-degree contribution and the contribution
of its unique last change, retaining the whole incoming component at that change.
The formula uses only finite encounter indices, with no finiteness assumption on
the grading or basis assumption on its pieces.

Indices run backwards: the last change is the least index at which adjacent
recorded degrees differ. The construction uses `homogeneousHistoryStage` and
`homogeneousHistoryStage_castSucc_eq_succ_of_decompose_self`. For broken-line
recursions this is the coefficient decomposition underlying deletion of the last
positive-degree change in Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] {ℳ : ι → Submodule R M} [DirectSum.Decomposition ℳ]
  {n : ℕ} {T : Fin n → Module.End R M}
  (hT : ∀ j s x, x ∈ ℳ s → (DirectSum.decompose ℳ (T j x) s : M) = x)

include hT

open Classical in
/-- Partition a whole history by its last degree change. A constant-degree
history contributes its input; every other history contributes exactly the whole
output component at its unique last change, with its actual incoming decoration.
Encounters of equal spatial velocity are not identified. -/
theorem homogeneousHistory_eq_add_sum_last_degree_change
    (r : Fin n → ι) {r₀ : ι} (a : ℳ r₀) :
    homogeneousHistory ℳ T r a =
      (if ∀ j, r j = Fin.snoc (α := fun _ => ι) r r₀ j.succ then (a : M) else 0) +
        ∑ j : Fin n,
          if r j ≠ Fin.snoc (α := fun _ => ι) r r₀ j.succ ∧
              ∀ i, i < j → r i = Fin.snoc (α := fun _ => ι) r r₀ i.succ
          then (DirectSum.decompose ℳ
            (T j (homogeneousHistoryStage ℳ T r j.succ a)) (r j) : M) else 0 := by
  classical
  have hstage (j : Fin (n + 1))
      (hj : ∀ i : Fin n, i.castSucc < j →
        r i = Fin.snoc (α := fun _ => ι) r r₀ i.succ) :
      homogeneousHistory ℳ T r a = homogeneousHistoryStage ℳ T r j a := by
    induction j using Fin.inductionOn with
    | zero => simp
    | succ j ih =>
      exact (ih fun i hi => hj i (hi.trans Fin.castSucc_lt_succ)).trans
        (homogeneousHistoryStage_castSucc_eq_succ_of_decompose_self hT r a.property j
          (hj j Fin.castSucc_lt_succ))
  by_cases hall : ∀ j, r j = Fin.snoc (α := fun _ => ι) r r₀ j.succ
  · have he := hstage (Fin.last n)
      (fun i _ => hall i)
    simpa [hall] using he
  · let S := Finset.univ.filter fun j => r j ≠ Fin.snoc (α := fun _ => ι) r r₀ j.succ
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := not_forall.mp hall
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    let j := S.min' hS
    have hj : r j ≠ Fin.snoc (α := fun _ => ι) r r₀ j.succ :=
      (Finset.mem_filter.mp (S.min'_mem hS)).2
    have hbefore : ∀ i, i < j → r i = Fin.snoc (α := fun _ => ι) r r₀ i.succ := by
      intro i hi
      by_contra hne
      exact (not_le_of_gt hi) (S.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩))
    rw [ite_eq_right hall, zero_add, Finset.sum_eq_single j]
    · rw [ite_eq_left ⟨hj, hbefore⟩, ← homogeneousHistoryStage_castSucc_apply]
      exact hstage j.castSucc
        (fun i hi => hbefore i (by simpa using hi))
    · intro i _ hij
      rw [ite_eq_right]
      rintro ⟨hi, hprev⟩
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hi (hbefore i hlt)
      · exact hj (hprev j hgt)
    · simp

end Mei
