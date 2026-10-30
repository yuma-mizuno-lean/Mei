/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Finite homogeneous propagation histories

Insert a homogeneous projection after each map in a finite sequence of linear
endomorphisms. Each choice of intermediate degrees gives a linear map retaining
whole homogeneous decorations. The maps are indexed backwards: index zero is the
final operation, so the first operation is the rightmost factor. A nonzero final
decoration forces every intermediate decoration to be nonzero.
`homogeneousHistoryStage` records all segment decorations and their component
propagation equations, for attachment to geometric realizations.

The construction uses Mathlib's internal direct-sum decomposition and component
maps. The finite-support expansion and its regrading comparison are developed in
`Mei.LinearAlgebra.GradedModule.History.Finite`.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Propagation along a chosen homogeneous degree history. Index zero records
its final component; the empty history leaves the input unchanged. -/
def homogeneousHistory : {n : ℕ} → (Fin n → Module.End R M) →
    (Fin n → ι) → Module.End R M
  | 0, _, _ => LinearMap.id
  | n + 1, T, p =>
    ((ℳ (p 0)).subtype.comp
      ((DirectSum.component R ι (fun i => ℳ i) (p 0)).comp
        (DirectSum.decomposeLinearEquiv ℳ).toLinearMap)).comp
      ((T 0).comp (homogeneousHistory (fun j : Fin n => T j.succ) (fun j => p j.succ)))

/-- No propagation steps give the identity map. -/
@[simp]
theorem homogeneousHistory_zero (T : Fin 0 → Module.End R M) (p : Fin 0 → ι) :
    homogeneousHistory ℳ T p = LinearMap.id := (rfl)

/-- One more history entry applies its map and selects the entire output component. -/
@[simp]
theorem homogeneousHistory_succ_apply {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) (a : M) :
    homogeneousHistory ℳ T p a =
      (DirectSum.decompose ℳ (T 0
        (homogeneousHistory ℳ (fun j : Fin n => T j.succ) (fun j => p j.succ) a)) (p 0) : M) :=
  (rfl)

/-- The output of a nonempty history lies in its last selected homogeneous piece. -/
theorem homogeneousHistory_mem {n : ℕ} (T : Fin (n + 1) → Module.End R M)
    (p : Fin (n + 1) → ι) (a : M) :
    homogeneousHistory ℳ T p a ∈ ℳ (p 0) := by
  rw [homogeneousHistory_succ_apply]
  exact Subtype.property _

/-- A vanished intermediate decoration cannot yield a nonzero final history. -/
theorem homogeneousHistory_tail_ne_zero {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) {a : M}
    (ha : homogeneousHistory ℳ T p a ≠ 0) :
    homogeneousHistory ℳ (fun j : Fin n => T j.succ) (fun j => p j.succ) a ≠ 0 := by
  intro hz
  apply ha
  simp [hz]

/-- The whole decoration on every segment of a homogeneous history, in backward
order. The last segment carries the input, and segment zero carries the output. -/
def homogeneousHistoryStage : {n : ℕ} → (Fin n → Module.End R M) →
    (Fin n → ι) → Fin (n + 1) → Module.End R M
  | 0, _, _ => fun _ => LinearMap.id
  | n + 1, T, p => Fin.cons (homogeneousHistory ℳ T p)
      (homogeneousHistoryStage (fun j : Fin n => T j.succ) (fun j => p j.succ))

/-- The terminal segment carries the final whole component. -/
@[simp]
theorem homogeneousHistoryStage_zero {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) :
    homogeneousHistoryStage ℳ T p 0 = homogeneousHistory ℳ T p := by
  cases n <;> rfl

/-- Removing the terminal segment removes the last propagation step. -/
@[simp]
theorem homogeneousHistoryStage_succ {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p j.succ =
      homogeneousHistoryStage ℳ (fun j => T j.succ) (fun j => p j.succ) j := (rfl)

/-- The incoming segment carries the original input. -/
@[simp]
theorem homogeneousHistoryStage_last {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) :
    homogeneousHistoryStage ℳ T p (Fin.last n) = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun j => T j.succ) (fun j => p j.succ)

/-- At an encounter the entire output component of its propagation map is
retained. Adjacent segments may have the same degree. -/
theorem homogeneousHistoryStage_castSucc_apply {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) (j : Fin n) (a : M) :
    homogeneousHistoryStage ℳ T p j.castSucc a =
      (DirectSum.decompose ℳ (T j (homogeneousHistoryStage ℳ T p j.succ a)) (p j) : M) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.castSucc_zero, homogeneousHistoryStage_zero,
        homogeneousHistoryStage_succ] using homogeneousHistory_succ_apply ℳ T p a
    · exact ih (fun j => T j.succ) (fun j => p j.succ) j

/-- A surviving final decoration forces every segment decoration to survive. -/
theorem homogeneousHistoryStage_ne_zero {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) {a : M}
    (ha : homogeneousHistory ℳ T p a ≠ 0) (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p j a ≠ 0 := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    refine Fin.cases ha (fun j => ?_) j
    exact ih (fun j => T j.succ) (fun j => p j.succ)
      (homogeneousHistory_tail_ne_zero ℳ T p ha) j

/-- Every selected segment decoration lies in its recorded homogeneous piece. -/
theorem homogeneousHistoryStage_mem {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) (a : M) (j : Fin n) :
    homogeneousHistoryStage ℳ T p j.castSucc a ∈ ℳ (p j) := by
  rw [homogeneousHistoryStage_castSucc_apply]
  exact Subtype.property _

/-- All segment decorations are homogeneous in the recorded degrees, including
the incoming degree appended after the selected output degrees. -/
theorem homogeneousHistoryStage_mem_snoc {n : ℕ}
    (T : Fin n → Module.End R M) (p : Fin n → ι) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T p j a ∈ ℳ (Fin.snoc (α := fun _ => ι) p p₀ j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [Fin.snoc_last, homogeneousHistoryStage_last, LinearMap.id_apply] using a.property
  · simpa only [Fin.snoc_castSucc] using homogeneousHistoryStage_mem ℳ T p a i

end Mei
