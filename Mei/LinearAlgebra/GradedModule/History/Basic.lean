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

end Mei
