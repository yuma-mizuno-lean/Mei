/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.Algebra.DirectSum.Map
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite support of homogeneous histories

A fixed input has only finitely many nonzero homogeneous propagation histories
along a finite sequence of linear maps, even when the grading set is infinite.
Their whole decorations sum to the original composite. Under an intertwining
regrading, each target history is the finite sum of its surviving source
refinements; neither the degree map nor its fibers need be finite.

This supplies finite coefficient-history sums for lattice-graded modules without
replacing their grading by a finite type. All statements are the constant-chain
cases of the expansion and regrading theorems for `chainHistory` in
`Mei.LinearAlgebra.GradedModule.History.Chain`, which allow the module and its
grading to change from step to step.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Only finitely many degree histories have nonzero whole decorations for a
fixed input and a finite sequence of linear maps. -/
theorem finite_support_homogeneousHistory {n : ℕ}
    (T : Fin n → Module.End R M) (a : M) :
    (Function.support (fun p => homogeneousHistory ℳ T p a)).Finite := by
  simp only [homogeneousHistory_eq_chainHistory]
  exact finite_support_chainHistory (fun _ => ℳ) T a

/-- The finite set of histories whose final whole decoration is nonzero.
Linearity ensures that every intermediate decoration is nonzero as well. -/
def homogeneousHistorySupport {n : ℕ} (T : Fin n → Module.End R M) (a : M) :
    Finset (Fin n → ι) :=
  chainHistorySupport (M := fun _ => M) (ι := fun _ => ι) (fun _ => ℳ) T a

/-- The support of a single-module history is the support of the constant chain. -/
theorem homogeneousHistorySupport_eq_chainHistorySupport {n : ℕ}
    (T : Fin n → Module.End R M) (a : M) :
    homogeneousHistorySupport ℳ T a =
      chainHistorySupport (M := fun _ => M) (ι := fun _ => ι) (fun _ => ℳ) T a :=
  (rfl)

/-- Membership retains precisely the histories with nonzero decoration. -/
@[simp]
theorem mem_homogeneousHistorySupport {n : ℕ} (T : Fin n → Module.End R M)
    (a : M) (p : Fin n → ι) :
    p ∈ homogeneousHistorySupport ℳ T a ↔ homogeneousHistory ℳ T p a ≠ 0 := by
  rw [homogeneousHistory_eq_chainHistory]
  exact mem_chainHistorySupport (fun _ => ℳ) T a p

/-- Zero input has no contributing histories. -/
@[simp]
theorem homogeneousHistorySupport_zero {n : ℕ} (T : Fin n → Module.End R M) :
    homogeneousHistorySupport ℳ T 0 = ∅ :=
  chainHistorySupport_zero (fun _ => ℳ) T

open Classical in
/-- Extend each contributing tail by precisely the nonzero output components
of the next linear map. Distinct tail histories remain distinct. -/
theorem homogeneousHistorySupport_succ {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (a : M) :
    homogeneousHistorySupport ℳ T a =
      (homogeneousHistorySupport ℳ (fun j : Fin n => T j.succ) a).biUnion fun p =>
        (DirectSum.decompose ℳ
          (T 0 (homogeneousHistory ℳ (fun j : Fin n => T j.succ) p a))).support.image
            (fun i => (Fin.cons i p : Fin (n + 1) → ι)) := by
  have h := chainHistorySupport_succ (fun _ => ℳ) T a
  simp only [← homogeneousHistory_eq_chainHistory,
    ← homogeneousHistorySupport_eq_chainHistorySupport] at h
  exact h

/-- Summing exactly the nonzero histories recovers the composite, without a
finite ambient degree type. -/
@[simp]
theorem sum_homogeneousHistory {n : ℕ}
    (T : Fin n → Module.End R M) (a : M) :
    ∑ p ∈ homogeneousHistorySupport ℳ T a, homogeneousHistory ℳ T p a =
      (List.ofFn T).prod a := by
  simp only [homogeneousHistory_eq_chainHistory, ← chainComp_const]
  exact sum_chainHistory (fun _ => ℳ) T a

section Regrading

variable {N κ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝓝 : κ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : ι → κ)
  (hr : ∀ i x, x ∈ ℳ i → r x ∈ 𝓝 (σ i))

include hr

open Classical in
/-- A target history is the finite sum of the images of its nonzero source
refinements. The source grading and the fibers of its degree map may be infinite. -/
theorem homogeneousHistory_map_eq_sum {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (q : Fin n → κ) (a : M) :
    homogeneousHistory 𝓝 U q (r a) =
      ∑ p ∈ homogeneousHistorySupport ℳ T a,
        if ∀ j, σ (p j) = q j then r (homogeneousHistory ℳ T p a) else 0 := by
  simp only [homogeneousHistory_eq_chainHistory]
  exact chainHistory_map_eq_sum (fun _ => ℳ) (fun _ => 𝓝) (fun _ => r) (fun _ => σ)
    (fun _ => hr) T U hT q a

open Classical in
/-- Refinements killed by specialization are omitted from the weighted sum.
The remaining finite set retains entire decorations, including all degree shifts
identified by the regrading. -/
theorem homogeneousHistory_map_eq_sum_surviving {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (q : Fin n → κ) (a : M) :
    homogeneousHistory 𝓝 U q (r a) =
      ∑ p ∈ (homogeneousHistorySupport ℳ T a).filter
          (fun p => (∀ j, σ (p j) = q j) ∧ r (homogeneousHistory ℳ T p a) ≠ 0),
        r (homogeneousHistory ℳ T p a) := by
  simp only [homogeneousHistory_eq_chainHistory]
  exact chainHistory_map_eq_sum_surviving (fun _ => ℳ) (fun _ => 𝓝) (fun _ => r)
    (fun _ => σ) (fun _ => hr) T U hT q a

/-- A nonzero target history admits a source refinement whose whole decoration
survives specialization, with no finiteness assumption on the grading. -/
theorem exists_homogeneousHistory_ne_zero_of_map_ne_zero {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (q : Fin n → κ) {a : M}
    (ha : homogeneousHistory 𝓝 U q (r a) ≠ 0) :
    ∃ p : Fin n → ι, (∀ j, σ (p j) = q j) ∧
      r (homogeneousHistory ℳ T p a) ≠ 0 := by
  simp only [homogeneousHistory_eq_chainHistory] at ha ⊢
  exact exists_chainHistory_ne_zero_of_map_ne_zero (fun _ => ℳ) (fun _ => 𝓝) (fun _ => r)
    (fun _ => σ) (fun _ => hr) T U hT q ha

open Classical in
/-- Selecting target histories commutes with coefficient change when source
histories are selected by their regraded history. Source histories with the same
image are added before vanishing target histories are discarded. -/
theorem map_sum_ite_homogeneousHistory {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (E : (Fin n → κ) → Prop) (a : M) :
    r (∑ p ∈ homogeneousHistorySupport ℳ T a,
      if E (σ ∘ p) then homogeneousHistory ℳ T p a else 0) =
      ∑ q ∈ homogeneousHistorySupport 𝓝 U (r a),
        if E q then homogeneousHistory 𝓝 U q (r a) else 0 := by
  simp only [homogeneousHistory_eq_chainHistory]
  exact map_sum_ite_chainHistory (fun _ => ℳ) (fun _ => 𝓝) (fun _ => r) (fun _ => σ)
    (fun _ => hr) T U hT E a

end Regrading

end Mei
