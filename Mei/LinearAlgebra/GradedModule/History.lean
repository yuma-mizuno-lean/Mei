/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.Map
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Finite homogeneous propagation histories

Insert a homogeneous projection after each map in a finite sequence of linear
endomorphisms. Each choice of intermediate degrees gives a linear map retaining
whole homogeneous decorations. Summing these history maps recovers the original
composite. The maps are indexed backwards: index zero is the final operation,
so the first operation is the rightmost factor.

Under an intertwining coefficient map that regrades homogeneous pieces, a target
history is the sum of the images of its source refinements. The degree map may
identify degrees and the coefficient map may kill decorations. This is the
algebraic weighted comparison needed when projecting decorated paths to a coarser
grading. Finite degree types model the retained pieces at a fixed cutoff;
no finiteness or freeness of the homogeneous modules is required.

The construction uses Mathlib's internal direct-sum decomposition and
`Fin.consEquiv`; the one-step regrading formula is
`DirectSum.decompose_map_eq_sum`.
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

section Finite

variable [Fintype ι]

/-- Summing all homogeneous histories recovers the original ordered composite.
There is no restriction on which components or intermediate sums vanish. -/
theorem sum_homogeneousHistory {n : ℕ} (T : Fin n → Module.End R M) (a : M) :
    ∑ p : Fin n → ι, homogeneousHistory ℳ T p a = (List.ofFn T).prod a := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
      (fun (p : ι × (Fin n → ι)) => homogeneousHistory ℳ T (Fin.cons p.1 p.2) a) _ (fun _ => rfl),
      Fintype.sum_prod_type, Finset.sum_comm]
    simp only [homogeneousHistory_succ_apply, Fin.cons_succ]
    have hsum (x : M) : ∑ i, (DirectSum.decompose ℳ x i : M) = x := by
      calc
        _ = ∑ i ∈ (DirectSum.decompose ℳ x).support,
            (DirectSum.decompose ℳ x i : M) :=
          (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
            have hz := DFinsupp.notMem_support_iff.mp hi
            simp [hz]).symm
        _ = x := DirectSum.sum_support_decompose ℳ x
    trans ∑ p : Fin n → ι, T 0 (homogeneousHistory ℳ (fun j => T j.succ) p a)
    · exact Finset.sum_congr rfl fun p _ => hsum _
    · rw [← map_sum, ih, List.ofFn_succ, List.prod_cons]
      rfl

section Regrading

variable {N κ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝓝 : κ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : ι → κ)
  (hr : ∀ i x, x ∈ ℳ i → r x ∈ 𝓝 (σ i))

include hr

/-- Under an intertwining regrading, the weight of one target history is the
sum of the images of all its source refinements. Neither injectivity of the
coefficient map nor injectivity or surjectivity of the degree map is needed. -/
theorem homogeneousHistory_map_eq_sum {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (q : Fin n → κ) (a : M) :
    homogeneousHistory 𝓝 U q (r a) =
      ∑ p : Fin n → ι, if ∀ j, σ (p j) = q j then
        r (homogeneousHistory ℳ T p a) else 0 := by
  classical
  have hcomponent (x : M) (j : κ) :
      (DirectSum.decompose 𝓝 (r x) j : N) =
        ∑ i, if σ i = j then r (DirectSum.decompose ℳ x i : M) else 0 := by
    have he := DirectSum.decompose_map_eq_sum ℳ 𝓝 r.toAddMonoidHom σ hr x j
    simp only [LinearMap.toAddMonoidHom_coe, Finset.sum_filter] at he
    refine he.trans ?_
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz := DFinsupp.notMem_support_iff.mp hi
    simp [hz]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [homogeneousHistory_succ_apply,
      ih (fun j : Fin n => T j.succ) (fun j => U j.succ) (fun j => hT j.succ)]
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
      (fun (p : ι × (Fin n → ι)) => if ∀ j, σ ((Fin.cons p.1 p.2 : Fin (n + 1) → ι) j) = q j then
        r (homogeneousHistory ℳ T (Fin.cons p.1 p.2) a) else 0) _ (fun _ => rfl),
      Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      homogeneousHistory_succ_apply]
    simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply]
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : ∀ j : Fin n, σ (p j) = q j.succ
    · simp only [hp, implies_true, and_true, ↓reduceIte]
      have hcomm := LinearMap.congr_fun (hT 0)
        (homogeneousHistory ℳ (fun j : Fin n => T j.succ) p a)
      simp only [LinearMap.comp_apply] at hcomm
      rw [← hcomm]
      exact hcomponent _ _
    · simp [hp]

open Classical in
/-- Only refinements whose whole final decoration survives the coefficient map
contribute to a target history. Zero source histories are also omitted, without
choosing basis coordinates or scalar representatives. -/
theorem homogeneousHistory_map_eq_sum_surviving {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (q : Fin n → κ) (a : M) :
    homogeneousHistory 𝓝 U q (r a) =
      ∑ p ∈ (Finset.univ : Finset (Fin n → ι)) with (∀ j, σ (p j) = q j) ∧
          r (homogeneousHistory ℳ T p a) ≠ 0,
        r (homogeneousHistory ℳ T p a) := by
  classical
  rw [homogeneousHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a, ← Finset.sum_filter]
  simpa only [Finset.filter_filter] using
    (Finset.sum_filter_ne_zero
      (f := fun p => r (homogeneousHistory ℳ T p a))
      (Finset.univ.filter fun p : Fin n → ι => ∀ j, σ (p j) = q j)).symm

omit [Fintype ι] in
/-- A nonzero target history has a source refinement with a surviving whole
weight. Several such refinements may contribute, and their weights may cancel. -/
theorem exists_homogeneousHistory_ne_zero_of_map_ne_zero [Finite ι] {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (q : Fin n → κ) {a : M}
    (ha : homogeneousHistory 𝓝 U q (r a) ≠ 0) :
    ∃ p : Fin n → ι, (∀ j, σ (p j) = q j) ∧
      r (homogeneousHistory ℳ T p a) ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  rw [homogeneousHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a] at ha
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  split_ifs at hp with h
  · exact ⟨p, h, hp⟩
  · exact (hp rfl).elim

end Regrading

end Finite

end Mei
