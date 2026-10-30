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
replacing their grading by a finite type. It uses `homogeneousHistory`, Mathlib's
finite homogeneous supports and `DirectSum.sum_support_decompose`, and the
one-step regrading formula `DirectSum.decompose_map_eq_sum`.
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
  classical
  induction n with
  | zero => exact Set.toFinite _
  | succ n ih =>
    let T' := fun j : Fin n => T j.succ
    let S := (ih T').toFinset
    let B := fun p => (DirectSum.decompose ℳ (T 0 (homogeneousHistory ℳ T' p a))).support
    have hfinite : (↑(S.biUnion fun p => (B p).image (fun i => (Fin.cons i p : Fin (n + 1) → ι))) :
        Set (Fin (n + 1) → ι)).Finite := Finset.finite_toSet _
    apply hfinite.subset
    intro p hp
    have ht : homogeneousHistory ℳ T' (fun j => p j.succ) a ≠ 0 :=
      homogeneousHistory_tail_ne_zero ℳ T p hp
    have hc : p 0 ∈ B (fun j => p j.succ) := by
      apply DFinsupp.mem_support_iff.mpr
      intro he
      have hp' : homogeneousHistory ℳ T p a ≠ 0 := hp
      apply hp'
      rw [homogeneousHistory_succ_apply]
      exact congrArg Subtype.val he
    apply Finset.mem_biUnion.mpr
    refine ⟨fun j => p j.succ, ?_, ?_⟩
    · exact (Set.Finite.mem_toFinset _).mpr ht
    · exact Finset.mem_image.mpr ⟨p 0, hc, Fin.cons_self_tail p⟩

open Classical in
/-- The finite set of histories whose final whole decoration is nonzero.
Linearity ensures that every intermediate decoration is nonzero as well. -/
def homogeneousHistorySupport {n : ℕ} (T : Fin n → Module.End R M) (a : M) :
    Finset (Fin n → ι) :=
  (finite_support_homogeneousHistory ℳ T a).toFinset

/-- Membership retains precisely the histories with nonzero decoration. -/
@[simp]
theorem mem_homogeneousHistorySupport {n : ℕ} (T : Fin n → Module.End R M)
    (a : M) (p : Fin n → ι) :
    p ∈ homogeneousHistorySupport ℳ T a ↔ homogeneousHistory ℳ T p a ≠ 0 := by
  classical
  exact Set.Finite.mem_toFinset _

/-- Zero input has no contributing histories. -/
@[simp]
theorem homogeneousHistorySupport_zero {n : ℕ} (T : Fin n → Module.End R M) :
    homogeneousHistorySupport ℳ T 0 = ∅ := by
  classical
  ext p
  simp

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
  classical
  ext p
  simp only [mem_homogeneousHistorySupport, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro hp
    refine ⟨fun j => p j.succ, homogeneousHistory_tail_ne_zero ℳ T p hp, p 0, ?_,
      Fin.cons_self_tail p⟩
    rw [homogeneousHistory_succ_apply] at hp
    exact DFinsupp.mem_support_iff.mpr (fun he => hp (congrArg Subtype.val he))
  · rintro ⟨q, _, i, hi, rfl⟩
    rw [homogeneousHistory_succ_apply]
    intro hz
    apply DFinsupp.mem_support_iff.mp hi
    exact Subtype.val_injective hz

open Classical in
private theorem homogeneousHistorySupport_extensions_disjoint {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (a : M) :
    Set.PairwiseDisjoint
      (↑(homogeneousHistorySupport ℳ (fun j : Fin n => T j.succ) a) : Set (Fin n → ι))
      (fun p => (DirectSum.decompose ℳ
        (T 0 (homogeneousHistory ℳ (fun j : Fin n => T j.succ) p a))).support.image
          (fun i => (Fin.cons i p : Fin (n + 1) → ι))) := by
  classical
  intro p _ q _ hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, he⟩ := Finset.mem_image.mp hy
  exact hpq (Fin.cons_inj.mp he).2.symm

/-- Summing exactly the nonzero histories recovers the composite, without a
finite ambient degree type. -/
@[simp]
theorem sum_homogeneousHistory {n : ℕ}
    (T : Fin n → Module.End R M) (a : M) :
    ∑ p ∈ homogeneousHistorySupport ℳ T a, homogeneousHistory ℳ T p a =
      (List.ofFn T).prod a := by
  classical
  induction n with
  | zero =>
    by_cases ha : a = 0
    · simp [ha]
    · have hs : homogeneousHistorySupport ℳ T a = {fun j => Fin.elim0 j} := by
        ext p
        simp [ha, Subsingleton.elim p (fun j => Fin.elim0 j)]
      simp [hs]
  | succ n ih =>
    rw [homogeneousHistorySupport_succ, Finset.sum_biUnion]
    · trans ∑ p ∈ homogeneousHistorySupport ℳ (fun j : Fin n => T j.succ) a,
          T 0 (homogeneousHistory ℳ (fun j : Fin n => T j.succ) p a)
      · apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_image]
        · simp only [homogeneousHistory_succ_apply, Fin.cons_succ]
          exact DirectSum.sum_support_decompose ℳ _
        · intro i _ j _ hij
          exact (Fin.cons_inj.mp hij).1
      · rw [← map_sum, ih, List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    · exact homogeneousHistorySupport_extensions_disjoint ℳ T a

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
  classical
  induction n with
  | zero =>
    simp only [Fin.forall_fin_zero, ↓reduceIte]
    rw [← map_sum, sum_homogeneousHistory]
    simp
  | succ n ih =>
    rw [homogeneousHistory_succ_apply,
      ih (fun j : Fin n => T j.succ) (fun j => U j.succ) (fun j => hT j.succ)]
    simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    rw [homogeneousHistorySupport_succ, Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_image]
      · simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
          homogeneousHistory_succ_apply]
        by_cases hp : ∀ j : Fin n, σ (p j) = q j.succ
        · simp only [hp, implies_true, and_true, ↓reduceIte]
          have hcomm := LinearMap.congr_fun (hT 0)
            (homogeneousHistory ℳ (fun j : Fin n => T j.succ) p a)
          simp only [LinearMap.comp_apply] at hcomm
          rw [← hcomm]
          have h := DirectSum.decompose_map_eq_sum ℳ 𝓝 r.toAddMonoidHom σ hr
            (T 0 (homogeneousHistory ℳ (fun j : Fin n => T j.succ) p a)) (q 0)
          rw [Finset.sum_filter] at h
          exact h
        · simp [hp]
      · intro i _ j _ hij
        exact (Fin.cons_inj.mp hij).1
    · exact homogeneousHistorySupport_extensions_disjoint ℳ T a

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
  classical
  rw [homogeneousHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a,
    ← Finset.sum_filter]
  simpa only [Finset.filter_filter] using
    (Finset.sum_filter_ne_zero (f := fun p => r (homogeneousHistory ℳ T p a))
      ((homogeneousHistorySupport ℳ T a).filter fun p => ∀ j, σ (p j) = q j)).symm

/-- A nonzero target history admits a source refinement whose whole decoration
survives specialization, with no finiteness assumption on the grading. -/
theorem exists_homogeneousHistory_ne_zero_of_map_ne_zero {n : ℕ}
    (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
    (hT : ∀ j, r.comp (T j) = (U j).comp r)
    (q : Fin n → κ) {a : M}
    (ha : homogeneousHistory 𝓝 U q (r a) ≠ 0) :
    ∃ p : Fin n → ι, (∀ j, σ (p j) = q j) ∧
      r (homogeneousHistory ℳ T p a) ≠ 0 := by
  classical
  rw [homogeneousHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a] at ha
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  split_ifs at hp with h
  · exact ⟨p, h, hp⟩
  · exact (hp rfl).elim

end Regrading

end Mei
