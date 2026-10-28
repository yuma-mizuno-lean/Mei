/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Itinerary
public import Mei.Geometry.Affine.Arrangement

/-!
# Discriminants of backward endpoint domains

Pull the support inequalities back along the affine encounter maps and combine
them with the elapsed-time conditions. Their nonconstant zero sets form a finite
exceptional arrangement. Away from it, strict and weak endpoint membership are
locally constant. Every frontier point of the strict domain, and every zero-time
limit of strict realizations, belongs to the exceptional locus.

These statements concern the selected support incidences and time order. They do
not assert avoidance of other walls or of singular supports. Such conditions can
be added as further affine conditions. Constant rows are retained in membership
tests but omitted from the arrangement, so redundant zero rows do not remove all
generic endpoints.

We reuse the backward propagation maps, `ExceptionalArrangement.ofAffineForms`,
and Mathlib's sign comparisons and neighborhood characterizations of interior.
-/

public section

noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → V)
  {m : Fin n → ℕ} (g : ∀ i, Fin (m i) → V →ᴬ[ℝ] ℝ)

/-- The discriminant of the selected itinerary and presented supports. It omits
constant endpoint conditions, including identically zero support rows. -/
def backwardDiscriminant : ExceptionalArrangement V :=
  ExceptionalArrangement.ofAffineForms (fun j => (backwardCondition f c v g j).toAffineMap)

/-- The backward discriminant is the arrangement of the affine endpoint conditions. -/
theorem backwardDiscriminant_def :
    backwardDiscriminant f c v g = ExceptionalArrangement.ofAffineForms
      (fun j => (backwardCondition f c v g j).toAffineMap) := (rfl)

/-- Genericity is nonvanishing of each nonconstant endpoint condition. -/
@[simp]
theorem isGeneric_backwardDiscriminant_iff (Q : V) :
    (backwardDiscriminant f c v g).IsGeneric Q ↔
      ∀ j, (backwardCondition f c v g j).toAffineMap.linear ≠ 0 →
        backwardCondition f c v g j Q ≠ 0 := by
  simp only [backwardDiscriminant, ExceptionalArrangement.isGeneric_ofAffineForms_iff,
    ContinuousAffineMap.coe_toAffineMap]

private theorem backwardDomain_mem_iff_of_sign_eq {Q Q' : V}
    (h : ∀ j, SignType.sign (backwardCondition f c v g j Q') =
      SignType.sign (backwardCondition f c v g j Q)) :
    (Q' ∈ backwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0}) ↔
      Q ∈ backwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0})) ∧
    (Q' ∈ weakBackwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0}) ↔
      Q ∈ weakBackwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0})) := by
  have ht (i : Fin n) :
      (0 < backwardTime f c v i Q' ↔ 0 < backwardTime f c v i Q) ∧
      (0 ≤ backwardTime f c v i Q' ↔ 0 ≤ backwardTime f c v i Q) := by
    have hi := h (.inl i)
    simp only [backwardCondition_time] at hi
    constructor
    · simpa only [sign_eq_neg_one_iff, neg_lt_zero] using
        iff_of_eq (congrArg (fun s : SignType => s = -1) hi)
    · simpa only [sign_nonpos_iff, neg_nonpos] using
        iff_of_eq (congrArg (fun s : SignType => s ≤ 0) hi)
  have hs (i : Fin n) (j : Fin (m i)) :
      (g i j (backwardPoint f c v i.succ Q') ≤ 0 ↔
        g i j (backwardPoint f c v i.succ Q) ≤ 0) := by
    have hi := h (.inr ⟨i, j⟩)
    simp only [backwardCondition_support] at hi
    simpa only [sign_nonpos_iff] using iff_of_eq (congrArg (fun s : SignType => s ≤ 0) hi)
  simp only [mem_backwardDomain, mem_weakBackwardDomain, Set.mem_ofPred_eq]
  exact ⟨forall_congr' fun i => and_congr (ht i).1 (forall_congr' (hs i)),
    forall_congr' fun i => and_congr (ht i).2 (forall_congr' (hs i))⟩

/-- A generic endpoint has a neighborhood on which membership in both the strict
and weak selected-itinerary domains is unchanged. No transversality or
nonemptiness hypothesis is needed; tangent steps make the strict domain empty. -/
theorem eventually_backwardDomain_mem_iff {Q : V}
    (hQ : (backwardDiscriminant f c v g).IsGeneric Q) :
    ∀ᶠ Q' in 𝓝 Q,
      (Q' ∈ backwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0}) ↔
        Q ∈ backwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0})) ∧
      (Q' ∈ weakBackwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0}) ↔
        Q ∈ weakBackwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0})) := by
  exact (ExceptionalArrangement.eventually_sign_eq_of_isGeneric
    (backwardCondition f c v g) hQ).mono fun _ h => backwardDomain_mem_iff_of_sign_eq f c v g h

/-- Every frontier point of the strict endpoint domain lies on a nonconstant
endpoint condition. This includes lower-dimensional and empty domains. -/
theorem not_isGeneric_backwardDiscriminant_of_mem_frontier {Q : V}
    (hQ : Q ∈ frontier (backwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0}))) :
    ¬ (backwardDiscriminant f c v g).IsGeneric Q := by
  intro hgen
  have he := (eventually_backwardDomain_mem_iff f c v g hgen).mono fun _ h => h.1
  by_cases hm : Q ∈ backwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0})
  · have hi := mem_interior_iff_mem_nhds.mpr (he.mono fun _ h => h.mpr hm)
    exact (mem_interior_iff_notMem_frontier hm).mp hi hQ
  · have hi : Q ∈ interior (backwardDomain f c v
        (fun i => {x | ∀ j, g i j x ≤ 0}))ᶜ :=
      mem_interior_iff_mem_nhds.mpr (he.mono fun _ h => mt h.mp hm)
    have hn := (mem_interior_iff_notMem_frontier hm).mp hi
    exact hn (by rwa [frontier_compl])

/-- A zero-duration limit of strict realizations lies in the exceptional locus,
even if other endpoint conditions vanish identically. -/
theorem not_isGeneric_backwardDiscriminant_of_time_eq_zero {Q : V}
    (hQ : Q ∈ closure (backwardDomain f c v (fun i => {x | ∀ j, g i j x ≤ 0})))
    (i : Fin n) (hi : backwardTime f c v i Q = 0) :
    ¬ (backwardDiscriminant f c v g).IsGeneric Q := by
  apply not_isGeneric_backwardDiscriminant_of_mem_frontier f c v g
  refine ⟨hQ, ?_⟩
  intro hint
  have hm := interior_subset hint
  have ht := (mem_backwardDomain _ _ _ _ Q).mp hm i
  rw [hi] at ht
  exact (lt_irrefl 0) ht.1

end Mei.Convex
