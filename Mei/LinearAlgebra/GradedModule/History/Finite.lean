/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite support of homogeneous histories

A fixed input has only finitely many nonzero homogeneous propagation histories
along a finite sequence of linear maps, even when the grading set is infinite.
Their whole decorations sum to the original composite. Under an intertwining
regrading, each target history is the finite sum of its surviving source
refinements; neither the degree map nor its fibers need be finite.

This supplies finite coefficient-history sums for lattice-graded modules without
replacing their grading by a finite type. The sequence `T` is the path
`Quiver.SingleObj.pathOfFn` through its positions in the one-object quiver on `Fin n`,
the arrow `j` carrying `T j` (`homogeneousHistory_eq_pathOfFn`). All statements are
transported from the expansion and regrading theorems for path histories in
`Mei.LinearAlgebra.GradedModule.History.Path` along `Quiver.SingleObj.degreesPathOfFn`.
-/

public noncomputable section

open Quiver

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- A sequence of endomorphisms as a path through its positions. -/
private abbrev positions (n : ℕ) : Path (SingleObj.star (Fin n)) (SingleObj.star (Fin n)) :=
  SingleObj.pathOfFn fun j => j

/-- A history along `T` is the path history along the positions of `T`. -/
private theorem homogeneousHistory_eq_positions {n : ℕ} (T : Fin n → Module.End R M)
    (p : Fin n → ι) :
    homogeneousHistory ℳ T p =
      (positions n).homogeneousHistory (M := fun _ => M) (fun j => T j) (fun _ => ℳ)
        (SingleObj.degreesPathOfFn ι (fun j : Fin n => j) p) :=
  homogeneousHistory_eq_pathOfFn ℳ T (fun j => j) p

/-- A path history along the positions of `T` is the history of the corresponding
function of degrees. -/
theorem homogeneousHistory_degreesPathOfFn_symm {n : ℕ} (T : Fin n → Module.End R M)
    (d : (SingleObj.pathOfFn fun j : Fin n => j).Degrees fun _ => ι) :
    homogeneousHistory ℳ T ((SingleObj.degreesPathOfFn ι (fun j : Fin n => j)).symm d) =
      (SingleObj.pathOfFn fun j : Fin n => j).homogeneousHistory (M := fun _ => M)
        (fun j => T j) (fun _ => ℳ) d := by
  rw [homogeneousHistory_eq_positions, Equiv.apply_symm_apply]

/-- The finite set of histories whose final whole decoration is nonzero.
Linearity ensures that every intermediate decoration is nonzero as well. -/
def homogeneousHistorySupport {n : ℕ} (T : Fin n → Module.End R M) (a : M) :
    Finset (Fin n → ι) :=
  ((positions n).historySupport (M := fun _ => M) (fun j => T j) (fun _ => ℳ) a).map
    (SingleObj.degreesPathOfFn ι (fun j : Fin n => j)).symm.toEmbedding

/-- The contributing histories along `T` are the contributing path histories along its
positions. -/
theorem homogeneousHistorySupport_eq_map {n : ℕ} (T : Fin n → Module.End R M) (a : M) :
    homogeneousHistorySupport ℳ T a =
      ((SingleObj.pathOfFn fun j : Fin n => j).historySupport (M := fun _ => M)
        (fun j => T j) (fun _ => ℳ) a).map
          (SingleObj.degreesPathOfFn ι (fun j : Fin n => j)).symm.toEmbedding :=
  (rfl)

private theorem sum_homogeneousHistorySupport {X : Type*} [AddCommMonoid X] {n : ℕ}
    (T : Fin n → Module.End R M) (a : M) (F : (Fin n → ι) → X) :
    ∑ p ∈ homogeneousHistorySupport ℳ T a, F p =
      ∑ d ∈ (positions n).historySupport (M := fun _ => M) (fun j => T j) (fun _ => ℳ) a,
        F ((SingleObj.degreesPathOfFn ι (fun j : Fin n => j)).symm d) := by
  rw [homogeneousHistorySupport_eq_map, Finset.sum_map]
  rfl

/-- Membership retains precisely the histories with nonzero decoration. -/
@[simp]
theorem mem_homogeneousHistorySupport {n : ℕ} (T : Fin n → Module.End R M)
    (a : M) (p : Fin n → ι) :
    p ∈ homogeneousHistorySupport ℳ T a ↔ homogeneousHistory ℳ T p a ≠ 0 := by
  rw [homogeneousHistorySupport, Finset.mem_map_equiv, Equiv.symm_symm,
    Path.mem_historySupport, homogeneousHistory_eq_positions]

/-- Only finitely many degree histories have nonzero whole decorations for a
fixed input and a finite sequence of linear maps. -/
theorem finite_support_homogeneousHistory {n : ℕ}
    (T : Fin n → Module.End R M) (a : M) :
    (Function.support (fun p => homogeneousHistory ℳ T p a)).Finite :=
  (homogeneousHistorySupport ℳ T a).finite_toSet.subset fun p hp =>
    (mem_homogeneousHistorySupport ℳ T a p).mpr hp

/-- Zero input has no contributing histories. -/
@[simp]
theorem homogeneousHistorySupport_zero {n : ℕ} (T : Fin n → Module.End R M) :
    homogeneousHistorySupport ℳ T 0 = ∅ := by
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
  ext q
  rw [mem_homogeneousHistorySupport, Finset.mem_biUnion]
  constructor
  · intro h
    refine ⟨fun j => q j.succ, (mem_homogeneousHistorySupport ..).mpr
      (homogeneousHistory_tail_ne_zero ℳ T q h), Finset.mem_image.mpr
        ⟨q 0, DFinsupp.mem_support_iff.mpr fun hz => h ?_, Fin.cons_self_tail q⟩⟩
    rw [homogeneousHistory_succ_apply, hz]
    rfl
  · rintro ⟨p, _, hy⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    rw [homogeneousHistory_succ_apply]
    simp only [Fin.cons_succ]
    exact fun hz => DFinsupp.mem_support_iff.mp hi (Subtype.val_injective hz)

/-- Summing exactly the nonzero histories recovers the composite, without a
finite ambient degree type. -/
@[simp]
theorem sum_homogeneousHistory {n : ℕ}
    (T : Fin n → Module.End R M) (a : M) :
    ∑ p ∈ homogeneousHistorySupport ℳ T a, homogeneousHistory ℳ T p a =
      (List.ofFn T).prod a := by
  simp only [sum_homogeneousHistorySupport, homogeneousHistory_degreesPathOfFn_symm,
    Path.sum_homogeneousHistory, composeLinear_pathOfFn]

section Regrading

variable {N κ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝓝 : κ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : ι → κ)
  (hr : ∀ i x, x ∈ ℳ i → r x ∈ 𝓝 (σ i))

omit [DecidableEq ι] [DecidableEq κ] in
/-- Transported degree histories agree with a target history exactly when the degree
map sends the source history to it at every position. -/
private theorem map_degreesPathOfFn_eq_iff {n : ℕ} (p : Fin n → ι) (q : Fin n → κ) :
    Path.Degrees.map (fun _ => σ) (positions n)
        (SingleObj.degreesPathOfFn ι (fun j : Fin n => j) p) =
      SingleObj.degreesPathOfFn κ (fun j : Fin n => j) q ↔ ∀ j, σ (p j) = q j := by
  rw [SingleObj.map_degreesPathOfFn, Equiv.apply_eq_iff_eq, funext_iff]
  rfl

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
  rw [homogeneousHistory_eq_positions, Path.homogeneousHistory_map_eq_sum
    (Q := SingleObj (Fin n)) (M := fun _ => M) (N := fun _ => N) (fun j => T j) (fun _ => ℳ)
    (fun j => U j) (fun _ => 𝓝) (fun _ => r) (fun _ => σ) (fun _ => hr) (fun j => hT j),
    sum_homogeneousHistorySupport]
  refine Finset.sum_congr rfl fun d _ => ?_
  obtain ⟨p, rfl⟩ := (SingleObj.degreesPathOfFn ι (fun j : Fin n => j)).surjective d
  rw [Equiv.symm_apply_apply, ← homogeneousHistory_eq_positions]
  exact if_congr (map_degreesPathOfFn_eq_iff σ p q) rfl rfl

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
  rw [homogeneousHistory_map_eq_sum ℳ 𝓝 r σ hr T U hT q a, ← Finset.sum_filter]
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
  have h := Path.map_sum_ite_homogeneousHistory (Q := SingleObj (Fin n)) (M := fun _ => M)
    (N := fun _ => N) (fun j => T j) (fun _ => ℳ) (fun j => U j) (fun _ => 𝓝) (fun _ => r)
    (fun _ => σ) (fun _ => hr) (fun j => hT j) (positions n)
    (fun d => E ((SingleObj.degreesPathOfFn κ (fun j : Fin n => j)).symm d)) a
  rw [sum_homogeneousHistorySupport, sum_homogeneousHistorySupport]
  simp only [homogeneousHistory_degreesPathOfFn_symm]
  convert h using 3 with d
  obtain ⟨p, rfl⟩ := (SingleObj.degreesPathOfFn ι (fun j : Fin n => j)).surjective d
  rw [Equiv.symm_apply_apply, SingleObj.map_degreesPathOfFn, Equiv.symm_apply_apply]

end Regrading

end Mei
