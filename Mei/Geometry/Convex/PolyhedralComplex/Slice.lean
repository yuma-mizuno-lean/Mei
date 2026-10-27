/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Affine.Transverse

/-!
# Isolated encounters of affine slices with polyhedral skeleta

A subset of an affine slice transverse to the cells of codimension `k` that it
meets, and avoiding the codimension-at-least-`k + 1` skeleton, meets the
codimension-at-least-`k` skeleton in finitely many isolated points. These points
admit pairwise disjoint balls in which the slice meets the skeleton at the center
alone. Every cell meeting such a ball contains the center's supporting cell.

For `k = 2`, this isolates the joint encounters of a transverse polygonal
filling avoiding the higher skeleton. The slice and its subset need not be
bounded, closed or full dimensional. Real offsets, unbounded cells and
lineality are allowed.

The results use `AffineSubspace.subsingleton_inter_of_disjoint_direction`,
`FinitePolyhedralComplex.exists_isolating_ball`, and Mathlib's
`Set.Finite.t2_separation`.
-/

public section

open Set Module

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

variable {k : ℕ}

/-- A subset of an affine slice transverse to all exact-codimension cells it
meets, and missing the next skeleton, has only finitely many encounters with
the skeleton. The slice need not be bounded or closed, and disjoint cells
impose no transversality condition. -/
theorem finite_inter_support_codimensionAtLeast (C : FinitePolyhedralComplex h)
    (A : AffineSubspace ℝ V) {S : Set V} (hSA : S ⊆ A)
    (hnext : Disjoint S (C.codimensionAtLeast (k + 1)).support)
    (htrans : ∀ P ∈ C.cellsOfCodimension k, (S ∩ P).Nonempty →
      Disjoint A.direction (affineSpan ℝ P).direction) :
    (S ∩ (C.codimensionAtLeast k).support).Finite := by
  have hfinite : (⋃ P ∈ C.cellsOfCodimension k, S ∩ P).Finite :=
    (C.cellsOfCodimension k).finite_toSet.biUnion fun P hP => by
      by_cases hmeet : (S ∩ P).Nonempty
      · exact ((A.subsingleton_inter_of_disjoint_direction (affineSpan ℝ P)
          (htrans P hP hmeet)).anti fun x (hx : x ∈ S ∩ P) =>
            ⟨hSA hx.1, subset_affineSpan ℝ P hx.2⟩).finite
      · exact (Set.not_nonempty_iff_eq_empty.mp hmeet) ▸ Set.finite_empty
  apply hfinite.subset
  rintro x ⟨hxS, hx⟩
  obtain ⟨P, hP, _⟩ := C.existsUnique_mem_cellsOfCodimension_of_notMem_succ hx
    (hnext.notMem_of_mem_left hxS)
  exact Set.mem_iUnion₂.mpr ⟨P, hP.1, hxS, intrinsicInterior_subset hP.2⟩

/-- Near a relative interior point of a cell, a slice with disjoint tangent
direction meets the cell's skeleton at exactly that point. Every cell of the
complex meeting the same ball contains the supporting cell. -/
theorem exists_ball_inter_slice_support_eq_singleton (C : FinitePolyhedralComplex h)
    (A : AffineSubspace ℝ V) {P : Set V} (hP : P ∈ C.cellsOfCodimension k)
    {x : V} (hx : x ∈ intrinsicInterior ℝ P) (hxA : x ∈ A)
    (htrans : Disjoint A.direction (affineSpan ℝ P).direction) :
    ∃ r > 0,
      Metric.ball x r ∩ ((A : Set V) ∩ (C.codimensionAtLeast k).support) = {x} ∧
      ∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → P ⊆ Q := by
  obtain ⟨r, hr, hlocal, _, _, hincident⟩ := C.exists_isolating_ball hP hx
  have hsub := A.subsingleton_inter_of_disjoint_direction (affineSpan ℝ P) htrans
  have hxP : x ∈ P := intrinsicInterior_subset hx
  have hxs : x ∈ (C.codimensionAtLeast k).support :=
    mem_support.mpr ⟨P, C.cellsOfCodimension_subset_codimensionAtLeast_cells k hP, hxP⟩
  refine ⟨r, hr, Set.Subset.antisymm ?_ ?_, hincident⟩
  · rintro y ⟨hyball, hyA, hys⟩
    have hyP := (Set.ext_iff.mp hlocal y).mp ⟨hyball, hys⟩
    exact Set.mem_singleton_iff.mpr (hsub ⟨hyA, subset_affineSpan ℝ P hyP.2⟩
      ⟨hxA, subset_affineSpan ℝ P hxP⟩)
  · rintro y (rfl : y = x)
    exact ⟨Metric.mem_ball_self hr, hxA, hxs⟩

/-- The finitely many encounters of a transverse slice with a skeleton admit
pairwise disjoint isolating balls. Each ball meets the sliced skeleton in its
center alone, and its incident cells contain the unique supporting cell.
For codimension two these are disjoint neighborhoods of the joint encounters
of a filling that avoids the higher skeleton. -/
theorem exists_pairwiseDisjoint_isolating_balls (C : FinitePolyhedralComplex h)
    (A : AffineSubspace ℝ V) {S : Set V} (hSA : S ⊆ A)
    (hnext : Disjoint S (C.codimensionAtLeast (k + 1)).support)
    (htrans : ∀ P ∈ C.cellsOfCodimension k, (S ∩ P).Nonempty →
      Disjoint A.direction (affineSpan ℝ P).direction) :
    ∃ r : (S ∩ (C.codimensionAtLeast k).support : Set V) → ℝ,
      Pairwise (fun (x y : (S ∩ (C.codimensionAtLeast k).support : Set V)) =>
        Disjoint (Metric.ball (x : V) (r x)) (Metric.ball (y : V) (r y))) ∧
      ∀ x, 0 < r x ∧
        Metric.ball (x : V) (r x) ∩ ((A : Set V) ∩ (C.codimensionAtLeast k).support) = {x.val} ∧
        ∃ P ∈ C.cellsOfCodimension k, x.val ∈ intrinsicInterior ℝ P ∧
          ∀ Q ∈ C.cells, (Metric.ball (x : V) (r x) ∩ Q).Nonempty → P ⊆ Q := by
  classical
  let E := S ∩ (C.codimensionAtLeast k).support
  obtain ⟨U, hU, hdisj⟩ :=
    (C.finite_inter_support_codimensionAtLeast A hSA hnext htrans).t2_separation
  have hlocal (x : V) (hx : x ∈ E) : ∃ r > 0,
      Metric.ball x r ⊆ U x ∧
      Metric.ball x r ∩ ((A : Set V) ∩ (C.codimensionAtLeast k).support) = {x} ∧
      ∃ P ∈ C.cellsOfCodimension k, x ∈ intrinsicInterior ℝ P ∧
        ∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → P ⊆ Q := by
    obtain ⟨P, hP, _⟩ := C.existsUnique_mem_cellsOfCodimension_of_notMem_succ hx.2
      (hnext.notMem_of_mem_left hx.1)
    obtain ⟨δ, hδ, heq, hinc⟩ := C.exists_ball_inter_slice_support_eq_singleton A
      hP.1 hP.2 (hSA hx.1) (htrans P hP.1 ⟨x, hx.1, intrinsicInterior_subset hP.2⟩)
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp (hU x).2 x (hU x).1
    have hball : Metric.ball x (min δ ε) ⊆ Metric.ball x δ :=
      Metric.ball_subset_ball (min_le_left δ ε)
    refine ⟨min δ ε, lt_min hδ hε,
      (Metric.ball_subset_ball (min_le_right δ ε)).trans hεU,
      Set.Subset.antisymm ?_ ?_, P, hP.1, hP.2, ?_⟩
    · exact (Set.inter_subset_inter_left _ hball).trans heq.subset
    · rintro y (rfl : y = x)
      exact ⟨Metric.mem_ball_self (lt_min hδ hε), hSA hx.1, hx.2⟩
    · intro Q hQ hmeet
      exact hinc Q hQ (hmeet.mono (Set.inter_subset_inter_left _ hball))
  choose r hr using fun x : E => hlocal x x.property
  refine ⟨r, ?_, fun x => ⟨(hr x).1, (hr x).2.2⟩⟩
  intro x y hxy
  exact (hdisj x.property y.property (Subtype.val_injective.ne hxy)).mono
    (hr x).2.1 (hr y).2.1

end Mei.FinitePolyhedralComplex
