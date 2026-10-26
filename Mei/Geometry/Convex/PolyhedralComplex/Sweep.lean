/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Polyhedron.Rational.Sweep
public import Mei.Geometry.Convex.Sweep.Face

/-!
# Sweeps of finite polyhedral complexes

A finite complex contained in a transverse affine subspace has a prism complex:
retain its base cells and add their negative-ray sweeps. Its support is the sweep
of the original support. Its cells of codimension `k` are the base cells of
codimension `k` and the swept cells of codimension `k + 1`. Subdivision of the
base induces subdivision of the prism. This supplies actual polyhedral
subdivisions for descending geometric sweep operations through subdivision relations.

The construction uses `IsExposed.exists_base_or_sweep` and
`IsExposed.sweep_of_transverse` from `Mei.Geometry.Convex.Sweep.Face`, together
with the rational-normal sweep presentations in
`Mei.Geometry.Convex.Polyhedron.Rational.Sweep`. Cells may be unbounded and have
lineality. Transversality is to the affine direction of the entire base support,
so swept cells cannot acquire new intersections away from their base intersections.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The prism complex consists of the original cells and their negative-ray
sweeps along a lattice vector transverse to the entire base support. -/
def sweep (C : FinitePolyhedralComplex h) (n : N)
    (hn : i n ∉ vectorSpan ℝ C.support) : FinitePolyhedralComplex h := by
  classical
  let := h.finiteDimensional
  have hcell {P : Set V} (hP : P ∈ C.cells) : P ⊆ C.support :=
    fun x hx => mem_support.mpr ⟨P, hP, hx⟩
  have hnP {P : Set V} (hP : P ∈ C.cells) : i n ∉ vectorSpan ℝ P :=
    fun hm => hn (vectorSpan_mono ℝ (hcell hP) hm)
  have hnPQ {P Q : Set V} (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) :
      i n ∉ vectorSpan ℝ (P ∪ Q) :=
    fun hm => hn (vectorSpan_mono ℝ (union_subset (hcell hP) (hcell hQ)) hm)
  refine {
    cells := C.cells ∪ C.cells.image (fun P => Mei.Convex.sweep P (i n))
    nonempty := ?_
    rational := ?_
    face_closed := ?_
    inter_face := ?_ }
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact C.nonempty P hP
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      exact sweep_nonempty (C.nonempty Q hQ) (i n)
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact C.rational P hP
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      convert (C.rational Q hQ).negRay n using 1
      ext y
      simp only [mem_sweep_iff_exists, mem_ofPred_eq]
      constructor
      · rintro ⟨x, hx, t, ht, rfl⟩
        exact ⟨t, ht, by simpa using hx⟩
      · rintro ⟨t, ht, hx⟩
        exact ⟨y + t • i n, hx, t, ht, by abel⟩
  · intro P hP F hF
    obtain ⟨hFne, hF⟩ := isPolyhedralFace_iff.mp hF
    rcases Finset.mem_union.mp hP with hP | hP
    · exact Finset.mem_union_left _ (C.face_closed P hP F (isPolyhedralFace_iff.mpr ⟨hFne, hF⟩))
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨G, hGne, hG, he⟩ := hF.exists_base_or_sweep hFne
      have hGc := C.face_closed Q hQ G (isPolyhedralFace_iff.mpr ⟨hGne, hG⟩)
      rcases he with rfl | rfl
      · exact Finset.mem_union_left _ hGc
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨G, hGc, rfl⟩)
  · intro P hP Q hQ hne
    -- Base/base, base/side, side/base and side/side intersections reduce to
    -- intersections in the base complex, where the common-face axiom applies.
    rcases Finset.mem_union.mp hP with hP | hP <;>
      rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact C.inter_face P hP Q hQ hne
    · obtain ⟨Q, hQc, rfl⟩ := Finset.mem_image.mp hQ
      rw [inter_sweep_of_transverse (hnPQ hP hQc)] at hne ⊢
      exact C.inter_face P hP Q hQc hne
    · obtain ⟨P, hPc, rfl⟩ := Finset.mem_image.mp hP
      have he : Mei.Convex.sweep P (i n) ∩ Q = P ∩ Q := by
        rw [inter_comm, inter_sweep_of_transverse (hnPQ hQ hPc), inter_comm]
      rw [he] at hne ⊢
      exact (C.inter_face P hPc Q hQ hne).in_sweep_of_transverse (hnP hPc)
    · obtain ⟨P, hPc, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q, hQc, rfl⟩ := Finset.mem_image.mp hQ
      rw [Mei.Convex.sweep_inter (hnPQ hPc hQc)] at hne ⊢
      obtain ⟨y, hy⟩ := hne
      obtain ⟨x, hx, t, ht, he⟩ := mem_sweep_iff_exists.mp hy
      exact (C.inter_face P hPc Q hQc ⟨x, hx⟩).sweep_of_transverse (hnP hPc)

/-- A prism cell is either a base cell or the sweep of a base cell. -/
@[simp]
theorem mem_sweep_cells {C : FinitePolyhedralComplex h} {n : N}
    {hn : i n ∉ vectorSpan ℝ C.support} {P : Set V} :
    P ∈ (C.sweep n hn).cells ↔
      P ∈ C.cells ∨ ∃ Q ∈ C.cells, Mei.Convex.sweep Q (i n) = P := by
  classical
  simp only [sweep, Finset.mem_union, Finset.mem_image]

/-- The prism complex has exactly the swept support. -/
@[simp]
theorem support_sweep (C : FinitePolyhedralComplex h) (n : N)
    (hn : i n ∉ vectorSpan ℝ C.support) :
    (C.sweep n hn).support = Mei.Convex.sweep C.support (i n) := by
  ext y
  constructor
  · intro hy
    obtain ⟨P, hP, hyP⟩ := mem_support.mp hy
    rcases mem_sweep_cells.mp hP with hP | ⟨Q, hQ, rfl⟩
    · exact subset_sweep C.support (i n) (mem_support.mpr ⟨P, hP, hyP⟩)
    · exact sweep_mono (fun x hx => mem_support.mpr ⟨Q, hQ, hx⟩) (i n) hyP
  · intro hy
    obtain ⟨x, hx, t, ht, rfl⟩ := mem_sweep_iff_exists.mp hy
    obtain ⟨P, hP, hxP⟩ := mem_support.mp hx
    exact mem_support.mpr ⟨Mei.Convex.sweep P (i n),
      mem_sweep_cells.mpr (Or.inr ⟨P, hP, rfl⟩),
      mem_sweep_iff_exists.mpr ⟨x, hxP, t, ht, rfl⟩⟩

/-- The codimension-`k` prism cells are the codimension-`k` base cells and the
sweeps of codimension-`k + 1` base cells. In particular this identifies the
walls and joints that a transverse sweep creates. -/
theorem mem_sweep_cellsOfCodimension {C : FinitePolyhedralComplex h} {n : N}
    {hn : i n ∉ vectorSpan ℝ C.support} (k : ℕ) (P : Set V) :
    P ∈ (C.sweep n hn).cellsOfCodimension k ↔
      P ∈ C.cellsOfCodimension k ∨
        ∃ Q ∈ C.cellsOfCodimension (k + 1), Mei.Convex.sweep Q (i n) = P := by
  let := h.finiteDimensional
  have hdim {Q : Set V} (hQ : Q ∈ C.cells) :
      Module.finrank ℝ (affineSpan ℝ (Mei.Convex.sweep Q (i n))).direction =
        Module.finrank ℝ (affineSpan ℝ Q).direction + 1 := by
    rw [direction_affineSpan, direction_affineSpan]
    exact finrank_sweep (C.nonempty Q hQ) (fun hm => hn (vectorSpan_mono ℝ
      (fun x hx => mem_support.mpr ⟨Q, hQ, hx⟩) hm))
  simp only [mem_cellsOfCodimension, mem_sweep_cells]
  constructor
  · rintro ⟨hP | ⟨Q, hQ, rfl⟩, hd⟩
    · exact Or.inl ⟨hP, hd⟩
    · exact Or.inr ⟨Q, ⟨hQ, by rw [hdim hQ] at hd; omega⟩, rfl⟩
  · rintro (⟨hP, hd⟩ | ⟨Q, ⟨hQ, hd⟩, rfl⟩)
    · exact ⟨Or.inl hP, hd⟩
    · exact ⟨Or.inr ⟨Q, hQ, rfl⟩, by rw [hdim hQ]; omega⟩

/-- Sweeping a weak refinement produces a weak refinement of prism complexes. -/
theorem IsWeakRefinement.sweep {C D : FinitePolyhedralComplex h}
    (hCD : C.IsWeakRefinement D) (n : N)
    (hn : i n ∉ vectorSpan ℝ D.support) :
    (C.sweep n (fun hm => hn (vectorSpan_mono ℝ hCD.support_subset hm))).IsWeakRefinement
      (D.sweep n hn) := by
  apply isWeakRefinement_iff.mpr
  have href := isWeakRefinement_iff.mp hCD
  intro P hP
  rcases mem_sweep_cells.mp hP with hP | ⟨Q, hQ, rfl⟩
  · obtain ⟨Q, hQ, hPQ⟩ := href P hP
    exact ⟨Q, mem_sweep_cells.mpr (Or.inl hQ), hPQ⟩
  · obtain ⟨R, hR, hQR⟩ := href Q hQ
    exact ⟨Mei.Convex.sweep R (i n),
      mem_sweep_cells.mpr (Or.inr ⟨R, hR, rfl⟩), sweep_mono hQR (i n)⟩

/-- Subdivision of a transverse base induces subdivision of its swept prism,
including all base and side faces. -/
theorem IsSubdivision.sweep {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) (n : N)
    (hn : i n ∉ vectorSpan ℝ D.support) :
    (C.sweep n (fun hm => hn (vectorSpan_mono ℝ
      (isSubdivision_iff.mp hCD).1.support_subset hm))).IsSubdivision (D.sweep n hn) := by
  obtain ⟨href, hsupport⟩ := isSubdivision_iff.mp hCD
  exact isSubdivision_iff.mpr ⟨href.sweep n hn, by simp [hsupport]⟩

end Mei.FinitePolyhedralComplex
