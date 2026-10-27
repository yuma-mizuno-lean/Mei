/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata

/-!
# Chambers incident to a wall

At a relative interior point of a wall in a finite polyhedral complex covering
a neighborhood of that point, each transverse ray enters the relative interior
of a unique full-dimensional cell. The two opposite rays enter distinct cells, both having
the original wall as a facet. Thus a short transverse crossing determines the
two chamber cells on which endpoint data for a wall crossing are evaluated.

The construction uses `FinitePolyhedralComplex.exists_isolating_ball` to exclude
all other cells of positive codimension, `IsExposed.eq_of_finrank_vectorSpan_eq`
to identify the common facet, and Mathlib's convexity theorem for open segments
from relative interior points. Unbounded cells, lineality and
arbitrary real offsets are allowed.
-/

public section

namespace Mei.FinitePolyhedralComplex

open Set Mei.Convex Filter Topology

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Two distinct cells with a common facet meet exactly in that facet.
The dimension condition is relative, so the cells need not be full dimensional. -/
theorem inter_eq_of_common_facet (C : FinitePolyhedralComplex h)
    {P Q Q' : Set V} (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hQ' : Q' ∈ C.cells)
    (hPQ : P ⊆ Q) (hPQ' : P ⊆ Q') (hne : Q ≠ Q')
    (hdim : Module.finrank ℝ (affineSpan ℝ Q).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction + 1)
    (hdim' : Module.finrank ℝ (affineSpan ℝ Q').direction =
      Module.finrank ℝ (affineSpan ℝ P).direction + 1) : Q ∩ Q' = P := by
  let := h.finiteDimensional
  have hPI : P ⊆ Q ∩ Q' := subset_inter hPQ hPQ'
  have hIne := (C.nonempty P hP).mono hPI
  have hI := C.inter_mem_cells hQ hQ' hIne
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le
    (affineSpan_mono ℝ inter_subset_left : affineSpan ℝ (Q ∩ Q') ≤ affineSpan ℝ Q))
  have hlt : Module.finrank ℝ (affineSpan ℝ (Q ∩ Q')).direction <
      Module.finrank ℝ (affineSpan ℝ Q).direction := by
    apply lt_of_le_of_ne hle
    intro he
    have heQ := (C.inter_face Q hQ Q' hQ' hIne).eq_of_finrank_vectorSpan_eq hIne
      (by rw [← direction_affineSpan, ← direction_affineSpan]; exact he)
    have heQ' := (isPolyhedralFace_iff.mp (C.face_of_subset hI hQ' inter_subset_right)).2
      |>.eq_of_finrank_vectorSpan_eq hIne
        (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)
    exact hne (heQ.symm.trans heQ')
  have hge := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hPI))
  exact ((isPolyhedralFace_iff.mp (C.face_of_subset hP hI hPI)).2.eq_of_finrank_vectorSpan_eq
    (C.nonempty P hP) (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)).symm

/-- A transverse ray from a wall's relative interior enters a unique
full-dimensional cell containing the wall, provided the complex covers a
neighborhood of the starting point. Every sufficiently short positive
part of the ray is in that cell's relative interior. -/
theorem existsUnique_cell_of_transverse_ray (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.walls) {q v : V}
    (hq : q ∈ intrinsicInterior ℝ P) (hcover : q ∈ interior C.support)
    (hv : v ∉ (affineSpan ℝ P).direction) :
    ∃! Q : Set V, Q ∈ C.cellsOfCodimension 0 ∧ P ⊆ Q ∧
      ∃ ε > 0, ∀ t ∈ Ioo (0 : ℝ) ε, q + t • v ∈ intrinsicInterior ℝ Q := by
  let := h.finiteDimensional
  obtain ⟨r, hr, hskel, _, _, hinc⟩ := C.exists_isolating_ball hP hq
  have htend : Tendsto (fun t : ℝ => q + t • v) (𝓝 0) (𝓝 q) := by
    have hc : Continuous (fun t : ℝ => q + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.tendsto 0
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp
    (htend.eventually (inter_mem (Metric.ball_mem_nhds q hr)
      (mem_interior_iff_mem_nhds.mp hcover)))
  let a := δ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hyball : q + a • v ∈ Metric.ball q r ∩ C.support := hδball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha]
    dsimp [a]
    linarith)
  -- Away from the wall, the isolating ball misses the entire positive-codimension skeleton.
  have hynP : q + a • v ∉ P := by
    intro hy
    have hdir := (affineSpan ℝ P).vsub_mem_direction
      (subset_affineSpan ℝ P hy) (subset_affineSpan ℝ P (intrinsicInterior_subset hq))
    have hasmul : a • v ∈ (affineSpan ℝ P).direction := by simpa using hdir
    exact hv ((Submodule.smul_mem_iff _ (ne_of_gt ha)).mp hasmul)
  have hynskel : q + a • v ∉ (C.codimensionAtLeast 1).support := by
    intro hy
    exact hynP ((Set.ext_iff.mp hskel _).mp ⟨hyball.1, hy⟩).2
  obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp hyball.2
  have hdimle := Submodule.finrank_le (affineSpan ℝ Q).direction
  have hdim : Module.finrank ℝ (affineSpan ℝ Q).direction = Module.finrank ℝ V := by
    by_contra hne
    exact hynskel (mem_support.mpr ⟨Q,
      (C.mem_codimensionAtLeast_cells 1 Q).mpr ⟨hQ, by omega⟩, hyQ⟩)
  have hyint : q + a • v ∈ intrinsicInterior ℝ Q := by
    rw [← intrinsicClosure_sdiff_intrinsicFrontier]
    refine ⟨subset_intrinsicClosure hyQ, fun hyfr => hynskel ?_⟩
    exact C.intrinsicFrontier_subset_support_codimensionAtLeast hQ 0
      (by omega) hyfr
  have hPQ := hinc Q hQ ⟨q + a • v, hyball.1, hyQ⟩
  -- Convexity extends this one interior point to the whole shorter ray.
  have hshort : ∀ t ∈ Ioo (0 : ℝ) a, q + t • v ∈ intrinsicInterior ℝ Q := by
    intro t ht
    apply Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      (C.isConvexPolyhedron hQ).convex
        hyint (subset_intrinsicClosure (hPQ (intrinsicInterior_subset hq)))
    rw [openSegment_symm]
    have he := lineMap_mem_openSegment ℝ q (q + a • v)
      ⟨div_pos ht.1 ha, (div_lt_one ha).mpr ht.2⟩
    simpa [AffineMap.lineMap_apply_module', smul_smul, ha.ne', add_comm] using he
  refine ⟨Q, ⟨(C.mem_cellsOfCodimension 0 Q).mpr ⟨hQ, by simpa using hdim⟩,
    hPQ, a, ha, hshort⟩, ?_⟩
  rintro Q' ⟨hQ', _, ε, hε, hshort'⟩
  have hb : 0 < min a ε / 2 := by positivity
  have hba : min a ε / 2 < a := by have := min_le_left a ε; linarith
  have hbε : min a ε / 2 < ε := by have := min_le_right a ε; linarith
  exact C.eq_of_mem_intrinsicInterior ((C.mem_cellsOfCodimension 0 Q').mp hQ').1 hQ
    (hshort' _ ⟨hb, hbε⟩) (hshort _ ⟨hb, hba⟩)

/-- A short transverse crossing of a wall has two distinct full-dimensional
incident cells meeting exactly in that wall, provided the complex covers a
neighborhood of the crossing point. The same cells work for every sufficiently
small crossing length. -/
theorem exists_transverse_wall_chambers (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.walls) {q v : V}
    (hq : q ∈ intrinsicInterior ℝ P) (hcover : q ∈ interior C.support)
    (hv : v ∉ (affineSpan ℝ P).direction) :
    ∃ Qminus ∈ C.cellsOfCodimension 0, ∃ Qplus ∈ C.cellsOfCodimension 0,
      Qminus ≠ Qplus ∧ Qminus ∩ Qplus = P ∧
      ∃ ε > 0, ∀ t ∈ Ioo (0 : ℝ) ε,
        q - t • v ∈ intrinsicInterior ℝ Qminus ∧
        q + t • v ∈ intrinsicInterior ℝ Qplus := by
  let := h.finiteDimensional
  obtain ⟨Qplus, ⟨hQplus, hPplus, εplus, hεplus, hshortplus⟩, _⟩ :=
    C.existsUnique_cell_of_transverse_ray hP hq hcover hv
  have hneg : -v ∉ (affineSpan ℝ P).direction := by simpa using hv
  obtain ⟨Qminus, ⟨hQminus, hPminus, εminus, hεminus, hshortminus⟩, _⟩ :=
    C.existsUnique_cell_of_transverse_ray hP hq hcover hneg
  have hshort : ∀ t ∈ Ioo (0 : ℝ) (min εminus εplus),
      q - t • v ∈ intrinsicInterior ℝ Qminus ∧
      q + t • v ∈ intrinsicInterior ℝ Qplus := by
    intro t ht
    refine ⟨?_, hshortplus t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩⟩
    simpa only [smul_neg, sub_eq_add_neg] using
      hshortminus t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hne : Qminus ≠ Qplus := by
    intro heq
    obtain ⟨hminus, hplus⟩ := hshort (min εminus εplus / 2) (by
      have := lt_min hεminus hεplus
      constructor <;> linarith)
    rw [heq] at hminus
    have hqint : q ∈ intrinsicInterior ℝ Qplus :=
      Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        (C.isConvexPolyhedron ((C.mem_cellsOfCodimension 0 Qplus).mp hQplus).1).convex
          hminus (subset_intrinsicClosure (intrinsicInterior_subset hplus))
          (_root_.mem_openSegment_sub_add (𝕜 := ℝ) q _)
    have hQP := C.subset_of_mem_intrinsicInterior
      ((C.mem_cellsOfCodimension 0 Qplus).mp hQplus).1 (C.mem_cells_of_mem_walls hP)
      hqint (intrinsicInterior_subset hq)
    have hdimQ := ((C.mem_cellsOfCodimension 0 Qplus).mp hQplus).2
    have hdimP := C.finrank_direction_add_one_of_mem_walls hP
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hQP))
    omega
  refine ⟨Qminus, hQminus, Qplus, hQplus, hne, ?_,
    min εminus εplus, lt_min hεminus hεplus, hshort⟩
  apply C.inter_eq_of_common_facet (C.mem_cells_of_mem_walls hP)
    ((C.mem_cellsOfCodimension 0 Qminus).mp hQminus).1
    ((C.mem_cellsOfCodimension 0 Qplus).mp hQplus).1 hPminus hPplus hne
  all_goals
    have hdimP := C.finrank_direction_add_one_of_mem_walls hP
    have hdimMinus := ((C.mem_cellsOfCodimension 0 Qminus).mp hQminus).2
    have hdimPlus := ((C.mem_cellsOfCodimension 0 Qplus).mp hQplus).2
    omega

end Mei.FinitePolyhedralComplex
