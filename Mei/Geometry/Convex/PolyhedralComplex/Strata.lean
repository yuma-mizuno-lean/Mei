/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Basic
public import Mei.Geometry.Convex.Polyhedron.SingularSupport
public import Mei.Geometry.Convex.Polyhedron.Face
import Mei.Geometry.Affine.Transverse

/-!
# Walls, joints and regular points of finite polyhedral complexes

Filter actual cell carriers by their ambient codimension. Walls have codimension
one, joints have codimension two, and the cells of codimension at least `k` form
a subcomplex. The singular support of the wall family is contained in the
codimension-at-least-two subcomplex. Outside singular support a point belongs
to at most one wall, so a transverse crossing has an unambiguous wall index.
The difference of successive skeleta is partitioned by the relative interiors
of the exact-codimension cells.

Near a relative interior point, the skeleton of the same or greater codimension
agrees with that cell. One ball isolates it from its boundary and all other cells
of the same codimension, while meeting only cells containing it.

A set meeting a joint, with affine direction disjoint from the joint direction,
meets the skeleton at exactly one point in a region meeting only cells incident
to that joint. This supplies the isolation conditions for transverse triangular loops.
All cells may be unbounded and may have lineality.

## References

* Mathlib's `IsExposed` common-face condition and relative interiors.
* Mei's `Mei.Convex.intrinsicFrontier_eq_iUnion_active` and
  `AffineMap.finrank_direction_inter_zero_lt`.
* Mei's `AffineSubspace.finrank_direction_inf_add_one_lt`.
* Mei's `AffineSubspace.subsingleton_inter_of_disjoint_direction`.
-/

public section

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The finite collection of cells of ambient codimension exactly `k`. -/
noncomputable def cellsOfCodimension (C : FinitePolyhedralComplex h) (k : ℕ) :
    Finset (Set V) := by
  classical
  exact C.cells.filter fun P =>
    Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V

/-- Membership records both the original cell and its exact codimension. -/
@[simp]
theorem mem_cellsOfCodimension (C : FinitePolyhedralComplex h) (k : ℕ) (P : Set V) :
    P ∈ C.cellsOfCodimension k ↔ P ∈ C.cells ∧
      Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V := by
  classical
  simp [cellsOfCodimension]

/-- Walls are the codimension-one cells. -/
noncomputable abbrev walls (C : FinitePolyhedralComplex h) : Finset (Set V) :=
  C.cellsOfCodimension 1

/-- Every wall is a cell of the complex. -/
theorem mem_cells_of_mem_walls (C : FinitePolyhedralComplex h) {P : Set V}
    (hP : P ∈ C.walls) : P ∈ C.cells :=
  ((C.mem_cellsOfCodimension 1 P).mp hP).1

/-- The direction dimension of a wall is one less than the ambient dimension. -/
theorem finrank_direction_add_one_of_mem_walls (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.walls) :
    Module.finrank ℝ (affineSpan ℝ P).direction + 1 = Module.finrank ℝ V :=
  ((C.mem_cellsOfCodimension 1 P).mp hP).2

/-- A wall contained in a set whose affine span also has codimension one has the
same affine span as that set. -/
theorem affineSpan_eq_of_mem_walls_subset (C : FinitePolyhedralComplex h)
    {Q S : Set V} (hQ : Q ∈ C.walls) (hQS : Q ⊆ S)
    (hS : Module.finrank ℝ (affineSpan ℝ S).direction + 1 = Module.finrank ℝ V) :
    affineSpan ℝ Q = affineSpan ℝ S := by
  have := h.finiteDimensional
  have hle := affineSpan_mono ℝ hQS
  have hQ' := C.finrank_direction_add_one_of_mem_walls hQ
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) (by omega))
    ((C.nonempty Q (C.mem_cells_of_mem_walls hQ)).mono (subset_affineSpan ℝ Q)) hle

/-- Contained walls in two finite complexes have the same affine span. -/
theorem affineSpan_eq_of_walls_subset {C D : FinitePolyhedralComplex h} (Q : C.walls) (P : D.walls)
    (hQP : (Q : Set V) ⊆ P) :
    affineSpan ℝ (Q : Set V) = affineSpan ℝ (P : Set V) :=
  C.affineSpan_eq_of_mem_walls_subset Q.property hQP
    (D.finrank_direction_add_one_of_mem_walls P.property)

/-- A complement to the affine direction of a subset of a wall is transverse
to that wall. No dimension hypothesis on the subset is required. -/
theorem not_le_wall_direction_of_isCompl (C : FinitePolyhedralComplex h)
    {J P : Set V} (hJP : J ⊆ P) (hP : P ∈ C.walls) {T : Submodule ℝ V}
    (hT : IsCompl (affineSpan ℝ J).direction T) :
    ¬ T ≤ (affineSpan ℝ P).direction := by
  have := h.finiteDimensional
  intro hle
  have hJle := AffineSubspace.direction_le (affineSpan_mono ℝ hJP)
  have htop : (affineSpan ℝ P).direction = ⊤ := by
    apply top_unique
    rw [← hT.sup_eq_top]
    exact sup_le hJle hle
  have hdim := C.finrank_direction_add_one_of_mem_walls hP
  rw [htop, finrank_top] at hdim
  omega

/-- A wall of any complex lies in at most one wall of `D`. -/
theorem eq_of_subset_of_mem_walls {C D : FinitePolyhedralComplex h} {Q P P' : Set V}
    (hQ : Q ∈ C.walls) (hP : P ∈ D.walls) (hP' : P' ∈ D.walls) (hQP : Q ⊆ P)
    (hQP' : Q ⊆ P') : P = P' := by
  have := h.finiteDimensional
  obtain ⟨x, hx⟩ := C.nonempty Q (C.mem_cells_of_mem_walls hQ)
  have hQd := C.finrank_direction_add_one_of_mem_walls hQ
  -- The common face contains `Q`, so it has the dimension of both walls.
  have hface {A B : Set V} (hA : A ∈ D.walls) (hB : B ∈ D.walls) (hQA : Q ⊆ A)
      (hQB : Q ⊆ B) : A ∩ B = A := by
    have hAB := D.inter_face A (D.mem_cells_of_mem_walls hA) B (D.mem_cells_of_mem_walls hB)
      ⟨x, hQA hx, hQB hx⟩
    apply hAB.eq_of_finrank_vectorSpan_eq ⟨x, hQA hx, hQB hx⟩
    apply le_antisymm (Submodule.finrank_mono (vectorSpan_mono ℝ hAB.subset))
    have hle := Submodule.finrank_mono (vectorSpan_mono ℝ (Set.subset_inter hQA hQB))
    have hAd := D.finrank_direction_add_one_of_mem_walls hA
    rw [direction_affineSpan] at hQd hAd
    omega
  rw [← hface hP hP' hQP hQP', Set.inter_comm, hface hP' hP hQP' hQP]

/-- Joints are the codimension-two cells. -/
noncomputable abbrev joints (C : FinitePolyhedralComplex h) : Finset (Set V) :=
  C.cellsOfCodimension 2

/-- The subcomplex consisting of all cells of ambient codimension at least `k`.
The dimension inequality also gives the empty complex when `k` exceeds the ambient dimension. -/
noncomputable def codimensionAtLeast (C : FinitePolyhedralComplex h) (k : ℕ) :
    FinitePolyhedralComplex h := by
  classical
  have := h.finiteDimensional
  refine
    { cells := C.cells.filter fun P =>
        Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V
      nonempty := ?_
      rational := ?_
      face_closed := ?_
      inter_face := ?_ }
  · intro P hP
    exact C.nonempty P (Finset.mem_filter.mp hP).1
  · intro P hP
    exact C.rational P (Finset.mem_filter.mp hP).1
  · intro P hP F hF
    obtain ⟨hPC, hdim⟩ := Finset.mem_filter.mp hP
    refine Finset.mem_filter.mpr ⟨C.face_closed P hPC F hF, ?_⟩
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le
      (affineSpan_mono ℝ (isPolyhedralFace_iff.mp hF).2.subset))
    exact (Nat.add_le_add_right hle k).trans hdim
  · intro P hP Q hQ hne
    exact C.inter_face P (Finset.mem_filter.mp hP).1 Q (Finset.mem_filter.mp hQ).1 hne

/-- Membership in the codimension subcomplex is the corresponding dimension inequality. -/
@[simp]
theorem mem_codimensionAtLeast_cells (C : FinitePolyhedralComplex h) (k : ℕ) (P : Set V) :
    P ∈ (C.codimensionAtLeast k).cells ↔ P ∈ C.cells ∧
      Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V := by
  classical
  simp [codimensionAtLeast]

/-- The codimension bound zero retains the entire complex. -/
@[simp]
theorem codimensionAtLeast_zero (C : FinitePolyhedralComplex h) :
    C.codimensionAtLeast 0 = C := by
  have := h.finiteDimensional
  apply ext
  ext P
  simp [Submodule.finrank_le]

/-- Every exact-codimension cell belongs to the corresponding codimension subcomplex. -/
theorem cellsOfCodimension_subset_codimensionAtLeast_cells
    (C : FinitePolyhedralComplex h) (k : ℕ) :
    C.cellsOfCodimension k ⊆ (C.codimensionAtLeast k).cells := by
  intro P hP
  obtain ⟨hPC, hdim⟩ := (C.mem_cellsOfCodimension k P).mp hP
  exact (C.mem_codimensionAtLeast_cells k P).mpr ⟨hPC, hdim.le⟩

/-- Increasing the codimension bound gives a subcomplex of the previous one. -/
theorem codimensionAtLeast_cells_antitone (C : FinitePolyhedralComplex h) :
    Antitone (fun k => (C.codimensionAtLeast k).cells) := by
  intro k l hkl P hP
  obtain ⟨hPC, hdim⟩ := (C.mem_codimensionAtLeast_cells l P).mp hP
  exact (C.mem_codimensionAtLeast_cells k P).mpr
    ⟨hPC, (Nat.add_le_add_left hkl _).trans hdim⟩

/-- Every codimension subcomplex is a weak refinement of the original complex. -/
theorem codimensionAtLeast_isWeakRefinement (C : FinitePolyhedralComplex h) (k : ℕ) :
    (C.codimensionAtLeast k).IsWeakRefinement C := by
  apply isWeakRefinement_iff.mpr
  intro P hP
  exact ⟨P, ((C.mem_codimensionAtLeast_cells k P).mp hP).1, Set.Subset.rfl⟩

open Filter Topology in
/-- Near a relative interior point of a codimension-`k` cell, the skeleton of
codimension at least `k` agrees with that cell. -/
theorem eventually_mem_support_codimensionAtLeast_iff (C : FinitePolyhedralComplex h)
    {P : Set V} {k : ℕ} (hP : P ∈ C.cellsOfCodimension k) {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) :
    ∀ᶠ y in 𝓝 x, y ∈ (C.codimensionAtLeast k).support ↔ y ∈ P := by
  let := h.finiteDimensional
  obtain ⟨hPC, hdimP⟩ := (C.mem_cellsOfCodimension k P).mp hP
  filter_upwards [C.eventually_subset_of_mem_cell hPC hx] with y hy
  constructor
  · intro hys
    obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp hys
    obtain ⟨hQC, hdimQ⟩ := (C.mem_codimensionAtLeast_cells k Q).mp hQ
    have hPQ := hy Q hQC hyQ
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hPQ))
    have hface := (isPolyhedralFace_iff.mp (C.face_of_subset hPC hQC hPQ)).2
    have heq : P = Q := hface.eq_of_finrank_vectorSpan_eq (C.nonempty P hPC)
      (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)
    exact heq ▸ hyQ
  · intro hyP
    exact mem_support.mpr ⟨P, C.cellsOfCodimension_subset_codimensionAtLeast_cells k hP, hyP⟩

open Set Filter Topology in
/-- At a relative interior point of an exact-codimension cell, one ball
simultaneously isolates the cell in its skeleton, avoids its relative boundary,
misses every other cell of the same codimension, and meets only cells containing it. -/
theorem exists_isolating_ball (C : FinitePolyhedralComplex h) {P : Set V} {k : ℕ}
    (hP : P ∈ C.cellsOfCodimension k) {x : V} (hx : x ∈ intrinsicInterior ℝ P) :
    ∃ r > 0,
      Metric.ball x r ∩ (C.codimensionAtLeast k).support = Metric.ball x r ∩ P ∧
      Disjoint (Metric.ball x r) (intrinsicFrontier ℝ P) ∧
      (∀ Q ∈ C.cellsOfCodimension k, Q ≠ P → Disjoint (Metric.ball x r) Q) ∧
      ∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → P ⊆ Q := by
  let := h.finiteDimensional
  have hPC := ((C.mem_cellsOfCodimension k P).mp hP).1
  have hxf : x ∉ intrinsicFrontier ℝ P := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact fun hmem => hmem.2 hx
  have hfront : ∀ᶠ y in 𝓝 x, y ∉ intrinsicFrontier ℝ P :=
    (isClosed_intrinsicFrontier (affineSpan ℝ P).closed_of_finiteDimensional).isOpen_compl.mem_nhds
      hxf
  have hnear := (C.eventually_mem_support_codimensionAtLeast_iff hP hx).and
    (hfront.and (C.eventually_subset_of_mem_cell hPC hx))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · ext y
    exact and_congr_right fun hy => (hball hy).1
  · exact Set.disjoint_left.mpr fun y hy hyf => (hball hy).2.1 hyf
  · intro Q hQ hne
    apply Set.disjoint_left.mpr
    intro y hy hyQ
    obtain ⟨hQC, hdimQ⟩ := (C.mem_cellsOfCodimension k Q).mp hQ
    have hPQ := (hball hy).2.2 Q hQC hyQ
    have hface := (isPolyhedralFace_iff.mp (C.face_of_subset hPC hQC hPQ)).2
    have hdimP := ((C.mem_cellsOfCodimension k P).mp hP).2
    have heq : P = Q := hface.eq_of_finrank_vectorSpan_eq (C.nonempty P hPC)
      (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)
    exact hne heq.symm
  · rintro Q hQ ⟨y, hy, hyQ⟩
    exact (hball hy).2.2 Q hQ hyQ

/-- The relative boundary of a cell of codimension at least `k` lies in the
subcomplex of codimension at least `k + 1`. -/
theorem intrinsicFrontier_subset_support_codimensionAtLeast (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.cells) (k : ℕ)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V) :
    intrinsicFrontier ℝ P ⊆ (C.codimensionAtLeast (k + 1)).support := by
  have := h.finiteDimensional
  obtain ⟨n, g, hpres⟩ := TauCeti.isConvexPolyhedron_iff.mp (C.isConvexPolyhedron hP)
  intro x hx
  rw [Mei.Convex.intrinsicFrontier_eq_iUnion_active g hpres] at hx
  obtain ⟨j, ⟨p, hp, hgp⟩, hxP, hgx⟩ := Set.mem_iUnion₂.mp hx
  let F := {y ∈ P | g j y = 0}
  have hxF : x ∈ F := ⟨hxP, hgx⟩
  have hex : IsExposed ℝ P F := by
    dsimp only [F]
    rw [hpres]
    simpa using Mei.Convex.isExposed_setOf_active g {j}
  have hlt : Module.finrank ℝ (affineSpan ℝ F).direction <
      Module.finrank ℝ (affineSpan ℝ P).direction :=
    (g j).toAffineMap.finrank_direction_inter_zero_lt ⟨x, hxP, hgx⟩ ⟨p, hp, hgp.ne⟩
  apply mem_support.mpr
  refine ⟨F, (C.mem_codimensionAtLeast_cells (k + 1) F).mpr
    ⟨C.face_closed P hP F (isPolyhedralFace_iff.mpr ⟨⟨x, hxF⟩, hex⟩), ?_⟩, hxF⟩
  omega

/-- A point in the codimension-at-least-`k` skeleton but outside the next
skeleton lies in the relative interior of a unique cell of codimension `k`. -/
theorem existsUnique_mem_cellsOfCodimension_of_notMem_succ
    (C : FinitePolyhedralComplex h) {k : ℕ} {x : V}
    (hx : x ∈ (C.codimensionAtLeast k).support)
    (hnext : x ∉ (C.codimensionAtLeast (k + 1)).support) :
    ∃! P : Set V, P ∈ C.cellsOfCodimension k ∧ x ∈ intrinsicInterior ℝ P := by
  obtain ⟨P, hP, hxP⟩ := mem_support.mp hx
  obtain ⟨hPC, hdim⟩ := (C.mem_codimensionAtLeast_cells k P).mp hP
  have hexact : Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V := by
    by_contra he
    exact hnext (mem_support.mpr ⟨P,
      (C.mem_codimensionAtLeast_cells (k + 1) P).mpr ⟨hPC, by omega⟩, hxP⟩)
  have hint : x ∈ intrinsicInterior ℝ P := by
    rw [← intrinsicClosure_sdiff_intrinsicFrontier]
    exact ⟨subset_intrinsicClosure hxP, fun hfront => hnext
      (C.intrinsicFrontier_subset_support_codimensionAtLeast hPC k hdim hfront)⟩
  refine ⟨P, ⟨(C.mem_cellsOfCodimension k P).mpr ⟨hPC, hexact⟩, hint⟩, ?_⟩
  rintro Q ⟨hQ, hxQ⟩
  exact C.eq_of_mem_intrinsicInterior
    ((C.mem_cellsOfCodimension k Q).mp hQ).1 hPC hxQ hint

/-- The singular support of the wall family lies in the support of the subcomplex
of cells of codimension at least two. -/
theorem singularSupport_walls_subset_support_codimensionAtLeast (C : FinitePolyhedralComplex h) :
    Mei.Convex.singularSupport (fun W : C.walls => (W : Set V)) ⊆
      (C.codimensionAtLeast 2).support := by
  have := h.finiteDimensional
  intro x hx
  rcases Mei.Convex.mem_singularSupport.mp hx with ⟨P, hxP⟩ | ⟨P, Q, hne, hxP, hxQ⟩
  · exact C.intrinsicFrontier_subset_support_codimensionAtLeast
      (C.mem_cells_of_mem_walls P.property) 1
      (C.finrank_direction_add_one_of_mem_walls P.property).le hxP
  · have hdimP := C.finrank_direction_add_one_of_mem_walls P.property
    have hdimQ := C.finrank_direction_add_one_of_mem_walls Q.property
    have hlt := (affineSpan ℝ (P : Set V)).finrank_direction_inf_add_one_lt
      (affineSpan ℝ (Q : Set V)) hdimP hdimQ hne
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le
      (le_inf (affineSpan_mono ℝ Set.inter_subset_left)
        (affineSpan_mono ℝ Set.inter_subset_right) :
          affineSpan ℝ ((P : Set V) ∩ Q) ≤ affineSpan ℝ (P : Set V) ⊓ affineSpan ℝ (Q : Set V)))
    apply mem_support.mpr
    refine ⟨(P : Set V) ∩ Q, (C.mem_codimensionAtLeast_cells 2 _).mpr
      ⟨C.inter_mem_cells (C.mem_cells_of_mem_walls P.property)
        (C.mem_cells_of_mem_walls Q.property) ⟨x, hxP, hxQ⟩, ?_⟩, hxP, hxQ⟩
    omega

/-- Away from the singular support there is at most one incident wall, including
when different walls have the same supporting hyperplane. -/
theorem eq_of_mem_wall_of_notMem_singularSupport (C : FinitePolyhedralComplex h)
    {P Q : C.walls} {x : V} (hxP : x ∈ (P : Set V)) (hxQ : x ∈ (Q : Set V))
    (hx : x ∉ Mei.Convex.singularSupport (fun W : C.walls => (W : Set V))) : P = Q := by
  apply Subtype.ext
  exact C.eq_of_mem_intrinsicInterior
    (C.mem_cells_of_mem_walls P.property) (C.mem_cells_of_mem_walls Q.property)
    (Mei.Convex.mem_intrinsicInterior_of_notMem_singularSupport hxP hx)
    (Mei.Convex.mem_intrinsicInterior_of_notMem_singularSupport hxQ hx)

section JointGeometry

open Set Module Mei.Convex

variable {C : FinitePolyhedralComplex h} {J U : Set V}

/-- If every cell meeting `U` contains the joint `J`, the codimension-two skeleton
meets `U` only in `J`. -/
theorem inter_support_codimensionAtLeast_two_subset (hJ : J ∈ C.joints)
    (hinc : ∀ Q ∈ C.cells, (U ∩ Q).Nonempty → J ⊆ Q) :
    U ∩ (C.codimensionAtLeast 2).support ⊆ J := by
  have := h.finiteDimensional
  rintro y ⟨hyU, hys⟩
  obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp hys
  obtain ⟨hQC, hdimQ⟩ := (C.mem_codimensionAtLeast_cells 2 Q).mp hQ
  obtain ⟨hJC, hdimJ⟩ := (C.mem_cellsOfCodimension 2 J).mp hJ
  have hJQ := hinc Q hQC ⟨y, hyU, hyQ⟩
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hJQ))
  have hface := (isPolyhedralFace_iff.mp (C.face_of_subset hJC hQC hJQ)).2
  have heq : J = Q := hface.eq_of_finrank_vectorSpan_eq (C.nonempty J hJC)
    (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)
  exact heq ▸ hyQ

/-- If every cell meeting `U` contains the joint `J`, then `U` misses the relative
boundary of `J`, which consists of cells of higher codimension. -/
theorem disjoint_intrinsicFrontier (hJ : J ∈ C.joints)
    (hinc : ∀ Q ∈ C.cells, (U ∩ Q).Nonempty → J ⊆ Q) :
    Disjoint U (intrinsicFrontier ℝ J) := by
  have := h.finiteDimensional
  obtain ⟨hJC, hdimJ⟩ := (C.mem_cellsOfCodimension 2 J).mp hJ
  refine Set.disjoint_left.mpr fun y hyU hyf => ?_
  obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp
    (C.intrinsicFrontier_subset_support_codimensionAtLeast hJC 2 hdimJ.le hyf)
  obtain ⟨hQC, hdimQ⟩ := (C.mem_codimensionAtLeast_cells (2 + 1) Q).mp hQ
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le
    (affineSpan_mono ℝ (hinc Q hQC ⟨y, hyU, hyQ⟩)))
  omega

/-- In a region meeting only cells incident to a joint, a set whose affine
direction is disjoint from the joint direction meets the skeleton in exactly one
point whenever it meets the joint. This point is in the joint's relative
interior, and the set misses the joint boundary and every other joint. -/
theorem exists_isolating_point_of_disjoint_direction (hJ : J ∈ C.joints)
    (hinc : ∀ Q ∈ C.cells, (U ∩ Q).Nonempty → J ⊆ Q)
    {S : Set V} (hSU : S ⊆ U) (hmeet : (S ∩ J).Nonempty)
    (htrans : Disjoint (affineSpan ℝ J).direction (affineSpan ℝ S).direction) :
    ∃ q ∈ intrinsicInterior ℝ J,
      S ∩ (C.codimensionAtLeast 2).support = {q} ∧
      Disjoint S (intrinsicFrontier ℝ J) ∧
      ∀ Q ∈ C.joints, Q ≠ J → Disjoint S Q := by
  have := h.finiteDimensional
  obtain ⟨q, hqS, hqJ⟩ := hmeet
  have hsub := (affineSpan ℝ J).subsingleton_inter_of_disjoint_direction
    (affineSpan ℝ S) htrans
  have hfront := (C.disjoint_intrinsicFrontier hJ hinc).mono_left hSU
  have hqint : q ∈ intrinsicInterior ℝ J := by
    rw [← closure_sdiff_intrinsicFrontier (𝕜 := ℝ)]
    exact ⟨subset_closure hqJ, hfront.notMem_of_mem_left hqS⟩
  refine ⟨q, hqint, Set.Subset.antisymm ?_ ?_, hfront, ?_⟩
  · rintro y ⟨hyS, hys⟩
    have hyJ := C.inter_support_codimensionAtLeast_two_subset hJ hinc ⟨hSU hyS, hys⟩
    exact Set.mem_singleton_iff.mpr (hsub
      ⟨subset_affineSpan ℝ J hyJ, subset_affineSpan ℝ S hyS⟩
      ⟨subset_affineSpan ℝ J hqJ, subset_affineSpan ℝ S hqS⟩)
  · rintro y (rfl : y = q)
    exact ⟨hqS, mem_support.mpr ⟨J,
      C.cellsOfCodimension_subset_codimensionAtLeast_cells 2 hJ, hqJ⟩⟩
  · intro Q hQ hne
    apply Set.disjoint_left.mpr
    intro y hyS hyQ
    obtain ⟨hJC, hdimJ⟩ := (C.mem_cellsOfCodimension 2 J).mp hJ
    obtain ⟨hQC, hdimQ⟩ := (C.mem_cellsOfCodimension 2 Q).mp hQ
    have hJQ := hinc Q hQC ⟨y, hSU hyS, hyQ⟩
    have hface := (isPolyhedralFace_iff.mp (C.face_of_subset hJC hQC hJQ)).2
    exact hne (hface.eq_of_finrank_vectorSpan_eq (C.nonempty J hJC)
      (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)).symm

/-- If a wall contains the joint `J`, the points of `J` are singular for the walls. -/
theorem mem_singularSupport_of_mem_joint (hJ : J ∈ C.joints) {P : C.walls}
    (hJP : J ⊆ P) {y : V} (hyJ : y ∈ J) :
    y ∈ singularSupport fun Q : C.walls => (Q : Set V) := by
  have := h.finiteDimensional
  obtain ⟨hJC, hdimJ⟩ := (C.mem_cellsOfCodimension 2 J).mp hJ
  by_contra hy
  have hPJ := C.subset_of_mem_intrinsicInterior (C.mem_cells_of_mem_walls P.property) hJC
    (mem_intrinsicInterior_of_notMem_singularSupport (hJP hyJ) hy) hyJ
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hPJ))
  have := C.finrank_direction_add_one_of_mem_walls P.property
  omega

end JointGeometry

end Mei.FinitePolyhedralComplex
