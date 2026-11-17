/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Basic
public import TauCeti.Geometry.Convex.PolyhedralComplex.Skeleton
public import Mei.Geometry.Convex.Polyhedron.SingularSupport
public import Mei.Geometry.Convex.Polyhedron.Face
import TauCeti.LinearAlgebra.AffineSpace.Transverse
import Mei.Geometry.Convex.Polyhedron.Boundary

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

open TauCeti (FinitePolyhedralComplex)

open TauCeti (singularSupport mem_intrinsicInterior_of_notMem_singularSupport)

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Every wall is a cell of the complex. -/
theorem mem_cells_of_mem_walls (C : FinitePolyhedralComplex h) {P : Set V}
    (hP : P ∈ C.walls) : P ∈ C.cells :=
  (mem_cellsOfCodimension.mp hP).1

/-- The direction dimension of a wall is one less than the ambient dimension. -/
theorem finrank_direction_add_one_of_mem_walls (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.walls) :
    Module.finrank ℝ (affineSpan ℝ P).direction + 1 = Module.finrank ℝ V :=
  (mem_cellsOfCodimension.mp hP).2

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

/-- A wall contained in a set whose affine span has codimension one has the affine span of
that set. -/
theorem affineSpan_eq_of_subset_of_mem_walls (C : FinitePolyhedralComplex h) {Q S : Set V}
    (hQ : Q ∈ C.walls) (hQS : Q ⊆ S)
    (hS : Module.finrank ℝ (affineSpan ℝ S).direction + 1 = Module.finrank ℝ V) :
    affineSpan ℝ Q = affineSpan ℝ S := by
  have := h.finiteDimensional
  have hle := affineSpan_mono ℝ hQS
  have hdQ := C.finrank_direction_add_one_of_mem_walls hQ
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) (by omega))
    ((C.nonempty Q (C.mem_cells_of_mem_walls hQ)).mono (subset_affineSpan ℝ Q)) hle

/-- Contained walls in two finite complexes have the same affine span. -/
theorem affineSpan_eq_of_walls_subset {C D : FinitePolyhedralComplex h} (Q : C.walls) (P : D.walls)
    (hQP : (Q : Set V) ⊆ P) :
    affineSpan ℝ (Q : Set V) = affineSpan ℝ (P : Set V) :=
  C.affineSpan_eq_of_subset_of_mem_walls Q.property hQP
    (D.finrank_direction_add_one_of_mem_walls P.property)

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

open Set in
/-- Near a relative interior point of a wall, a ball meets no other wall. -/
theorem exists_ball_eq_wall_of_mem_intrinsicInterior (C : FinitePolyhedralComplex h)
    (P : C.walls) {q : V}
    (hq : q ∈ intrinsicInterior ℝ (P : Set V)) :
    ∃ r > 0, ∀ Q : C.walls, ∀ z ∈ Metric.ball q r, z ∈ (Q : Set V) → Q = P := by
  obtain ⟨r, hr, -, -, hdisj, -⟩ := C.exists_ball_inter_support_codimensionGE_eq P.property hq
  refine ⟨r, hr, fun Q z hz hzQ => ?_⟩
  by_contra hne
  exact disjoint_left.mp (hdisj Q (C.cellsOfCodimension_subset_cells_codimensionGE 1 Q.property)
    (fun he => hne (Subtype.ext he))) hz hzQ

/-- The relative boundary of a cell of codimension at least `k` lies in the
subcomplex of codimension at least `k + 1`. -/
theorem intrinsicFrontier_subset_support_codimensionAtLeast (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.cells) (k : ℕ)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V) :
    intrinsicFrontier ℝ P ⊆ (C.codimensionGE (k + 1)).support := by
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
    simpa using TauCeti.isExposed_setOf_active g {j}
  have hlt : Module.finrank ℝ (affineSpan ℝ F).direction <
      Module.finrank ℝ (affineSpan ℝ P).direction :=
    (g j).toAffineMap.finrank_direction_inter_zero_lt ⟨x, hxP, hgx⟩ ⟨p, hp, hgp.ne⟩
  apply mem_support.mpr
  refine ⟨F, FinitePolyhedralComplex.mem_cells_codimensionGE.mpr
    ⟨C.face_closed P hP F (isPolyhedralFace_iff.mpr ⟨⟨x, hxF⟩, hex⟩), ?_⟩, hxF⟩
  omega

/-- A point in the codimension-at-least-`k` skeleton but outside the next
skeleton lies in the relative interior of a unique cell of codimension `k`. -/
theorem existsUnique_mem_cellsOfCodimension_of_notMem_succ
    (C : FinitePolyhedralComplex h) {k : ℕ} {x : V}
    (hx : x ∈ (C.codimensionGE k).support)
    (hnext : x ∉ (C.codimensionGE (k + 1)).support) :
    ∃! P : Set V, P ∈ C.cellsOfCodimension k ∧ x ∈ intrinsicInterior ℝ P := by
  obtain ⟨P, hP, hxP⟩ := mem_support.mp hx
  obtain ⟨hPC, hdim⟩ := FinitePolyhedralComplex.mem_cells_codimensionGE.mp hP
  have hexact : Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V := by
    by_contra he
    exact hnext (mem_support.mpr ⟨P,
      FinitePolyhedralComplex.mem_cells_codimensionGE.mpr ⟨hPC, by omega⟩, hxP⟩)
  have hint : x ∈ intrinsicInterior ℝ P := by
    rw [← intrinsicClosure_sdiff_intrinsicFrontier]
    exact ⟨subset_intrinsicClosure hxP, fun hfront => hnext
      (C.intrinsicFrontier_subset_support_codimensionAtLeast hPC k hdim hfront)⟩
  refine ⟨P, ⟨mem_cellsOfCodimension.mpr ⟨hPC, hexact⟩, hint⟩, ?_⟩
  rintro Q ⟨hQ, hxQ⟩
  exact C.eq_of_mem_intrinsicInterior
    (mem_cellsOfCodimension.mp hQ).1 hPC hxQ hint

/-- The singular support of the wall family lies in the support of the subcomplex
of cells of codimension at least two. -/
theorem singularSupport_walls_subset_support_codimensionAtLeast (C : FinitePolyhedralComplex h) :
    TauCeti.singularSupport (fun W : C.walls => (W : Set V)) ⊆
      (C.codimensionGE 2).support := by
  have := h.finiteDimensional
  intro x hx
  rcases TauCeti.mem_singularSupport.mp hx with ⟨P, hxP⟩ | ⟨P, Q, hne, hxP, hxQ⟩
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
    refine ⟨(P : Set V) ∩ Q, FinitePolyhedralComplex.mem_cells_codimensionGE.mpr
      ⟨C.inter_mem_cells (C.mem_cells_of_mem_walls P.property)
        (C.mem_cells_of_mem_walls Q.property) ⟨x, hxP, hxQ⟩, ?_⟩, hxP, hxQ⟩
    omega

/-- Away from the singular support there is at most one incident wall, including
when different walls have the same supporting hyperplane. -/
theorem eq_of_mem_wall_of_notMem_singularSupport (C : FinitePolyhedralComplex h)
    {P Q : C.walls} {x : V} (hxP : x ∈ (P : Set V)) (hxQ : x ∈ (Q : Set V))
    (hx : x ∉ TauCeti.singularSupport (fun W : C.walls => (W : Set V))) : P = Q := by
  apply Subtype.ext
  exact C.eq_of_mem_intrinsicInterior
    (C.mem_cells_of_mem_walls P.property) (C.mem_cells_of_mem_walls Q.property)
    (TauCeti.mem_intrinsicInterior_of_notMem_singularSupport hxP hx)
    (TauCeti.mem_intrinsicInterior_of_notMem_singularSupport hxQ hx)

section JointGeometry

open Set Module Mei.Convex

variable {C : FinitePolyhedralComplex h} {J U : Set V}

/-- If every cell meeting `U` contains the joint `J`, the codimension-two skeleton
meets `U` only in `J`. -/
theorem inter_support_codimensionAtLeast_two_subset (hJ : J ∈ C.joints)
    (hinc : ∀ Q ∈ C.cells, (U ∩ Q).Nonempty → J ⊆ Q) :
    U ∩ (C.codimensionGE 2).support ⊆ J := by
  have := h.finiteDimensional
  rintro y ⟨hyU, hys⟩
  obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp hys
  obtain ⟨hQC, hdimQ⟩ := FinitePolyhedralComplex.mem_cells_codimensionGE.mp hQ
  obtain ⟨hJC, hdimJ⟩ := mem_cellsOfCodimension.mp hJ
  have hJQ := hinc Q hQC ⟨y, hyU, hyQ⟩
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hJQ))
  have hface := (isPolyhedralFace_iff.mp (C.isPolyhedralFace_of_subset hJC hQC hJQ)).2
  have heq : J = Q := hface.eq_of_finrank_vectorSpan_eq (C.nonempty J hJC)
    (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)
  exact heq ▸ hyQ

/-- If every cell meeting `U` contains the joint `J`, then `U` misses the relative
boundary of `J`, which consists of cells of higher codimension. -/
theorem disjoint_intrinsicFrontier (hJ : J ∈ C.joints)
    (hinc : ∀ Q ∈ C.cells, (U ∩ Q).Nonempty → J ⊆ Q) :
    Disjoint U (intrinsicFrontier ℝ J) := by
  have := h.finiteDimensional
  obtain ⟨hJC, hdimJ⟩ := mem_cellsOfCodimension.mp hJ
  refine Set.disjoint_left.mpr fun y hyU hyf => ?_
  obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp
    (C.intrinsicFrontier_subset_support_codimensionAtLeast hJC 2 hdimJ.le hyf)
  obtain ⟨hQC, hdimQ⟩ := FinitePolyhedralComplex.mem_cells_codimensionGE.mp hQ
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
      S ∩ (C.codimensionGE 2).support = {q} ∧
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
      C.cellsOfCodimension_subset_cells_codimensionGE 2 hJ, hqJ⟩⟩
  · intro Q hQ hne
    apply Set.disjoint_left.mpr
    intro y hyS hyQ
    obtain ⟨hJC, hdimJ⟩ := mem_cellsOfCodimension.mp hJ
    obtain ⟨hQC, hdimQ⟩ := mem_cellsOfCodimension.mp hQ
    have hJQ := hinc Q hQC ⟨y, hSU hyS, hyQ⟩
    have hface := (isPolyhedralFace_iff.mp (C.isPolyhedralFace_of_subset hJC hQC hJQ)).2
    exact hne (hface.eq_of_finrank_vectorSpan_eq (C.nonempty J hJC)
      (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)).symm

/-- If a wall contains the joint `J`, the points of `J` are singular for the walls. -/
theorem mem_singularSupport_of_mem_joint (hJ : J ∈ C.joints) {P : C.walls}
    (hJP : J ⊆ P) {y : V} (hyJ : y ∈ J) :
    y ∈ singularSupport fun Q : C.walls => (Q : Set V) := by
  have := h.finiteDimensional
  obtain ⟨hJC, hdimJ⟩ := mem_cellsOfCodimension.mp hJ
  by_contra hy
  have hPJ := C.subset_of_mem_intrinsicInterior (C.mem_cells_of_mem_walls P.property) hJC
    (mem_intrinsicInterior_of_notMem_singularSupport (hJP hyJ) hy) hyJ
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hPJ))
  have := C.finrank_direction_add_one_of_mem_walls P.property
  omega

end JointGeometry
end TauCeti.FinitePolyhedralComplex
