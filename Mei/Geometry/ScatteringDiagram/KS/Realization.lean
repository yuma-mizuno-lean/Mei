/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Presentation
public import Mei.Geometry.ScatteringDiagram.Equivalence
import Mei.Geometry.Convex.Polyhedron.Path.Restriction

/-!
# Indexed ray representatives of finite KS complexes

Every finite KS complex has an indexed wall presentation on its own walls whose completed
labels project to the original labels. Each wall is indexed by the supported primitive ray
of its coorienting degree. Identity labels lift to the identity. At the prescribed cutoff,
discarding these identity walls preserves path products, as does replacing the original
coorientations by their primitive generators. Converting the presentation back to a KS
complex gives a diagram equivalent to the original. The construction chooses lifts independently
at this single cutoff; it does not assert compatibility of such choices at different cutoffs.

This supplies finite ray representatives for the comparison of cone complexes and indexed
presentations in Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), and Bridgeland, *Scattering diagrams, Hall algebras and stability
conditions*, §§2–3 (arXiv:1603.00416v4). The central formal inputs are
`KSComplex.label_mem_bchSubgroup_rayLieSubalgebra`,
`PositiveDegrees.exists_completedRaySubgroup_projection_eq`,
`FiniteWallDiagram.pathProduct_rescale` and `Quiver.Path.wallPathProduct_restrict`.
-/

public section

noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace Mei.KSComplex

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [Module.Free ℤ N]
  {C : FinitePolyhedralComplex h} {k : ℕ} (D : KSComplex s d ℒ C k)

/-- The supported primitive ray of the coorienting degree of a KS wall. -/
def wallRay (P : C.walls) : SupportedRay d :=
  (d.exists_supportedRay (D.degree_mem P) (D.degree_ne_zero P)).choose

/-- The original coorienting degree is an actual degree of its supported ray. -/
theorem degree_mem_wallRay (P : C.walls) : D.degree P ∈ (D.wallRay P).rayDegrees :=
  (d.exists_supportedRay (D.degree_mem P) (D.degree_ne_zero P)).choose_spec

private theorem exists_label_lift (P : C.walls) :
    ∃ G ∈ d.completedRaySubgroup ℒ (D.wallRay P),
      CompletedGroup.projection k G = D.label P :=
  d.exists_completedRaySubgroup_projection_eq ℒ _ k
    (D.label_mem_bchSubgroup_rayLieSubalgebra P (D.degree_mem_wallRay P))

/-- Lift one KS wall to an indexed wall on its supported primitive ray. The completed
label is a choice of lift of the finite label, with the identity lifted to the identity. -/
def indexedWall (P : C.walls) : IndexedWall s d ℒ := by
  classical
  exact {
    ray := D.wallRay P
    support := P
    isCone := (FinitePolyhedralComplex.isConical_iff C).mp D.isConical P
      (C.mem_cells_of_mem_walls P.property)
    rational_support := C.rational P (C.mem_cells_of_mem_walls P.property)
    direction_support := by
      obtain ⟨a, ha, he⟩ := s.exists_normal_eq_smul_of_mem_rayDegrees (D.degree_mem_wallRay P)
      rw [← D.ker_normal P, he, LinearMap.ker_smul _ _ ha.ne']
    label := if D.label P = 1 then 1 else (D.exists_label_lift P).choose
    label_mem := by
      split_ifs
      · exact one_mem _
      · exact (D.exists_label_lift P).choose_spec.1 }

@[simp]
theorem indexedWall_ray (P : C.walls) :
    (D.indexedWall P).ray = D.wallRay P := (rfl)

@[simp]
theorem indexedWall_support (P : C.walls) :
    (D.indexedWall P).support = (P : Set V) := (rfl)

/-- The chosen completed label recovers exactly the original finite label. -/
@[simp]
theorem projection_indexedWall_label (P : C.walls) :
    (CompletedGroup.projection k (D.indexedWall P).label : d.truncatedGroup ℒ k) = D.label P := by
  classical
  dsimp only [indexedWall]
  split_ifs with hP
  · simp only [map_one, hP]
    rfl
  · exact (D.exists_label_lift P).choose_spec.2

/-- A lifted wall is the identity exactly when its original finite label is the identity. -/
@[simp]
theorem indexedWall_label_eq_one_iff (P : C.walls) :
    (D.indexedWall P).label = 1 ↔ D.label P = 1 := by
  classical
  constructor
  · intro he
    rw [← D.projection_indexedWall_label P, he, map_one]
    rfl
  · intro he
    simp [indexedWall, he]

/-- An indexed presentation representing the KS complex at its specified finite cutoff.
It retains one index for each original wall, including identity-labelled walls. -/
def indexedPresentation : IndexedWallPresentation s d ℒ C.walls where
  wall := D.indexedWall
  finite_active _ := Set.toFinite _

@[simp]
theorem indexedPresentation_wall (P : C.walls) :
    D.indexedPresentation.wall P = D.indexedWall P := (rfl)

/-- Activity at the represented cutoff is precisely nontriviality of the original label. -/
@[simp↓]
theorem mem_indexedPresentation_active (P : C.walls) :
    P ∈ D.indexedPresentation.active k ↔ D.label P ≠ 1 := by
  simp only [IndexedWallPresentation.mem_active, indexedPresentation_wall,
    projection_indexedWall_label]
  rfl

/-- Forget the identity walls of the represented cutoff without changing the vertices. -/
def indexedPathPrefunctor :
    WallComplement (fun P : C.walls => (P : Set V)) ⥤q
      WallComplement (fun P : D.indexedPresentation.active k =>
        (D.indexedPresentation.wall P).support) :=
  WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V)) Subtype.val

@[simp]
theorem indexedPathPrefunctor_obj_val
    (x : WallComplement (fun P : C.walls => (P : Set V))) :
    ((D.indexedPathPrefunctor).obj x).val = x.val := (rfl)

/-- Forgetting identity walls commutes with reversal of segments and paths. -/
instance : D.indexedPathPrefunctor.MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

private def primitiveDiagram : FiniteWallDiagram C (d.truncatedGroup ℒ k) where
  normal P := s.normal (D.wallRay P).generator
  ker_normal P := by
    obtain ⟨a, ha, he⟩ := s.exists_normal_eq_smul_of_mem_rayDegrees (D.degree_mem_wallRay P)
    rw [← D.ker_normal P, he, LinearMap.ker_smul _ _ ha.ne']
  label := D.label

private theorem primitiveDiagram_normal (P : C.walls) :
    D.primitiveDiagram.normal P = s.normal (D.wallRay P).generator := (rfl)

private theorem primitiveDiagram_label (P : C.walls) :
    D.primitiveDiagram.label P = D.label P := (rfl)

private theorem primitiveDiagram_pathProduct
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) :
    D.primitiveDiagram.pathProduct p = D.toFiniteWallDiagram.pathProduct p := by
  choose a ha he using fun P =>
    s.exists_normal_eq_smul_of_mem_rayDegrees (D.degree_mem_wallRay P)
  have heq : D.primitiveDiagram.rescale a ha = D.toFiniteWallDiagram := by
    apply FiniteWallDiagram.ext
    · funext P
      simp only [FiniteWallDiagram.rescale_normal, primitiveDiagram_normal,
        toFiniteWallDiagram_normal, he]
    · funext P
      rw [FiniteWallDiagram.rescale_label, primitiveDiagram_label, toFiniteWallDiagram_label]
  rw [← heq, FiniteWallDiagram.pathProduct_rescale]

/-- At the represented cutoff the indexed presentation computes the original KS product.
The path simply forgets walls whose original labels are the identity. -/
theorem levelPathProduct_indexedPresentation [IsAbelianRays d ℒ]
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) :
    D.indexedPresentation.levelPathProduct k (D.indexedPathPrefunctor.mapPath p) =
      D.toFiniteWallDiagram.pathProduct p := by
  have comm : ∀ P Q : C.walls, affineSpan ℝ (P : Set V) = affineSpan ℝ (Q : Set V) →
      Commute (D.primitiveDiagram.label P) (D.primitiveDiagram.label Q) := by
    simpa only [primitiveDiagram_label] using D.commute_label_of_affineSpan_eq
  rw [← D.primitiveDiagram_pathProduct p,
    FiniteWallDiagram.pathProduct_eq_wallPathProduct _ comm,
    D.indexedPresentation.levelPathProduct_eq_wallPathProduct k _
      (D.indexedPresentation.activeLabels_commute k)]
  have hr := p.wallPathProduct_restrict D.primitiveDiagram.normal D.primitiveDiagram.label
    comm (κ := D.indexedPresentation.active k) Subtype.val Subtype.val_injective (by
    intro P hP
    by_contra hn
    exact hP ⟨⟨P, (D.mem_indexedPresentation_active P).mpr hn⟩, rfl⟩)
  simp only [indexedPathPrefunctor, indexedPresentation_wall, indexedWall_ray,
    projection_indexedWall_label]
  -- Normalize the categorical tower fiber to its concrete BCH quotient in the comparison.
  convert! hr using 1

/-- Every common vertex list has the same transport in the original complex and its
indexed representative, even when the endpoints use different admissibility proofs. -/
theorem pathProduct_indexedPresentation [IsAbelianRays d ℒ]
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    {x' y' : WallComplement (fun P : D.indexedPresentation.active k =>
      (D.indexedPresentation.wall P).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    D.toFiniteWallDiagram.pathProduct p = D.indexedPresentation.levelPathProduct k q := by
  rw [← D.levelPathProduct_indexedPresentation p]
  let E := D.indexedPresentation
  rw [E.levelPathProduct_eq_wallPathProduct k _ (E.activeLabels_commute k),
    E.levelPathProduct_eq_wallPathProduct k _ (E.activeLabels_commute k)]
  apply Quiver.Path.wallPathProduct_eq_of_segmentPathProduct_eq
    _ _ _ _ _ _ ?_ _ _
    (by simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      indexedPathPrefunctor_obj_val] using hpq)
  intro a b a' b' e e' ha hb
  obtain rfl : a = a' := WallComplement.ext ha
  obtain rfl : b = b' := WallComplement.ext hb
  congr 1
  exact PLift.ext (Subsingleton.elim _ _)

/-- Converting the indexed representative back to a KS complex recovers the original
finite diagram up to its actual path-product equivalence. -/
theorem toKSComplex_indexedPresentation_equivalent [IsAbelianRays d ℒ] :
    (D.indexedPresentation.toKSComplex k).toFiniteWallDiagram.Equivalent
      D.toFiniteWallDiagram := by
  rw [FiniteWallDiagram.equivalent_def]
  intro x y x' y' p q hpq
  rw [D.indexedPresentation.pathProduct_toKSComplex_eq_levelPathProduct_mapPath k p]
  symm
  apply D.pathProduct_indexedPresentation q _
  simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    IndexedWallPresentation.pathPrefunctor_obj_val] using hpq.symm

end Mei.KSComplex
