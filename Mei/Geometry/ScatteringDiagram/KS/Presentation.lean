/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall
public import Mei.Geometry.ScatteringDiagram.KS.Completion
public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision
public import Mei.Geometry.Convex.PolyhedralComplex.Subcomplex
public import Mei.Geometry.Convex.Polyhedron.Path.Coarsening
public import Mei.Geometry.Convex.Polyhedron.Path.Comparison
import Mei.Data.Finset.NoncommProd

/-!
# Finite KS complexes of indexed wall presentations

At each degree cutoff `k`, the active supports of an indexed wall presentation are cut along all
inequalities of linear presentations of these cones. This gives a conical ambient subdivision of
the KS space; its walls lying in some active support, with all their faces, form the order-`k`
complex of the presentation. A wall of this complex lies in a unique supported-ray hyperplane,
and with abelian rays it carries the `Finset.noncommProd` of the projected labels of all active
indexed walls containing it. This is a `KSComplex` whose path products are the presentation's
finite-order path products on every common vertex list: at each crossing, the active supports
met are exactly those containing the crossed wall, and they are crossed with the same sign.
Lowering the cutoff projects these path products and forgets the walls that become inactive, so
the finite KS complexes form the `CompletedDiagram` of the presentation. The linear presentations
of the supports are auxiliary choices; the stated properties concern actual cells and supports.

This realizes the cell labelling of the abelian-ray presentations of scattering diagrams in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), in the conical complexes of Bridgeland, *Scattering diagrams, Hall algebras
and stability conditions*, Definition 2.1 (arXiv:1603.00416v4). Coincident and overlapping
supports, lineality and identity labels are allowed.

The construction uses `FinitePolyhedralComplex.ambientSubdivision`,
`FinitePolyhedralComplex.generatedSubcomplex` and
`WallComplement.segmentPathProduct_eq_of_crossingEventProduct_eq`.
-/

public section

noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace Mei

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

namespace IndexedWallPresentation

variable {ι : Type*} (D : IndexedWallPresentation s d ℒ ι)

private def presentation (j : ι) : RationalAffinePolyhedron h :=
  Classical.choose (D.wall j).exists_presentation_map_zero

private theorem presentation_carrier (j : ι) : (D.presentation j).carrier = (D.wall j).support :=
  (Classical.choose_spec (D.wall j).exists_presentation_map_zero).1

private theorem presentation_inequality_zero (j : ι) (m) :
    (D.presentation j).inequality m 0 = 0 :=
  (Classical.choose_spec (D.wall j).exists_presentation_map_zero).2 m

/-- The conical ambient subdivision cut out by every inequality of fixed linear presentations
of the active supports at order `k`. It covers the whole KS space. -/
def ambientComplex (k : ℕ) : FinitePolyhedralComplex h :=
  FinitePolyhedralComplex.ambientSubdivision (fun j : D.active k => D.presentation j.val)

/-- The ambient complex is conical, with lineality allowed. -/
theorem isConical_ambientComplex (k : ℕ) : (D.ambientComplex k).IsConical :=
  FinitePolyhedralComplex.isConical_ambientSubdivision _
    (fun j => D.presentation_inequality_zero j.val)

/-- The ambient complex covers the whole space. -/
@[simp]
theorem support_ambientComplex (k : ℕ) : (D.ambientComplex k).support = univ :=
  FinitePolyhedralComplex.support_ambientSubdivision _

/-- The order-`k` complex: walls of the ambient complex contained in an active support, with all
their faces. -/
def levelComplex (k : ℕ) : FinitePolyhedralComplex h :=
  (D.ambientComplex k).generatedSubcomplex
    {Q | Q ∈ (D.ambientComplex k).walls ∧ ∃ j : D.active k, Q ⊆ (D.wall j).support}

/-- The order-`k` complex is a subcomplex of the ambient complex. -/
theorem levelComplex_isSubcomplex (k : ℕ) : (D.levelComplex k).IsSubcomplex (D.ambientComplex k) :=
  FinitePolyhedralComplex.generatedSubcomplex_isSubcomplex _ _

/-- The order-`k` complex is conical. -/
theorem isConical_levelComplex (k : ℕ) : (D.levelComplex k).IsConical :=
  (FinitePolyhedralComplex.isConical_iff _).mpr fun Q hQ =>
    (FinitePolyhedralComplex.isConical_iff _).mp (D.isConical_ambientComplex k) Q
      (FinitePolyhedralComplex.isSubcomplex_iff.mp (D.levelComplex_isSubcomplex k) hQ)

/-- The walls of the order-`k` complex are the ambient walls contained in an active support. -/
theorem mem_levelComplex_walls {k : ℕ} {Q : Set V} :
    Q ∈ (D.levelComplex k).walls ↔
      Q ∈ (D.ambientComplex k).walls ∧ ∃ j : D.active k, Q ⊆ (D.wall j).support := by
  simp only [FinitePolyhedralComplex.mem_cellsOfCodimension]
  constructor
  · rintro ⟨hQ, hdim⟩
    obtain ⟨hQa, Q', -, ⟨-, j, hj⟩, hQQ'⟩ :=
      FinitePolyhedralComplex.mem_generatedSubcomplex_cells.mp hQ
    exact ⟨⟨hQa, hdim⟩, j, hQQ'.trans hj⟩
  · rintro ⟨⟨hQa, hdim⟩, hj⟩
    refine ⟨FinitePolyhedralComplex.mem_generatedSubcomplex_of_mem hQa ⟨?_, hj⟩, hdim⟩
    exact (FinitePolyhedralComplex.mem_cellsOfCodimension _ 1 Q).mpr ⟨hQa, hdim⟩

/-- Every wall of the order-`k` complex lies in an active support. -/
theorem exists_subset_support_of_mem_levelComplex_walls {k : ℕ} {Q : Set V}
    (hQ : Q ∈ (D.levelComplex k).walls) : ∃ j : D.active k, Q ⊆ (D.wall j).support :=
  (D.mem_levelComplex_walls.mp hQ).2

/-- Every point of an active support lies on a wall of the order-`k` complex contained in that
support, even when the point is on the support's relative boundary. -/
theorem exists_mem_levelComplex_walls_subset (k : ℕ) (j : D.active k) {x : V}
    (hx : x ∈ (D.wall j).support) :
    ∃ Q ∈ (D.levelComplex k).walls, x ∈ Q ∧ Q ⊆ (D.wall j).support := by
  have hdim : Module.finrank ℝ (affineSpan ℝ (D.presentation j.val).carrier).direction + 1 =
      Module.finrank ℝ V := by
    rw [D.presentation_carrier]
    exact (D.wall j).finrank_direction_add_one
  have he := FinitePolyhedralComplex.exists_mem_ambientSubdivision_walls_subset
    (fun a : D.active k => D.presentation a.val) j hdim (by rwa [D.presentation_carrier])
  rw [D.presentation_carrier] at he
  obtain ⟨Q, hQ, hxQ, hsub⟩ := he
  exact ⟨Q, D.mem_levelComplex_walls.mpr ⟨hQ, j, hsub⟩, hxQ, hsub⟩

/-- The order-`k` complex covers exactly the active supports. -/
@[simp]
theorem support_levelComplex (k : ℕ) :
    (D.levelComplex k).support = ⋃ j : D.active k, (D.wall j).support := by
  ext x
  rw [FinitePolyhedralComplex.mem_support, mem_iUnion]
  constructor
  · rintro ⟨Q, hQ, hxQ⟩
    obtain ⟨-, Q', -, ⟨-, j, hj⟩, hQQ'⟩ :=
      FinitePolyhedralComplex.mem_generatedSubcomplex_cells.mp hQ
    exact ⟨j, hj (hQQ' hxQ)⟩
  · rintro ⟨j, hj⟩
    obtain ⟨Q, hQ, hxQ, -⟩ := D.exists_mem_levelComplex_walls_subset k j hj
    exact ⟨Q, (D.levelComplex k).mem_cells_of_mem_walls hQ, hxQ⟩

/-- On the relative interior of a cell of the order-`k` complex, meeting an active support is
equivalent to containment of the whole closed cell in that support. -/
theorem mem_support_iff_of_mem_intrinsicInterior (k : ℕ) {Q : Set V}
    (hQ : Q ∈ (D.levelComplex k).cells) {x : V} (hx : x ∈ intrinsicInterior ℝ Q) (j : D.active k) :
    x ∈ (D.wall j).support ↔ Q ⊆ (D.wall j).support := by
  refine ⟨fun hxj => ?_, fun hsub => hsub (intrinsicInterior_subset hx)⟩
  rw [← D.presentation_carrier] at hxj ⊢
  exact FinitePolyhedralComplex.subset_carrier_of_mem_intrinsicInterior_ambientSubdivision
    (fun a : D.active k => D.presentation a.val)
    (FinitePolyhedralComplex.isSubcomplex_iff.mp (D.levelComplex_isSubcomplex k) hQ) j hx hxj

private theorem affineSpan_eq_of_subset {k : ℕ} {Q : Set V} (hQ : Q ∈ (D.levelComplex k).walls)
    (j : ι) (hsub : Q ⊆ (D.wall j).support) :
    affineSpan ℝ Q = affineSpan ℝ (D.wall j).support :=
  (D.levelComplex k).affineSpan_eq_of_subset_of_mem_walls hQ hsub
    (D.wall j).finrank_direction_add_one

/-- All indexed walls containing a wall of the order-`k` complex lie on one supported ray. -/
theorem ray_eq_of_subset [Module.Free ℤ N] {k : ℕ} {Q : Set V} (hQ : Q ∈ (D.levelComplex k).walls)
    {j j' : ι} (hj : Q ⊆ (D.wall j).support) (hj' : Q ⊆ (D.wall j').support) :
    (D.wall j).ray = (D.wall j').ray :=
  (D.wall j).ray_eq_of_affineSpan_eq (D.wall j')
    ((D.affineSpan_eq_of_subset hQ j hj).symm.trans (D.affineSpan_eq_of_subset hQ j' hj'))

/-- Forget the extra cuts of the order-`k` complex without moving the path. -/
def pathPrefunctor (k : ℕ) :
    WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V)) ⥤q
      WallComplement (fun j : D.active k => (D.wall j).support) :=
  WallComplement.wallCoverPrefunctor (fun j => (D.wall j).isConvexPolyhedron.isClosed)
    (fun j x hx => by
      obtain ⟨Q, hQ, hxQ, hsub⟩ := D.exists_mem_levelComplex_walls_subset k j hx
      exact ⟨⟨Q, hQ⟩, hxQ, hsub, D.affineSpan_eq_of_subset hQ j hsub⟩)

/-- Forgetting the extra cuts preserves each ambient point. -/
@[simp]
theorem pathPrefunctor_obj_val (k : ℕ)
    (x : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V))) :
    ((D.pathPrefunctor k).obj x).val = x.val := by
  rw [pathPrefunctor, WallComplement.wallCoverPrefunctor_obj_val]

/-- Forgetting the extra cuts commutes with path reversal. -/
instance (k : ℕ) : (D.pathPrefunctor k).MapReverse := by
  unfold pathPrefunctor
  infer_instance

/-- The active indices whose supports contain a set. -/
def wallIndices (k : ℕ) (Q : Set V) : Finset (D.active k) :=
  (Set.toFinite {j : D.active k | Q ⊆ (D.wall j).support}).toFinset

@[simp]
theorem mem_wallIndices {k : ℕ} {Q : Set V} {j : D.active k} :
    j ∈ D.wallIndices k Q ↔ Q ⊆ (D.wall j).support := by
  simp [wallIndices]

/-- The supported ray of a wall of the order-`k` complex. By `wallRay_eq` it is the ray of
every active indexed wall containing it. -/
def wallRay {k : ℕ} (Q : (D.levelComplex k).walls) : SupportedRay d :=
  (D.wall (D.exists_subset_support_of_mem_levelComplex_walls Q.property).choose).ray

/-- Every active indexed wall containing a wall of the order-`k` complex has its ray. -/
theorem wallRay_eq [Module.Free ℤ N] {k : ℕ} (Q : (D.levelComplex k).walls) {j : ι}
    (hj : (Q : Set V) ⊆ (D.wall j).support) : D.wallRay Q = (D.wall j).ray :=
  D.ray_eq_of_subset Q.property
    (D.exists_subset_support_of_mem_levelComplex_walls Q.property).choose_spec hj

variable [Module.Free ℤ N] [IsAbelianRays d ℒ]

/-- The projected labels of the active indexed walls containing a wall commute. -/
theorem wallIndices_pairwise_commute {k : ℕ} {Q : Set V} (hQ : Q ∈ (D.levelComplex k).walls) :
    ((D.wallIndices k Q : Finset (D.active k)) : Set (D.active k)).Pairwise
      (fun a b => Commute (CompletedGroup.projection k (D.wall a).label)
        (CompletedGroup.projection k (D.wall b).label)) := by
  intro a ha b hb _
  have hab := D.ray_eq_of_subset hQ (D.mem_wallIndices.mp ha) (D.mem_wallIndices.mp hb)
  exact (d.commute_of_mem_completedRaySubgroup ℒ (D.wall a).label_mem
    (hab ▸ (D.wall b).label_mem)).map (CompletedGroup.projection k)

/-- The order-`k` KS complex of a presentation. Each wall carries the unordered product of the
projected labels of all active indexed walls containing it, and is cooriented by a degree on
their common ray. -/
def toKSComplex (k : ℕ) : KSComplex s d ℒ (D.levelComplex k) k where
  isConical := D.isConical_levelComplex k
  degree Q := (D.wallRay Q).rayDegrees_nonempty.some
  degree_mem Q := (D.wallRay Q).rayDegrees_subset (D.wallRay Q).rayDegrees_nonempty.some_mem
  degree_ne_zero Q :=
    SupportedRay.ne_zero_of_mem_rayDegrees (D.wallRay Q).rayDegrees_nonempty.some_mem
  evaluation_eq_zero Q θ hθ :=
    (D.wall _).evaluation_eq_zero_of_mem_rayDegrees (D.wallRay Q).rayDegrees_nonempty.some_mem
      ((D.exists_subset_support_of_mem_levelComplex_walls Q.property).choose_spec hθ)
  label Q := (D.wallIndices k Q).noncommProd (fun j => CompletedGroup.projection k (D.wall j).label)
    (D.wallIndices_pairwise_commute Q.property)
  label_mem Q := by
    refine Subgroup.noncommProd_mem _ _ fun j hj => ?_
    obtain ⟨n, hn⟩ := (D.wall j).ray.rayDegrees_nonempty
    have hray : CompletedGroup.projection k (D.wall j).label ∈
        (rayLieSubalgebra (d.truncatedGrading ℒ k) (D.wall j).ray).bchSubgroup := by
      exact (LieSubalgebra.mem_bchSubgroup _ _).mpr
        ((d.mem_completedRaySubgroup ℒ _ _).mp (D.wall j).label_mem k)
    exact LieSubalgebra.bchSubgroup_le_bchSubgroup.mpr
      (s.rayLieSubalgebra_le_orthogonalLieSubalgebra (d.truncatedGrading ℒ k) hn
        (fun θ hθ => (D.wall j).evaluation_eq_zero_of_mem_rayDegrees hn
          (D.mem_wallIndices.mp hj hθ))) hray

/-- Each wall carries the unordered product of the projected labels of the active indexed walls
containing it. -/
@[simp]
theorem toKSComplex_label (k : ℕ) (Q : (D.levelComplex k).walls) :
    (D.toKSComplex k).label Q = (D.wallIndices k Q).noncommProd
      (fun j => CompletedGroup.projection k (D.wall j).label)
      (D.wallIndices_pairwise_commute Q.property) := (rfl)

/-- Each wall is cooriented by a degree on its supported ray. -/
theorem toKSComplex_degree_mem_rayDegrees (k : ℕ) (Q : (D.levelComplex k).walls) :
    (D.toKSComplex k).degree Q ∈ (D.wallRay Q).rayDegrees :=
  (D.wallRay Q).rayDegrees_nonempty.some_mem

/-- Walls of the order-`k` complex with the same affine span have commuting labels. -/
theorem commute_toKSComplex_label (k : ℕ) (Q Q' : (D.levelComplex k).walls)
    (hQQ' : affineSpan ℝ (Q : Set V) = affineSpan ℝ (Q' : Set V)) :
    Commute ((D.toKSComplex k).label Q) ((D.toKSComplex k).label Q') := by
  obtain ⟨j, hj⟩ := D.exists_subset_support_of_mem_levelComplex_walls Q.property
  obtain ⟨j', hj'⟩ := D.exists_subset_support_of_mem_levelComplex_walls Q'.property
  have hray : D.wallRay Q = D.wallRay Q' := by
    rw [D.wallRay_eq Q hj, D.wallRay_eq Q' hj']
    exact (D.wall j).ray_eq_of_affineSpan_eq (D.wall j')
      ((D.affineSpan_eq_of_subset Q.property j hj).symm.trans
        (hQQ'.trans (D.affineSpan_eq_of_subset Q'.property j' hj')))
  have hg := (D.toKSComplex k).label_mem_bchSubgroup_rayLieSubalgebra Q
    (D.toKSComplex_degree_mem_rayDegrees k Q)
  have hg' := (D.toKSComplex k).label_mem_bchSubgroup_rayLieSubalgebra Q'
    (D.toKSComplex_degree_mem_rayDegrees k Q')
  rw [← hray, LieSubalgebra.mem_bchSubgroup] at hg'
  rw [LieSubalgebra.mem_bchSubgroup] at hg
  exact BCHGroup.commute_of_lie_log_eq_zero _ _
    (lie_eq_zero_of_mem_rayLieSubalgebra (d.truncatedGrading ℒ k) hg hg')

private theorem commute_toFiniteWallDiagram_label (k : ℕ) (Q Q' : (D.levelComplex k).walls)
    (hQQ' : affineSpan ℝ (Q : Set V) = affineSpan ℝ (Q' : Set V)) :
    Commute ((D.toKSComplex k).toFiniteWallDiagram.label Q)
      ((D.toKSComplex k).toFiniteWallDiagram.label Q') := by
  simpa only [KSComplex.toFiniteWallDiagram_label] using D.commute_toKSComplex_label k Q Q' hQQ'

/-- An active indexed wall containing a wall of the order-`k` complex is crossed with the sign
of that wall's coorientation. -/
private theorem normal_pos_iff {k : ℕ} (Q : (D.levelComplex k).walls) {j : ι}
    (hj : (Q : Set V) ⊆ (D.wall j).support) (v : V) :
    0 < s.normal ((D.toKSComplex k).degree Q) v ↔ 0 < s.normal (D.wall j).ray.generator v := by
  have hn := D.toKSComplex_degree_mem_rayDegrees k Q
  rw [D.wallRay_eq Q hj] at hn
  obtain ⟨a, ha, he⟩ := s.exists_normal_eq_smul_of_mem_rayDegrees hn
  rw [he, LinearMap.smul_apply, smul_eq_mul]
  exact mul_pos_iff_of_pos_left ha

/-- If a segment crosses a wall of the order-`k` complex at a relative interior point, the
active indexed walls it crosses at that time are those containing the wall, all crossed with the
sign of the wall. -/
private theorem signedCrossingEvent_eq_map_wallIndices {k : ℕ}
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (Q : (D.levelComplex k).walls)
    (hint : AffineMap.lineMap x.val y.val t ∈ intrinsicInterior ℝ (Q : Set V)) :
    signedCrossingEvent (fun j : D.active k => s.normal (D.wall j).ray.generator) x y t =
      (D.wallIndices k Q).map ⟨fun j => (j,
        if 0 < s.normal ((D.toKSComplex k).degree Q) (y.val - x.val) then -1 else 1),
        Prod.mk_left_injective _⟩ := by
  have hQc := (D.levelComplex k).mem_cells_of_mem_walls Q.property
  ext ⟨j, s'⟩
  rw [mem_signedCrossingEvent, mem_crossings, Finset.mem_map]
  constructor
  · rintro ⟨⟨-, hzj⟩, rfl⟩
    have hsub := (D.mem_support_iff_of_mem_intrinsicInterior k hQc hint j).mp hzj
    refine ⟨j, D.mem_wallIndices.mpr hsub, ?_⟩
    simp only [Function.Embedding.coeFn_mk, D.normal_pos_iff Q hsub]
  · rintro ⟨j', hj', he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hsub := D.mem_wallIndices.mp hj'
    exact ⟨⟨ht, hsub (intrinsicInterior_subset hint)⟩, by simp only [D.normal_pos_iff Q hsub]⟩

/-- At each time, the simultaneous crossing product of the order-`k` KS complex is that of the
active indexed walls along a segment with the same endpoints. -/
private theorem crossingEventProduct_toKSComplex (k : ℕ)
    {x y : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V))}
    {x' y' : WallComplement (fun j : D.active k => (D.wall j).support)}
    (e : x ⟶ y) (e' : x' ⟶ y') (hx : x.val = x'.val) (hy : y.val = y'.val)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    crossingEventProduct (D.toKSComplex k).toFiniteWallDiagram.normal
        (D.toKSComplex k).toFiniteWallDiagram.label (D.commute_toFiniteWallDiagram_label k) e t =
      crossingEventProduct (fun j : D.active k => s.normal (D.wall j).ray.generator)
        (fun j => CompletedGroup.projection k (D.wall j).label) (D.activeLabels_commute k)
        e' t := by
  classical
  have hz : AffineMap.lineMap x'.val y'.val t = AffineMap.lineMap x.val y.val t := by
    rw [hx, hy]
  by_cases hQ : ∃ Q : (D.levelComplex k).walls, AffineMap.lineMap x.val y.val t ∈ (Q : Set V)
  · -- The segment crosses a single wall `Q`, and the indexed walls containing it.
    obtain ⟨Q, hzQ⟩ := hQ
    have hint := (e.down.crossing_mem_intrinsicInterior ht hzQ).2
    set σ : ℤ := if 0 < s.normal ((D.toKSComplex k).degree Q) (y.val - x.val) then -1 else 1
      with hσ
    have hKS := (D.levelComplex k).signedCrossingEvent_eq_singleton
      (D.toKSComplex k).toFiniteWallDiagram.normal e ((mem_crossings _ _ _ _).mpr ⟨ht, hzQ⟩)
    rw [KSComplex.toFiniteWallDiagram_normal, ← hσ] at hKS
    have hpres := D.signedCrossingEvent_eq_map_wallIndices ht Q (hz ▸ hint)
    rw [← hx, ← hy] at hpres
    rw [crossingEventProduct_singleton _ _ _ e t _ hKS,
      crossingEventProduct_eq_noncommProd _ _ _ e' t
        (signedCrossingEvent_pairwise _ _ (D.activeLabels_commute k) e' t),
      Finset.noncommProd_congr hpres (fun _ _ => rfl)]
    refine Eq.trans ?_ (Finset.noncommProd_map _ _ _ _).symm
    simp only [Function.Embedding.coeFn_mk, KSComplex.toFiniteWallDiagram_label,
      toKSComplex_label, ← hσ]
    -- The common sign is `±1`; inversion distributes over the commuting labels.
    rcases (show σ = -1 ∨ σ = 1 by rw [hσ]; split_ifs <;> simp) with hs | hs
    · simp only [hs, zpow_neg, zpow_one]
      exact (zpow_neg_one _).trans
        (Finset.noncommProd_inv (G := d.truncatedGroup ℒ k) _ _ _).symm
    · simp only [hs]
      exact (zpow_one _).trans (Finset.noncommProd_congr rfl (fun _ _ => (zpow_one _).symm) _)
  · -- No wall is crossed, hence no active support is met either.
    simp only [not_exists] at hQ
    have hKS : signedCrossingEvent (D.toKSComplex k).toFiniteWallDiagram.normal x y t = ∅ := by
      ext ⟨Q', s'⟩
      simp only [mem_signedCrossingEvent, mem_crossings, Finset.notMem_empty, iff_false]
      exact fun h => hQ Q' h.1.2
    have hpres : signedCrossingEvent (fun j : D.active k => s.normal (D.wall j).ray.generator)
        x' y' t = ∅ := by
      ext ⟨j, s'⟩
      simp only [mem_signedCrossingEvent, mem_crossings, Finset.notMem_empty, iff_false, hz]
      rintro ⟨⟨-, hzj⟩, -⟩
      obtain ⟨Q, hQw, hzQ, -⟩ := D.exists_mem_levelComplex_walls_subset k j hzj
      exact hQ ⟨Q, hQw⟩ hzQ
    exact (crossingEventProduct_empty _ _ _ e t hKS).trans
      (crossingEventProduct_empty _ _ _ e' t hpres).symm

/-- On every common vertex list, the path product of the order-`k` KS complex is the
order-`k` path product of the presentation. -/
theorem pathProduct_toKSComplex (k : ℕ)
    {x y : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V))}
    {x' y' : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    (D.toKSComplex k).toFiniteWallDiagram.pathProduct p = D.levelPathProduct k q := by
  rw [FiniteWallDiagram.pathProduct_eq_wallPathProduct _ (D.commute_toFiniteWallDiagram_label k),
    D.levelPathProduct_eq_wallPathProduct k q (D.activeLabels_commute k)]
  exact Quiver.Path.wallPathProduct_eq_of_segmentPathProduct_eq _ _ _ _ _ _
    (fun e e' hx hy => segmentPathProduct_eq_of_crossingEventProduct_eq _ _ _ _ _ _ e e'
      (fun _ ht => D.crossingEventProduct_toKSComplex k e e' hx hy ht)) p q hpq

/-- The path product of the order-`k` KS complex is the presentation's path product along the
same path with the extra cuts forgotten. -/
theorem pathProduct_toKSComplex_eq_levelPathProduct_mapPath (k : ℕ)
    {x y : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V))}
    (p : AdmissiblePLPath x y) :
    (D.toKSComplex k).toFiniteWallDiagram.pathProduct p =
      D.levelPathProduct k ((D.pathPrefunctor k).mapPath p) :=
  D.pathProduct_toKSComplex k p _ (by
    simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      pathPrefunctor_obj_val])

/-- The completed KS diagram of a presentation: its order-`k` KS complexes at every cutoff. They
are compatible because lowering the cutoff projects the presentation's path products and
forgets exactly the walls that become inactive. -/
def toCompletedDiagram : CompletedDiagram s d ℒ D.levelComplex where
  diagram := D.toKSComplex
  compatible k _ _ _ _ p q hpq := by
    rw [D.pathProduct_toKSComplex_eq_levelPathProduct_mapPath (k + 1) q,
      D.truncation_levelPathProduct (Nat.le_succ k)]
    have hq : ((D.pathPrefunctor (k + 1)).mapPath q).vertices.map WallComplement.val =
        q.vertices.map WallComplement.val := by
      simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        pathPrefunctor_obj_val]
    exact (D.pathProduct_toKSComplex k p _ (hpq.trans
      ((WallComplement.vertices_restrictPrefunctor
        (fun j : D.active (k + 1) => (D.wall j).support)
        (Set.inclusion (D.active_mono (Nat.le_succ k))) _).trans hq).symm)).symm

@[simp]
theorem toCompletedDiagram_diagram (k : ℕ) : D.toCompletedDiagram.diagram k = D.toKSComplex k :=
  (rfl)

end IndexedWallPresentation

end Mei
