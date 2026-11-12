/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Completion
public import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport
import Mei.Geometry.Convex.Polyhedron.Path.Restriction

/-!
# Pushing directed diagrams forward along degree-changing maps

A `DirectedWall.Pushforward` pushes every indexed wall of a directed diagram forward,
preserving finite activity through the cutoff modulus of the positive degree map. At
target order `k`, paths are pushed forward from any source cutoff `a` covering the
modulus: first the walls whose labels die at order `k` are forgotten, then the path is
moved by the spatial affine equivalence. The finite path product is carried by the
truncated BCH homomorphism, and common all-order paths give naturality of completed
path products.

Image normals are only positive rational multiples of the inverse-dual normals, as for
tropical pairings of finite-index lattices; positive rescaling of normals does not change
path products. The fixed-degree coefficient maps `DirectedDiagram.map` and the coordinate
changes `DirectedDiagram.image` are special cases. The setting is Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Example 2.1(i).
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' ι : Type*} {L L' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [DecidableEq Γ] [DecidableEq Γ']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (D : DirectedDiagram (d := d) h H ι)
  (P : DirectedWall.Pushforward d d' h h' H H')

/-- Push every indexed wall forward. Finite activity is preserved through the cutoff
modulus of the degree map. -/
def pushforward : DirectedDiagram (d := d') h' H' ι where
  wall j := (D.wall j).pushforward P
  finite_active := by
    simpa only [DirectedWall.pushforward_label] using
      P.lieHom.hasFiniteSupport_completedMap D.finite_active

/-- Diagram pushforward pushes every indexed wall forward. -/
@[simp]
theorem pushforward_wall (j : ι) : (D.pushforward P).wall j = (D.wall j).pushforward P :=
  (rfl)

/-- The pushed support of an indexed wall is the spatial image of its support. -/
theorem pushforward_wall_support (j : ι) :
    ((D.pushforward P).wall j).support = P.spatialMap '' (D.wall j).support := by
  rw [pushforward_wall, DirectedWall.pushforward_support]

/-- A target-active label was active at any source order covering the modulus. -/
theorem active_pushforward_subset (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    (D.pushforward P).active k ⊆ D.active a := by
  simpa only [Set.subset_def, mem_active, Function.mem_mulSupport, pushforward_wall,
    DirectedWall.pushforward_label] using
    P.lieHom.mulSupport_projection_completedMap_subset (fun j => (D.wall j).label) k ha

/-- The order-`k` label of a pushed wall is the truncated image of its order-`a` label. -/
theorem projection_pushforward_wall_label (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (j : ι) : CompletedGroup.projection k ((D.pushforward P).wall j).label =
      (P.lieHom.truncatedMap k ha).bchGroupMap (CompletedGroup.projection a (D.wall j).label) := by
  rw [pushforward_wall, DirectedWall.pushforward_label]
  exact P.lieHom.projection_completedMap_of_le k ha _

/-- Move a path avoiding the source walls that survive at target order `k` by the spatial
affine equivalence. -/
def survivingPathPushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    WallComplement ((fun j : D.active a => (D.wall j).support) ∘
      Set.inclusion (D.active_pushforward_subset P k ha)) ⥤q
      WallComplement (fun j : (D.pushforward P).active k =>
        ((D.pushforward P).wall j).support) :=
  P.spatialMap.wallComplementMap (Equiv.refl _) (fun j => D.pushforward_wall_support P j)

/-- Restrict a source path to the target-active indices and then apply the spatial
affine equivalence. The source cutoff can be any bound for the prescribed modulus. -/
def levelPathPushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    WallComplement (fun j : D.active a => (D.wall j).support) ⥤q
      WallComplement (fun j : (D.pushforward P).active k =>
        ((D.pushforward P).wall j).support) :=
  WallComplement.restrictPrefunctor (fun j : D.active a => (D.wall j).support)
      (Set.inclusion (D.active_pushforward_subset P k ha)) ⋙q
    D.survivingPathPushforward P k ha

/-- The finite path map sends each vertex to its spatial image. -/
@[simp]
theorem levelPathPushforward_obj_val (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (x : WallComplement (fun j : D.active a => (D.wall j).support)) :
    ((D.levelPathPushforward P k ha).obj x).val = P.spatialMap x.val :=
  ContinuousAffineEquiv.wallComplementMap_obj_val _ _ _ _

/-- Finite path pushforward preserves reversal of segments and polygonal paths. -/
instance (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    (D.levelPathPushforward P k ha).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- A finite path product along a pushed path is the product along the restricted path
moved by the spatial map. -/
theorem levelPathProduct_levelPathPushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    {x y : WallComplement (fun j : D.active a => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.pushforward P).levelPathProduct k ((D.levelPathPushforward P k ha).mapPath p) =
      (D.pushforward P).levelPathProduct k ((D.survivingPathPushforward P k ha).mapPath
        ((WallComplement.restrictPrefunctor _
          (Set.inclusion (D.active_pushforward_subset P k ha))).mapPath p)) := by
  rw [levelPathPushforward, Prefunctor.mapPath_comp_apply]
  -- The endpoints `(F ⋙q G).obj x` and `G.obj (F.obj x)` agree by definition.
  rfl

/-- Forgetting the walls whose truncated labels die does not change a source product with
truncated labels. -/
private theorem wallPathProduct_restrict_pushforward (k : ℕ) {a : ℕ}
    (ha : P.degreeMap.modulus k ≤ a)
    {x y : WallComplement (fun j : D.active a => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    ((WallComplement.restrictPrefunctor _
        (Set.inclusion (D.active_pushforward_subset P k ha))).mapPath p).wallPathProduct
        (fun j : (D.pushforward P).active k => h.realCharacter (D.wall j).normal)
        (fun j : (D.pushforward P).active k => (P.lieHom.truncatedMap k ha).bchGroupMap
          (CompletedGroup.projection a (D.wall j).label))
        (fun j l hjl => (D.activeLabels_commute a (Set.inclusion _ j) (Set.inclusion _ l)
          hjl).map _) =
      p.wallPathProduct (fun j : D.active a => h.realCharacter (D.wall j).normal)
        (fun j : D.active a => (P.lieHom.truncatedMap k ha).bchGroupMap
          (CompletedGroup.projection a (D.wall j).label))
        (fun j l hjl => (D.activeLabels_commute a j l hjl).map _) := by
  refine p.wallPathProduct_restrict (fun j : D.active a => h.realCharacter (D.wall j).normal)
    (fun j : D.active a => (P.lieHom.truncatedMap k ha).bchGroupMap
      (CompletedGroup.projection a (D.wall j).label))
    (fun j l hjl => (D.activeLabels_commute a j l hjl).map _) _ (Set.inclusion_injective _)
    fun j hj => ?_
  rw [← projection_pushforward_wall_label]
  by_contra hne
  exact hj ⟨⟨j.val, ((D.pushforward P).mem_active k j.val).mpr hne⟩, rfl⟩

/-- On the surviving walls, the spatial map carries the source product, taken with the
source normals, to the target product. -/
private theorem wallPathProduct_wallComplementMap_pushforward (k : ℕ) {a : ℕ}
    (ha : P.degreeMap.modulus k ≤ a)
    {x y : WallComplement ((fun j : D.active a => (D.wall j).support) ∘
      Set.inclusion (D.active_pushforward_subset P k ha))}
    (q : AdmissiblePLPath x y) :
    ((D.survivingPathPushforward P k ha).mapPath q).wallPathProduct
        (fun j : (D.pushforward P).active k => h'.realCharacter ((D.pushforward P).wall j).normal)
        (fun j : (D.pushforward P).active k =>
          CompletedGroup.projection k ((D.pushforward P).wall j).label)
        ((D.pushforward P).activeLabels_commute k) =
      (P.lieHom.truncatedMap k ha).bchGroupMap (q.wallPathProduct
        (fun j : (D.pushforward P).active k => h.realCharacter (D.wall j).normal)
        (fun j : (D.pushforward P).active k => CompletedGroup.projection a (D.wall j).label)
        (fun j l hjl => D.activeLabels_commute a (Set.inclusion _ j) (Set.inclusion _ l) hjl)) := by
  let r : (D.pushforward P).active k → ℝ :=
    fun j => ((P.realCharacter_normalMap (D.wall j).normal).choose : ℝ)
  have hs := q.wallPathProduct_smul_normal (fun j => h.realCharacter (D.wall j).normal) r
    (fun j => Rat.cast_pos.mpr (P.realCharacter_normalMap (D.wall j).normal).choose_spec.1)
    (fun j => CompletedGroup.projection a (D.wall j).label)
    (fun j l hjl => D.activeLabels_commute a (Set.inclusion _ j) (Set.inclusion _ l) hjl)
  refine (q.wallPathProduct_wallComplementMap P.spatialMap (Equiv.refl _) _
    (fun j => r j • h.realCharacter (D.wall j).normal) _ (fun j => ?_) _ _ _ _ _
    (fun j => D.projection_pushforward_wall_label P k ha j)).trans (congrArg _ hs)
  rw [Equiv.refl_apply, pushforward_wall, DirectedWall.pushforward_normal]
  exact (P.realCharacter_normalMap (D.wall j).normal).choose_spec.2

/-- Finite directed transport is natural under pushforward, using the truncated BCH map
at any source cutoff covering the target modulus. Walls whose labels die are forgotten,
and image normals may be positive multiples of the inverse-dual normals. -/
@[simp]
theorem levelPathProduct_pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    {x y : WallComplement (fun j : D.active a => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.pushforward P).levelPathProduct k ((D.levelPathPushforward P k ha).mapPath p) =
      (P.lieHom.truncatedMap k ha).bchGroupMap (D.levelPathProduct a p) := by
  rw [levelPathProduct_levelPathPushforward, levelPathProduct_eq_wallPathProduct _ k _
      ((D.pushforward P).activeLabels_commute k),
    D.levelPathProduct_eq_wallPathProduct a p (D.activeLabels_commute a),
    wallPathProduct_wallComplementMap_pushforward]
  exact (Quiver.Path.map_wallPathProduct _ _ _ _ _).trans
    ((D.wallPathProduct_restrict_pushforward P k ha p).trans
      (Quiver.Path.map_wallPathProduct _ _ _ _ p).symm)

/-- Push an all-order allowed point forward by the spatial map. -/
def pointPushforward (x : D.Point) : (D.pushforward P).Point :=
  ⟨P.spatialMap x.val, fun k j => by
    have hx := ((D.levelPathPushforward P k le_rfl).obj
      (CommonWallComplement.projection (P.degreeMap.modulus k) x)).notMem j
    simpa only [levelPathPushforward_obj_val, CommonWallComplement.projection_val] using hx⟩

/-- A pushed point is the spatial image of the original point. -/
@[simp]
theorem pointPushforward_val (x : D.Point) :
    (D.pointPushforward P x).val = P.spatialMap x.val := (rfl)

/-- Projecting a pushed point agrees with pushing its projection from the source cutoff
selected by the modulus. -/
theorem projection_pointPushforward (k : ℕ) (x : D.Point) :
    CommonWallComplement.projection k (D.pointPushforward P x) =
      (D.levelPathPushforward P k le_rfl).obj
        (CommonWallComplement.projection (P.degreeMap.modulus k) x) := by
  apply WallComplement.ext
  rw [levelPathPushforward_obj_val, CommonWallComplement.projection_val,
    CommonWallComplement.projection_val, pointPushforward_val]

/-- Push a common all-order path forward. Each target admissibility condition uses the
source condition at its prescribed cutoff modulus. -/
def pathPushforward : D.Point ⥤q (D.pushforward P).Point where
  obj := D.pointPushforward P
  map {x y} a := ⟨fun k => by
    rw [projection_pointPushforward, projection_pointPushforward]
    exact ((D.levelPathPushforward P k le_rfl).map
      ((CommonWallComplement.projectionPrefunctor (P.degreeMap.modulus k)).map a)).down⟩

/-- All-order allowed points move by the spatial affine equivalence. -/
@[simp]
theorem pathPushforward_obj_val (x : D.Point) :
    ((D.pathPushforward P).obj x).val = P.spatialMap x.val := (rfl)

/-- All-order path pushforward preserves reversal. -/
instance : (D.pathPushforward P).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projecting a pushed common path agrees with pushing its projection from the source
cutoff selected by the modulus. -/
theorem pathPushforward_comp_projection (k : ℕ) :
    D.pathPushforward P ⋙q CommonWallComplement.projectionPrefunctor k =
      CommonWallComplement.projectionPrefunctor (P.degreeMap.modulus k) ⋙q
        D.levelPathPushforward P k le_rfl := by
  refine Prefunctor.ext (fun x => ?_) (fun _ _ _ => PLift.ext (Subsingleton.elim _ _))
  apply WallComplement.ext
  simp

/-- Pushforward carries completed directed path products through the completed BCH
group homomorphism of the graded Lie map. -/
@[simp]
theorem pathProduct_pushforward {x y : D.Point} (p : Quiver.Path x y) :
    (D.pushforward P).pathProduct ((D.pathPushforward P).mapPath p) =
      P.lieHom.completedMap (D.pathProduct p) := by
  apply CompletedGroup.ext
  intro k
  have hp := congrArg
    (fun F : D.Point ⥤q WallComplement
        (fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support) =>
      (D.pushforward P).levelPathProduct k (F.mapPath p))
    (D.pathPushforward_comp_projection P k)
  simp only [Prefunctor.mapPath_comp_apply] at hp
  rw [projection_pathProduct, P.lieHom.projection_completedMap, projection_pathProduct]
  exact hp.trans (D.levelPathProduct_pushforward P k le_rfl
    ((CommonWallComplement.projectionPrefunctor (P.degreeMap.modulus k)).mapPath p))

section Composition

variable {Γ'' Λ'' V'' : Type*} {L'' : Type u} [AddCommGroup Γ''] [AddCommGroup Λ'']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ''] {ρ'' : Γ'' →+ Λ''} {ℋ : Γ'' → Submodule R L''}
  {d'' : PositiveDegrees Γ''} [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
  {i'' : Λ'' →+ V''} {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H'' : DirectedWallSpaces ρ'' ℋ}

/-- Successive diagram pushforwards agree with the pushforward along the composite. -/
@[simp]
theorem pushforward_pushforward (Q : DirectedWall.Pushforward d' d'' h' h'' H' H'') :
    (D.pushforward P).pushforward Q = D.pushforward (Q.comp P) := by
  apply DirectedDiagram.ext
  funext j
  simp

end Composition

end Mei.DirectedDiagram
