/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Presentation.Splitting
public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall.Hyperplane
public import Mei.Algebra.Lie.BCH.Ray.Commensurable
public import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport
import Mei.Geometry.Convex.Polyhedron.Path.Restriction

/-!
# Walls indexed by degrees

A degree-indexed wall (`DegreeIndexedWall`) of a KS space is a rational codimension-one cone in
the hyperplane `n⊥` of a nonzero allowed degree `n`, which need not be primitive, labelled by a
completed label whose logarithmic coefficients vanish off the positive multiples `(j + 1) • n`.
A degree-indexed presentation (`DegreeIndexedPresentation`) is a family of such walls with only
finitely many labels surviving each degree cutoff; at each cutoff its active walls are
cooriented by the normals of their own degrees.

Over a free degree lattice, the following is proved.

* A degree-indexed wall is reindexed by the unique supported ray through its degree
  (`DegreeIndexedWall.toIndexedWall`), keeping its support and label: the label lies in the
  completed ray group by `PositiveDegrees.mem_completedRaySubgroup_of_logComponent_eq_zero`.
  Reindexing a presentation (`DegreeIndexedPresentation.toIndexedPresentation`) keeps the active
  walls at every order.
* With abelian rays, reindexing preserves the order-`k` path product along every admissible path
  (`DegreeIndexedPresentation.levelPathProduct_toIndexedPathPrefunctor`), and on every common
  vertex list (`DegreeIndexedPresentation.levelPathProduct_toIndexedPresentation`): each degree
  normal is a positive multiple of the normal of the ray generator.
* Reindexing commutes with degree-preserving coefficient maps
  (`DegreeIndexedPresentation.toIndexedPresentation_map`), and with abelian rays in source and
  target the order-`k` path products of a mapped presentation are the images of the original
  ones on common vertex lists (`DegreeIndexedPresentation.levelPathProduct_map`). No
  injectivity or consistency is assumed.
* Splitting an indexed wall presentation into its actual homogeneous degrees gives a
  degree-indexed presentation
  (`IndexedWallPresentation.homogeneousDegreeIndexedPresentation`), finite at each order, whose
  reindexing is the homogeneous splitting `IndexedWallPresentation.homogeneousPresentation`.
  With abelian rays its reindexing is equivalent to the original presentation, and its path
  products are those of the original presentation on common vertex lists.

This is the reindexing of walls `(n⊥, exp(⊕_{j≥1} g_{jn}))` by their primitive rays in the
abelian-ray description of scattering diagrams of Gross–Hacking–Keel–Kontsevich, *Canonical
bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), in the KS setting of Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §§2–3 (arXiv:1603.00416v4).
The path product comparison uses `Quiver.Path.wallPathProduct_smul_normal` and
`Quiver.Path.wallPathProduct_restrict`.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

universe u

variable {N V R : Type*} {L : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (s : KSSpace h) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- A rational codimension-one cone in the hyperplane `n⊥` of a nonzero allowed degree `n`,
labelled by a completed label whose logarithmic coefficients vanish off the positive multiples
`(j + 1) • n`. The degree need not be primitive, and lineality is allowed. -/
@[ext]
structure DegreeIndexedWall where
  /-- The nonzero allowed degree indexing the wall. -/
  degree : N
  /-- The indexing degree is allowed. -/
  degree_mem : degree ∈ d.monoid
  /-- The indexing degree is nonzero. -/
  degree_ne_zero : degree ≠ 0
  /-- The actual support, independent of an inequality presentation. -/
  support : Set V
  /-- The support is a cone with apex zero. -/
  isCone : ∃ σ : PointedCone ℝ V, (σ : Set V) = support
  /-- The support has rational normals. -/
  rational_support : IsRationalNormalPolyhedron h support
  /-- The support spans the hyperplane of the indexing degree. -/
  direction_support : (affineSpan ℝ support).direction = LinearMap.ker (s.normal degree)
  /-- The completed wall label. -/
  label : d.completedBCHGroup ℒ
  /-- The logarithmic coefficients of the label vanish off the positive multiples of the
  degree. -/
  logComponent_eq_zero :
    ∀ m, (∀ j : ℕ, (j + 1) • degree ≠ m) → d.logComponent ℒ label m = 0

namespace DegreeIndexedWall

variable {s d ℒ}

section Hyperplane

variable (s)

/-- The full hyperplane `n⊥` of a nonzero allowed degree `n`, labelled by a completed label `g`
whose logarithmic coefficients vanish off the positive multiples of `n`. -/
def hyperplane (n : N) (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (g : d.completedBCHGroup ℒ)
    (hg : ∀ m, (∀ j : ℕ, (j + 1) • n ≠ m) → d.logComponent ℒ g m = 0) :
    DegreeIndexedWall s d ℒ where
  degree := n
  degree_mem := hn
  degree_ne_zero := hn0
  support := LinearMap.ker (s.normal n)
  isCone := ⟨PointedCone.ofSubmodule (LinearMap.ker (s.normal n)),
    PointedCone.coe_ofSubmodule _⟩
  rational_support := s.isRationalNormalPolyhedron_ker_normal n
  direction_support := by
    rw [← Submodule.coe_toAffineSubspace, AffineSubspace.affineSpan_coe,
      Submodule.toAffineSubspace_direction]
  label := g
  logComponent_eq_zero := hg

variable (n : N) (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (g : d.completedBCHGroup ℒ)
  (hg : ∀ m, (∀ j : ℕ, (j + 1) • n ≠ m) → d.logComponent ℒ g m = 0)

@[simp]
theorem hyperplane_degree : (hyperplane s n hn hn0 g hg).degree = n := (rfl)

@[simp]
theorem hyperplane_support :
    (hyperplane s n hn hn0 g hg).support = LinearMap.ker (s.normal n) := (rfl)

@[simp]
theorem hyperplane_label : (hyperplane s n hn hn0 g hg).label = g := (rfl)

end Hyperplane

variable (W : DegreeIndexedWall s d ℒ)

section Ray

variable [Module.Free ℤ N]

/-- The supported ray through the degree of the wall. It is the only supported ray containing
that degree (`ray_eq_of_degree_mem_rayDegrees`). -/
def ray : SupportedRay d :=
  (d.exists_supportedRay W.degree_mem W.degree_ne_zero).choose

/-- The degree of the wall is an actual degree of its ray. -/
theorem degree_mem_rayDegrees : W.degree ∈ W.ray.rayDegrees :=
  (d.exists_supportedRay W.degree_mem W.degree_ne_zero).choose_spec

/-- Every supported ray containing the degree of the wall is its ray. -/
theorem ray_eq_of_degree_mem_rayDegrees {w : SupportedRay d} (hw : W.degree ∈ w.rayDegrees) :
    W.ray = w :=
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  SupportedRay.eq_of_mem_rayDegrees W.degree_mem_rayDegrees hw

/-- The label lies in the completed group of the ray through the degree. -/
theorem label_mem_completedRaySubgroup : W.label ∈ d.completedRaySubgroup ℒ W.ray :=
  d.mem_completedRaySubgroup_of_logComponent_eq_zero ℒ W.degree_mem_rayDegrees
    W.logComponent_eq_zero

/-- The normals of the degree and of the ray generator have the same kernel. -/
theorem ker_normal_generator :
    LinearMap.ker (s.normal W.ray.generator) = LinearMap.ker (s.normal W.degree) := by
  obtain ⟨a, ha, he⟩ := s.exists_normal_eq_smul_of_mem_rayDegrees W.degree_mem_rayDegrees
  rw [he, LinearMap.ker_smul _ _ ha.ne']

/-- Reindex a wall by the supported ray through its degree, keeping its support and label. -/
def toIndexedWall : IndexedWall s d ℒ where
  ray := W.ray
  support := W.support
  isCone := W.isCone
  rational_support := W.rational_support
  direction_support := W.direction_support.trans W.ker_normal_generator.symm
  label := W.label
  label_mem := W.label_mem_completedRaySubgroup

@[simp]
theorem toIndexedWall_ray : W.toIndexedWall.ray = W.ray := (rfl)

@[simp]
theorem toIndexedWall_support : W.toIndexedWall.support = W.support := (rfl)

@[simp]
theorem toIndexedWall_label : W.toIndexedWall.label = W.label := (rfl)

/-- With abelian rays, the labels of degree-indexed walls with the same affine span commute,
although their degrees may be different multiples of one primitive vector. -/
theorem commute_label [IsAbelianRays d ℒ] (W' : DegreeIndexedWall s d ℒ)
    (hWW' : affineSpan ℝ W.support = affineSpan ℝ W'.support) : Commute W.label W'.label := by
  simpa only [toIndexedWall_label] using W.toIndexedWall.commute_label W'.toIndexedWall
    (by simpa only [toIndexedWall_support] using hWW')

end Ray

section Map

variable {L' L'' : Type u} [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L']
  [IsScalarTower ℚ R L'] [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L'']
  [IsScalarTower ℚ R L'']
  {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
  {ℋ : N → Submodule R L''} [GradedLieAlgebra ℋ] [IsPositiveGrading d ℋ]
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)

/-- Apply a degree-preserving Lie homomorphism to the label, keeping the degree and support. -/
def map : DegreeIndexedWall s d ℳ where
  degree := W.degree
  degree_mem := W.degree_mem
  degree_ne_zero := W.degree_ne_zero
  support := W.support
  isCone := W.isCone
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := f.completedMap W.label
  logComponent_eq_zero m hm := by
    apply Subtype.ext
    rw [f.logComponent_completedMap, W.logComponent_eq_zero m hm]
    simp

@[simp]
theorem map_degree : (W.map f).degree = W.degree := (rfl)

@[simp]
theorem map_support : (W.map f).support = W.support := (rfl)

@[simp]
theorem map_label : (W.map f).label = f.completedMap W.label := (rfl)

/-- The identity coefficient map fixes every degree-indexed wall. -/
@[simp]
theorem map_id : W.map (GradedLieHom.id ℒ) = W := by
  apply DegreeIndexedWall.ext <;> simp

/-- Successive coefficient maps agree with the composite on degree-indexed walls. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (W.map f).map g = W.map (g.compId f) := by
  apply DegreeIndexedWall.ext <;>
    simp only [map_degree, map_support, map_label, GradedLieHom.completedMap_compId,
      MonoidHom.comp_apply]

variable [Module.Free ℤ N]

/-- A coefficient map keeps the ray of a degree-indexed wall. -/
@[simp]
theorem map_ray : (W.map f).ray = W.ray :=
  (W.map f).ray_eq_of_degree_mem_rayDegrees W.degree_mem_rayDegrees

/-- Reindexing by rays commutes with degree-preserving coefficient maps. -/
@[simp]
theorem toIndexedWall_map : (W.map f).toIndexedWall = W.toIndexedWall.map f := by
  apply IndexedWall.ext <;> simp

end Map

end DegreeIndexedWall

/-- A family of degree-indexed walls with only finitely many labels surviving each degree
cutoff. Repeated walls retain distinct indices. -/
@[ext]
structure DegreeIndexedPresentation (ι : Type*) where
  /-- The degree-indexed walls, with their supports and completed labels. -/
  wall : ι → DegreeIndexedWall s d ℒ
  /-- Only finitely many labels are nonidentity at any fixed order. -/
  finite_active : CompletedGroup.HasFiniteSupport (fun j => (wall j).label)

namespace DegreeIndexedPresentation

variable {s d ℒ} {ι : Type*} (D : DegreeIndexedPresentation s d ℒ ι)

/-- The indices whose labels survive the order-`k` projection. -/
def active (k : ℕ) : Set ι :=
  Function.mulSupport (fun j => CompletedGroup.projection k (D.wall j).label)

/-- Activity is exactly nontriviality of the projected label. -/
@[simp]
theorem mem_active (k : ℕ) (j : ι) :
    j ∈ D.active k ↔ CompletedGroup.projection k (D.wall j).label ≠ 1 := Iff.rfl

/-- The active wall index type is finite at every order. -/
instance finiteActive (k : ℕ) : Finite (D.active k) :=
  Set.finite_coe_iff.mpr (D.finite_active k)

section Ray

variable [Module.Free ℤ N]

/-- Reindex every wall by the supported ray through its degree, keeping the indices. -/
def toIndexedPresentation : IndexedWallPresentation s d ℒ ι where
  wall j := (D.wall j).toIndexedWall
  finite_active := by
    simpa only [DegreeIndexedWall.toIndexedWall_label] using D.finite_active

@[simp]
theorem toIndexedPresentation_wall (j : ι) :
    D.toIndexedPresentation.wall j = (D.wall j).toIndexedWall := (rfl)

/-- Reindexing keeps the active walls at every order. -/
@[simp]
theorem active_toIndexedPresentation (k : ℕ) : D.toIndexedPresentation.active k = D.active k := by
  ext j
  simp only [IndexedWallPresentation.mem_active, mem_active, toIndexedPresentation_wall,
    DegreeIndexedWall.toIndexedWall_label]

/-- The complement of the active degree-indexed walls is the complement of the active walls of
the reindexed presentation, with the same ambient points. -/
def toIndexedPathPrefunctor (k : ℕ) :
    WallComplement (fun j : D.active k => (D.wall j).support) ⥤q
      WallComplement (fun j : D.toIndexedPresentation.active k =>
        (D.toIndexedPresentation.wall j).support) :=
  -- The two families agree after unfolding the reindexed supports.
  WallComplement.restrictPrefunctor (fun j : D.active k => (D.wall j).support)
    (Set.inclusion (D.active_toIndexedPresentation k).le)

@[simp]
theorem toIndexedPathPrefunctor_obj_val (k : ℕ)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    ((D.toIndexedPathPrefunctor k).obj x).val = x.val := (rfl)

/-- The identification of complements preserves every ambient vertex. -/
theorem vertices_toIndexedPathPrefunctor (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    ((D.toIndexedPathPrefunctor k).mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    toIndexedPathPrefunctor_obj_val]

variable [IsAbelianRays d ℒ]

/-- With abelian rays, the projected labels of active walls with the same affine span
commute. -/
theorem activeLabels_commute (k : ℕ) (a b : D.active k)
    (hab : affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support) :
    Commute (CompletedGroup.projection k (D.wall a).label)
      (CompletedGroup.projection k (D.wall b).label) :=
  ((D.wall a).commute_label (D.wall b) hab).map (CompletedGroup.projection k)

/-- The order-`k` transport along a path admissible for the finite active wall family, with
abelian rays. Each wall is cooriented by the normal of its own degree. -/
def levelPathProduct (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) : d.truncatedGroup ℒ k :=
  p.wallPathProduct (fun j : D.active k => s.normal (D.wall j).degree)
    (fun j => CompletedGroup.projection k (D.wall j).label) (D.activeLabels_commute k)

/-- The wall-family product characterizes finite-order transport, independently of which proof
of coplanar commutation is used. -/
theorem levelPathProduct_eq_wallPathProduct (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y)
    (comm : ∀ a b : D.active k,
      affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support →
        Commute (CompletedGroup.projection k (D.wall a).label)
          (CompletedGroup.projection k (D.wall b).label)) :
    D.levelPathProduct k p =
      p.wallPathProduct (fun j : D.active k => s.normal (D.wall j).degree)
        (fun j => CompletedGroup.projection k (D.wall j).label) comm := (rfl)

/-- With abelian rays, reindexing by rays preserves the order-`k` transport along every
admissible path: coorienting a wall by its degree or by its ray generator gives the same
crossing signs. -/
theorem levelPathProduct_toIndexedPathPrefunctor (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.toIndexedPresentation.levelPathProduct k ((D.toIndexedPathPrefunctor k).mapPath p) =
      D.levelPathProduct k p := by
  -- Each degree normal is a positive multiple of the normal of its ray generator.
  choose r hr he using fun j : D.active k =>
    s.exists_normal_eq_smul_of_mem_rayDegrees (D.wall j).degree_mem_rayDegrees
  have hν : (fun j : D.active k => s.normal (D.wall j).degree) =
      fun j => r j • s.normal (D.wall j).ray.generator := funext he
  -- The reindexed family forgets no active wall.
  have hres := p.wallPathProduct_restrict
    (fun j : D.active k => s.normal (D.wall j).ray.generator)
    (fun j => CompletedGroup.projection k (D.wall j).label) (D.activeLabels_commute k)
    (Set.inclusion (D.active_toIndexedPresentation k).le) (Set.inclusion_injective _)
    (fun j hj => (hj ⟨⟨j.val, by simp⟩, Subtype.ext rfl⟩).elim)
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k), hν,
    p.wallPathProduct_smul_normal _ r hr, ← hres,
    IndexedWallPresentation.levelPathProduct_eq_wallPathProduct _ k _
      (D.toIndexedPresentation.activeLabels_commute k)]
  exact Quiver.Path.wallPathProduct_congr _ (funext fun j => by simp) (funext fun j => by simp)

/-- With abelian rays, reindexing by rays preserves the order-`k` transport on every common
admissible vertex list. -/
theorem levelPathProduct_toIndexedPresentation (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement (fun j : D.toIndexedPresentation.active k =>
      (D.toIndexedPresentation.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    D.levelPathProduct k p = D.toIndexedPresentation.levelPathProduct k q := by
  rw [← D.levelPathProduct_toIndexedPathPrefunctor k p]
  exact (D.toIndexedPresentation.levelEquivalent_def _ k).mp
    (IndexedWallPresentation.LevelEquivalent.refl _ k) _ q
    ((D.vertices_toIndexedPathPrefunctor k p).trans hpq)

end Ray

section Map

variable {L' L'' : Type u} [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L']
  [IsScalarTower ℚ R L'] [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L'']
  [IsScalarTower ℚ R L'']
  {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
  {ℋ : N → Submodule R L''} [GradedLieAlgebra ℋ] [IsPositiveGrading d ℋ]
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)

/-- Change every completed label, keeping degrees, supports and indices. -/
def map : DegreeIndexedPresentation s d ℳ ι where
  wall j := (D.wall j).map f
  finite_active := by
    simpa only [DegreeIndexedWall.map_label] using f.hasFiniteSupport_completedMap D.finite_active

@[simp]
theorem map_wall (j : ι) : (D.map f).wall j = (D.wall j).map f := (rfl)

/-- The identity coefficient map fixes the whole presentation. -/
@[simp]
theorem map_id : D.map (GradedLieHom.id ℒ) = D := by
  apply DegreeIndexedPresentation.ext
  funext j
  simp

/-- Successive coefficient changes agree with the composite on presentations. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.map f).map g = D.map (g.compId f) := by
  apply DegreeIndexedPresentation.ext
  funext j
  simp only [map_wall, DegreeIndexedWall.map_map]

variable [Module.Free ℤ N]

/-- Reindexing by rays commutes with degree-preserving coefficient maps. -/
@[simp]
theorem toIndexedPresentation_map :
    (D.map f).toIndexedPresentation = D.toIndexedPresentation.map f := by
  apply IndexedWallPresentation.ext
  funext j
  simp

variable [IsAbelianRays d ℒ] [IsAbelianRays d ℳ]

/-- With abelian rays in source and target, changing coefficients maps the order-`k` transport
on every common admissible vertex list. Labels killed by the map are allowed; no injectivity or
consistency is assumed. -/
theorem levelPathProduct_map (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement (fun j : (D.map f).active k => ((D.map f).wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    (D.map f).levelPathProduct k q =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.levelPathProduct k p) := by
  -- Compare along the reindexed path, then use coefficient naturality of indexed walls.
  have hr := (D.toIndexedPresentation.vertices_mapPathPrefunctor f k
    ((D.toIndexedPathPrefunctor k).mapPath p)).trans
      ((D.vertices_toIndexedPathPrefunctor k p).trans hpq)
  have hE :
      (D.map f).toIndexedPresentation.LevelEquivalent (D.toIndexedPresentation.map f) k := by
    rw [D.toIndexedPresentation_map f]
    exact IndexedWallPresentation.LevelEquivalent.refl _ k
  rw [← D.levelPathProduct_toIndexedPathPrefunctor k p,
    ← D.toIndexedPresentation.levelPathProduct_mapPathPrefunctor f k,
    ← (D.map f).levelPathProduct_toIndexedPathPrefunctor k q]
  exact ((IndexedWallPresentation.levelEquivalent_def _ _ k).mp hE) _ _
    (((D.map f).vertices_toIndexedPathPrefunctor k q).trans hr.symm)

end Map

end DegreeIndexedPresentation

namespace IndexedWall

variable {s d ℒ} (W : IndexedWall s d ℒ)

/-- The homogeneous factor of an indexed wall in an actual degree `n` of its ray, as a wall
indexed by `n` with the original support. -/
def degreeIndexedFactor {n : N} (hn : n ∈ W.ray.rayDegrees) : DegreeIndexedWall s d ℒ where
  degree := n
  degree_mem := W.ray.rayDegrees_subset hn
  degree_ne_zero := SupportedRay.ne_zero_of_mem_rayDegrees hn
  support := W.support
  isCone := W.isCone
  rational_support := W.rational_support
  direction_support := (W.ker_normal_of_mem_rayDegrees hn).symm
  label := d.homogeneousFactor ℒ W.label n
  logComponent_eq_zero m hm :=
    d.logComponent_homogeneousFactor_of_ne ℒ W.label (by simpa using hm 0)

variable {n : N} (hn : n ∈ W.ray.rayDegrees)

@[simp]
theorem degreeIndexedFactor_degree : (W.degreeIndexedFactor hn).degree = n := (rfl)

@[simp]
theorem degreeIndexedFactor_support : (W.degreeIndexedFactor hn).support = W.support := (rfl)

@[simp]
theorem degreeIndexedFactor_label :
    (W.degreeIndexedFactor hn).label = d.homogeneousFactor ℒ W.label n := (rfl)

/-- Reindexing a homogeneous degree-indexed factor by its ray gives the homogeneous factor of
the indexed wall. -/
@[simp]
theorem toIndexedWall_degreeIndexedFactor [Module.Free ℤ N] :
    (W.degreeIndexedFactor hn).toIndexedWall = W.homogeneousFactor n := by
  apply IndexedWall.ext
  · simpa using (W.degreeIndexedFactor hn).ray_eq_of_degree_mem_rayDegrees (w := W.ray)
      (by simpa using hn)
  · simp
  · simp

end IndexedWall

namespace IndexedWallPresentation

variable {s d ℒ} {ι : Type*} (D : IndexedWallPresentation s d ℒ ι)

/-- Split every indexed wall into its actual homogeneous degrees, each indexed by its degree.
This is finite at every order, without abelian rays. -/
def homogeneousDegreeIndexedPresentation : DegreeIndexedPresentation s d ℒ D.HomogeneousIndex where
  wall a := (D.wall a.1).degreeIndexedFactor a.2.property
  finite_active := by
    simpa only [homogeneousPresentation_wall, IndexedWall.homogeneousFactor_label,
      IndexedWall.degreeIndexedFactor_label] using D.homogeneousPresentation.finite_active

@[simp]
theorem homogeneousDegreeIndexedPresentation_wall (a : D.HomogeneousIndex) :
    D.homogeneousDegreeIndexedPresentation.wall a =
      (D.wall a.1).degreeIndexedFactor a.2.property := (rfl)

/-- The degree-indexed splitting has the active walls of the homogeneous splitting. -/
@[simp]
theorem active_homogeneousDegreeIndexedPresentation (k : ℕ) :
    D.homogeneousDegreeIndexedPresentation.active k = D.homogeneousPresentation.active k := by
  ext a
  simp only [DegreeIndexedPresentation.mem_active, mem_active,
    homogeneousDegreeIndexedPresentation_wall, IndexedWall.degreeIndexedFactor_label,
    homogeneousPresentation_wall, IndexedWall.homogeneousFactor_label]

variable [Module.Free ℤ N]

/-- Reindexing the degree-indexed splitting by rays gives the homogeneous splitting. -/
@[simp]
theorem toIndexedPresentation_homogeneousDegreeIndexedPresentation :
    D.homogeneousDegreeIndexedPresentation.toIndexedPresentation = D.homogeneousPresentation := by
  apply IndexedWallPresentation.ext
  funext a
  simp

variable [IsAbelianRays d ℒ]

/-- With abelian rays, reindexing the degree-indexed splitting by rays gives a presentation
equivalent to the original one. -/
theorem toIndexedPresentation_homogeneousDegreeIndexedPresentation_equivalent :
    D.homogeneousDegreeIndexedPresentation.toIndexedPresentation.Equivalent D := by
  rw [toIndexedPresentation_homogeneousDegreeIndexedPresentation]
  exact D.homogeneousPresentation_equivalent

/-- With abelian rays, the degree-indexed splitting has the order-`k` transport of the original
presentation on every common admissible vertex list. -/
theorem levelPathProduct_homogeneousDegreeIndexedPresentation (k : ℕ)
    {x y : WallComplement (fun a : D.homogeneousDegreeIndexedPresentation.active k =>
      (D.homogeneousDegreeIndexedPresentation.wall a).support)}
    {x' y' : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    D.homogeneousDegreeIndexedPresentation.levelPathProduct k p = D.levelPathProduct k q := by
  rw [← D.homogeneousDegreeIndexedPresentation.levelPathProduct_toIndexedPathPrefunctor k p]
  exact (levelEquivalent_def _ _ k).mp
    ((equivalent_iff _ _).mp D.toIndexedPresentation_homogeneousDegreeIndexedPresentation_equivalent
      k) _ q
    ((D.homogeneousDegreeIndexedPresentation.vertices_toIndexedPathPrefunctor k p).trans hpq)

end IndexedWallPresentation

end Mei
