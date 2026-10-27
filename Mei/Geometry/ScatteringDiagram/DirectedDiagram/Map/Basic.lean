/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Map
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness
import Mei.Geometry.Convex.Polyhedron.Path.Restriction
import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport

/-!
# Coefficient maps of directed scattering diagrams

A fixed-degree Lie homomorphism preserving wall spaces maps every indexed label.
The active wall family can shrink: a noninjective coefficient map may kill a
label. Transport along an original admissible path maps to transport along the
same path after forgetting the killed walls. Consistency is preserved for all
paths of the resulting diagram, including those through supports that disappear.

The transport calculation combines `GradedLieHom.completedMap` with
`Quiver.Path.map_wallPathProduct` and `Quiver.Path.wallPathProduct_restrict`,
following the restriction-and-transport calculation in
`DirectedDiagram.levelPathProduct_image`.
The all-order path map and its completed product formula follow the projection
argument in `DirectedDiagram.pathImage` and `DirectedDiagram.pathProduct_image`.
The consistency proof uses `exists_loop_levelPathProduct_eq_of_vertices_eq` to
move a loop off the original active supports while retaining its mapped product.
Together with outgoingness of mapped walls, this gives coefficient naturality
of outgoing completions. No faithful action or injective coefficient map is needed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Λ R V ι : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'} {ℋ : Γ → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  {H'' : DirectedWallSpaces ρ ℋ}
  (D : DirectedDiagram (d := d) h H ι)
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m)

/-- Apply a fixed-degree coefficient map to every wall label, retaining its index. -/
def map : DirectedDiagram (d := d) h H' ι where
  wall j := (D.wall j).map f hf
  finite_active := by
    simpa only [DirectedWall.map_label] using f.hasFiniteSupport_completedMap D.finite_active

@[simp]
theorem map_wall (j : ι) : (D.map f hf).wall j = (D.wall j).map f hf := (rfl)

/-- Coefficient maps can only remove active walls. -/
theorem active_map_subset (k : ℕ) : (D.map f hf).active k ⊆ D.active k := by
  simp only [Set.subset_def, mem_active, map_wall, DirectedWall.map_label,
    f.projection_completedMap_of_le k (a := k) (by simp)]
  -- Identify categorical tower identities with the concrete BCH quotient identities.
  convert Function.mulSupport_comp_subset
    (f.truncatedMap k (a := k) (by simp)).bchGroupMap.map_one
    (fun j => CompletedGroup.projection k (D.wall j).label) using 1
  rfl

/-- The identity coefficient map fixes the indexed diagram. -/
@[simp]
theorem map_id : D.map (GradedLieHom.id ℒ) (fun _ _ _ hx => by simpa using hx) = D := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Successive coefficient maps agree with their composite on indexed diagrams. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (hg : ∀ n m, ∀ x ∈ H'.wall n m, g x ∈ H''.wall n m) :
    (D.map f hf).map g hg = D.map
      { toLieHom := g.toLieHom.comp f.toLieHom
        map_mem hx := by simpa using g.map_mem (f.map_mem hx) }
      (fun n m x hx => hg n m _ (hf n m x hx)) := by
  apply DirectedDiagram.ext
  funext j
  simp only [map_wall, DirectedWall.map_map]
  rfl

/-- Forget the walls whose labels the coefficient map kills at the chosen cutoff. -/
def mapPathPrefunctor (k : ℕ) :
    WallComplement (fun j : D.active k => (D.wall j).support) ⥤q
      WallComplement (fun j : (D.map f hf).active k => ((D.map f hf).wall j).support) :=
  WallComplement.restrictPrefunctor (fun j : D.active k => (D.wall j).support)
      (Set.inclusion (D.active_map_subset f hf k)) ⋙q
    (ContinuousAffineEquiv.refl ℝ V).wallComplementMap (Equiv.refl _) (by
      intro j
      ext v
      simp)

@[simp]
theorem mapPathPrefunctor_obj_val (k : ℕ)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    ((D.mapPathPrefunctor f hf k).obj x).val = x.val := by
  simp [mapPathPrefunctor]

/-- Mapping coefficients preserves the actual finite-order product on the same
ambient path, including simultaneous crossings and labels that become trivial. -/
@[simp]
theorem levelPathProduct_mapPathPrefunctor (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.map f hf).levelPathProduct k ((D.mapPathPrefunctor f hf k).mapPath p) =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.levelPathProduct k p) := by
  let a := Set.inclusion (D.active_map_subset f hf k)
  let q := (WallComplement.restrictPrefunctor
    (fun j : D.active k => (D.wall j).support) a).mapPath p
  let F := (f.truncatedMap (a := k) k (by simp)).bchGroupMap
  have hlabel (j : ι) : CompletedGroup.projection k ((D.map f hf).wall j).label =
      F (CompletedGroup.projection k (D.wall j).label) := by
    rw [map_wall, DirectedWall.map_label,
      f.projection_completedMap_of_le k (a := k) (by simp)]
  have hzero (j : D.active k) (hj : j ∉ range a) :
      F (CompletedGroup.projection k (D.wall j).label) = 1 := by
    rw [← hlabel]
    by_contra hne
    exact hj ⟨⟨j.val, ((D.map f hf).mem_active k j.val).mpr hne⟩, Subtype.ext rfl⟩
  -- Delete the source-active labels whose finite images are trivial.
  have hr := p.wallPathProduct_restrict
    (fun j : D.active k => h.realCharacter (D.wall j).normal)
    (fun j => F (CompletedGroup.projection k (D.wall j).label))
    (fun j l hab => (D.activeLabels_commute k j l hab).map F)
    a (Set.inclusion_injective _) hzero
  -- The identity affine map identifies the surviving supports without exposing wall bodies.
  have hi := q.wallPathProduct_wallComplementMap (ContinuousAffineEquiv.refl ℝ V)
    (Equiv.refl _)
    (W' := fun j : (D.map f hf).active k => ((D.map f hf).wall j).support)
    (by intro j; simp [a])
    (fun j => h.realCharacter (D.wall (a j)).normal)
    (fun j => h.realCharacter ((D.map f hf).wall j).normal)
    (by intro j; ext v; simp [a])
    (fun j => F (CompletedGroup.projection k (D.wall (a j)).label))
    (fun j => CompletedGroup.projection k ((D.map f hf).wall j).label)
    (fun j l hab => (D.activeLabels_commute k (a j) (a l) hab).map F)
    ((D.map f hf).activeLabels_commute k) (MonoidHom.id _)
    (fun j => hlabel j)
  have hm' := p.map_wallPathProduct
    (fun j : D.active k => h.realCharacter (D.wall j).normal)
    (fun j => CompletedGroup.projection k (D.wall j).label)
    (D.activeLabels_commute k) F
  calc
    _ = _ := (D.map f hf).levelPathProduct_eq_wallPathProduct k _
      ((D.map f hf).activeLabels_commute k)
    _ = _ := by
      -- Identify the composed prefunctor with its two successive path maps.
      convert (hi.trans hr).trans hm'.symm using 1
      simp only [mapPathPrefunctor, Prefunctor.mapPath_comp_apply, q, a]
      rfl
    _ = _ := congrArg F (D.levelPathProduct_eq_wallPathProduct k p
      (D.activeLabels_commute k)).symm

/-- Forget coefficient-killed walls along a common all-order path, retaining its
ambient vertices and segments. -/
def pathMap : D.Point ⥤q (D.map f hf).Point where
  obj x := ⟨x.val, fun k j => by
    have hx := ((D.mapPathPrefunctor f hf k).obj
      (CommonWallComplement.projection k x)).notMem j
    simpa only [mapPathPrefunctor_obj_val, CommonWallComplement.projection_val] using hx⟩
  map a := ⟨fun k => by
    let b := (D.mapPathPrefunctor f hf k).map
      ((CommonWallComplement.projectionPrefunctor k).map a)
    have hb := b.down
    -- The projected endpoints and their finite images have the same ambient values.
    convert hb using 1 <;> apply WallComplement.ext <;>
      simp only [mapPathPrefunctor_obj_val, CommonWallComplement.projection_val,
        CommonWallComplement.projectionPrefunctor_obj]⟩

/-- The all-order coefficient path map preserves ambient points. -/
@[simp]
theorem pathMap_obj_val (x : D.Point) :
    ((D.pathMap f hf).obj x).val = x.val := (rfl)

/-- The all-order coefficient path map preserves reversal. -/
instance : (D.pathMap f hf).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projecting a mapped common path agrees with mapping its finite projection. -/
theorem pathMap_comp_projection (k : ℕ) :
    D.pathMap f hf ⋙q CommonWallComplement.projectionPrefunctor k =
      CommonWallComplement.projectionPrefunctor k ⋙q D.mapPathPrefunctor f hf k := by
  refine Prefunctor.ext (fun x => ?_) (fun _ _ _ => PLift.ext (Subsingleton.elim _ _))
  apply WallComplement.ext
  simp

/-- Mapping coefficients carries the completed product along the same geometric
path through the completed BCH group homomorphism. -/
@[simp]
theorem pathProduct_pathMap {x y : D.Point} (p : Quiver.Path x y) :
    (D.map f hf).pathProduct ((D.pathMap f hf).mapPath p) =
      f.completedMap (D.pathProduct p) := by
  apply CompletedGroup.ext
  intro k
  have hp := congrArg
    (fun F : D.Point ⥤q WallComplement
        (fun j : (D.map f hf).active k => ((D.map f hf).wall j).support) =>
      (D.map f hf).levelPathProduct k (F.mapPath p))
    (D.pathMap_comp_projection f hf k)
  simp only [Prefunctor.mapPath_comp_apply] at hp
  rw [projection_pathProduct, f.projection_completedMap_of_le k (a := k) (by simp),
    projection_pathProduct]
  exact hp.trans (D.levelPathProduct_mapPathPrefunctor f hf k
    ((CommonWallComplement.projectionPrefunctor k).mapPath p))

/-- Coefficient maps preserve consistency even though paths may cross supports
of labels killed by the map. -/
theorem LevelConsistent.map {k : ℕ} (hD : D.LevelConsistent k) :
    (D.map f hf).LevelConsistent k := by
  rw [(D.map f hf).levelConsistent_iff_loops]
  intro x p
  obtain ⟨z, q, hq⟩ := (D.map f hf).exists_loop_levelPathProduct_eq_of_vertices_eq k
    (fun j : D.active k => (D.wall j).support)
    (fun j => (D.wall j).isConvexPolyhedron)
    (fun j => (D.wall j).finrank_direction_add_one) p
  have he := hq ((D.mapPathPrefunctor f hf k).mapPath q) (by
    simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      mapPathPrefunctor_obj_val])
  rw [levelPathProduct_mapPathPrefunctor, (D.levelConsistent_iff_loops k).mp hD z q,
    map_one] at he
  exact he.symm

/-- A consistent directed diagram remains consistent after changing coefficients. -/
theorem Consistent.map (hD : D.Consistent) : (D.map f hf).Consistent := by
  rw [consistent_iff] at hD ⊢
  exact fun k => (hD k).map D f hf

omit D in
/-- Mapping coefficients sends an outgoing completion to an outgoing completion
of the mapped input, even when some initial or outgoing labels vanish. -/
theorem IsOutgoingCompletion.map {ι₀ κ : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H}
    {E : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)}
    (hE : IsOutgoingCompletion D₀ E) :
    IsOutgoingCompletion (fun j => (D₀ j).map f hf) (E.map f hf) where
  wall_inl j := by rw [map_wall, hE.wall_inl]
  outgoing_inr j := by simpa using hE.outgoing_inr j
  consistent := hE.consistent.map E f hf

omit D in
/-- Every outgoing completion of the mapped input represents the coefficient
image of any outgoing completion of the original input. -/
theorem IsOutgoingCompletion.equivalent_map {ι₀ κ κ' : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H}
    {E : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)}
    {E' : DirectedDiagram (d := d) h H' (ι₀ ⊕ κ')}
    (hE : IsOutgoingCompletion D₀ E)
    (hE' : IsOutgoingCompletion (fun j => (D₀ j).map f hf) E') :
    E'.Equivalent (E.map f hf) :=
  outgoingCompletion_unique hE' (hE.map f hf)

end Mei.DirectedDiagram
