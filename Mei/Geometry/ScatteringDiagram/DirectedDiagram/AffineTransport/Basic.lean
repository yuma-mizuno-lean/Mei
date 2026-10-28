/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Completion
public import Mei.Geometry.ScatteringDiagram.DirectedWall.AffineTransport
public import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport
import Mei.Geometry.Convex.Polyhedron.Path.Restriction

/-!
# Affine transport of directed diagrams

Compatible spatial and algebraic coordinate changes transport a directed diagram,
preserving finite activity, incomingness and outgoingness. The degree functions
may differ: at target order `k`, paths are transported from any source cutoff
covering the coordinate change's modulus. The finite path product is carried by
the corresponding truncated BCH homomorphism, even when some source walls vanish.
Common all-order paths then give naturality of the completed path product.

This combines `DirectedWall.image`, `GradedLieHom.hasFiniteSupport_completedMap`,
and the affine covariance and identity-wall deletion theorems for
`Quiver.Path.wallPathProduct`. Repeated and coincident walls retain their indices;
translations and orientation-reversing affine equivalences are allowed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Γ'' Λ Λ' Λ'' R V V' V'' ι : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'} {d'' : PositiveDegrees Γ''}
  [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
  {i : Λ →+ V} {i' : Λ' →+ V'} {i'' : Λ'' →+ V''}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {H'' : DirectedWallSpaces ρ'' ℋ}
  (D : DirectedDiagram (d := d) h H ι)
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- Transport every indexed wall through compatible spatial and algebraic
coordinate changes. Finite activity is preserved through the cutoff modulus. -/
def image : DirectedDiagram (d := d') h' H' ι where
  wall j := (D.wall j).image e E hE
  finite_active := by
    simpa only [DirectedWall.image_label, E.completedEquiv_apply] using
      E.gradedLieHom.hasFiniteSupport_completedMap D.finite_active

/-- Diagram transport applies the existing affine transport to every wall. -/
@[simp]
theorem image_wall (j : ι) : (D.image e E hE).wall j = (D.wall j).image e E hE := (rfl)

/-- Integral affine transport preserves full-hyperplane inputs, with translated offsets. -/
theorem image_fullHyperplane
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    (e : Toric.IntegralAffineEquiv h h')
    (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
    (hE : E.tangentEquiv = e.latticeEquiv) : ∀ j, ∃ a : ℝ,
    ((D.image e E hE).wall j).support =
      {x | h'.realCharacter ((D.image e E hE).wall j).normal x = a} := by
  intro j
  obtain ⟨a, ha⟩ := hfull j
  rw [image_wall]
  exact ⟨_, (D.wall j).image_support_eq_hyperplane e E hE ha⟩

/-- Identity coordinates fix a directed diagram. -/
@[simp]
theorem image_refl :
    D.image (Toric.IntegralAffineEquiv.refl h)
      (DirectedWallSpaces.CoordinateChange.refl H) (by simp) = D := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Successive spatial and algebraic coordinate changes compose on diagrams. -/
theorem image_image
    (f : Toric.IntegralAffineEquiv h' h'')
    (F : DirectedWallSpaces.CoordinateChange (d := d') (e := d'') H' H'')
    (hF : F.tangentEquiv = f.latticeEquiv) :
    (D.image e E hE).image f F hF =
      D.image (e.trans f) (E.trans F) (by simp [hE, hF]) := by
  apply DirectedDiagram.ext
  funext j
  simp only [image_wall, DirectedWall.image_image]

/-- Transport by the inverse coordinates recovers the original diagram. -/
@[simp]
theorem image_symm_image :
    (D.image e E hE).image e.symm E.symm (by simp [hE]) = D := by
  rw [image_image]
  simp

/-- Affine coordinate changes identify the existing directed-diagram carriers. -/
def imageEquiv : DirectedDiagram (d := d) h H ι ≃ DirectedDiagram (d := d') h' H' ι where
  toFun D := D.image e E hE
  invFun D := D.image e.symm E.symm (by simp [hE])
  left_inv D := D.image_symm_image e E hE
  right_inv D := by simpa using D.image_symm_image e.symm E.symm (by simp [hE])

@[simp]
theorem imageEquiv_apply : imageEquiv e E hE D = D.image e E hE := (rfl)

@[simp]
theorem imageEquiv_symm_apply (D' : DirectedDiagram (d := d') h' H' ι) :
    (imageEquiv (ι := ι) e E hE).symm D' = D'.image e.symm E.symm (by simp [hE]) := (rfl)

/-- A target-active label was active at any source order covering the modulus. -/
theorem active_image_subset (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a) :
    (D.image e E hE).active k ⊆ D.active a := by
  intro j hj
  simp only [mem_active, image_wall, DirectedWall.image_label, E.completedEquiv_apply,
    E.gradedLieHom.projection_completedMap_of_le k ha] at hj
  rw [mem_active]
  intro he
  apply hj
  rw [he]
  -- The tower object carries the concrete BCH group operations.
  convert (E.gradedLieHom.truncatedMap k ha).bchGroupMap.map_one using 1
  rfl

/-- Restrict a source path to the target-active indices and then apply the spatial
affine map. The source cutoff can be any bound for the prescribed modulus. -/
def levelPathImage (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a) :
    WallComplement (fun j : D.active a => (D.wall j).support) ⥤q
      WallComplement (fun j : (D.image e E hE).active k =>
        ((D.image e E hE).wall j).support) :=
  WallComplement.restrictPrefunctor (fun j : D.active a => (D.wall j).support)
      (Set.inclusion (D.active_image_subset e E hE k ha)) ⋙q
    e.toContinuousAffineEquiv.wallComplementMap (Equiv.refl _) (by
      intro j
      simp only [Equiv.refl_apply, image_wall, DirectedWall.image_support,
        Function.comp_apply]
      ext v
      simp)

/-- The finite path map sends each vertex to its actual affine image. -/
@[simp]
theorem levelPathImage_obj_val (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (x : WallComplement (fun j : D.active a => (D.wall j).support)) :
    ((D.levelPathImage e E hE k ha).obj x).val = e x.val := by
  simp [levelPathImage]

/-- Finite path transport preserves reversal of segments and polygonal paths. -/
instance (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a) :
    (D.levelPathImage e E hE k ha).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Finite directed transport is natural under affine coordinate changes, using
the truncated BCH map at any source cutoff covering the target modulus. -/
@[simp]
theorem levelPathProduct_image (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    {x y : WallComplement (fun j : D.active a => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.image e E hE).levelPathProduct k ((D.levelPathImage e E hE k ha).mapPath p) =
      (E.gradedLieHom.truncatedMap k ha).bchGroupMap (D.levelPathProduct a p) := by
  let f := Set.inclusion (D.active_image_subset e E hE k ha)
  let q := (WallComplement.restrictPrefunctor
    (fun j : D.active a => (D.wall j).support) f).mapPath p
  let F := (E.gradedLieHom.truncatedMap k ha).bchGroupMap
  have hlabel (j : ι) : CompletedGroup.projection k ((D.image e E hE).wall j).label =
      F (CompletedGroup.projection a (D.wall j).label) := by
    simp only [image_wall, DirectedWall.image_label, E.completedEquiv_apply]
    exact E.gradedLieHom.projection_completedMap_of_le k ha _
  -- First delete exactly the labels killed at the target cutoff.
  have hzero (j : D.active a) (hj : j ∉ range f) :
      F (CompletedGroup.projection a (D.wall j).label) = 1 := by
    rw [← hlabel]
    by_contra hne
    exact hj ⟨⟨j.val, ((D.image e E hE).mem_active k j.val).mpr hne⟩, Subtype.ext rfl⟩
  have hr := p.wallPathProduct_restrict
    (fun j : D.active a => h.realCharacter (D.wall j).normal)
    (fun j => F (CompletedGroup.projection a (D.wall j).label))
    (fun j l h => (D.activeLabels_commute a j l h).map F) f (Set.inclusion_injective _) hzero
  -- Affine covariance now applies to the surviving indexed family.
  have hi := q.wallPathProduct_wallComplementMap e.toContinuousAffineEquiv (Equiv.refl _)
    (W' := fun j : (D.image e E hE).active k => ((D.image e E hE).wall j).support)
    (by
      intro j
      simp only [Equiv.refl_apply, image_wall, DirectedWall.image_support]
      ext v
      simp [f])
    (fun j => h.realCharacter (D.wall (f j)).normal)
    (fun j => h'.realCharacter ((D.image e E hE).wall j).normal)
    (by
      intro j
      ext v
      simpa only [Equiv.refl_apply, image_wall, LinearMap.comp_apply,
        Toric.IntegralAffineEquiv.toContinuousAffineEquiv_toAffineEquiv,
        f, Set.coe_inclusion, LinearEquiv.coe_coe] using
        (D.wall j).realCharacter_image_normal e E hE v)
    (fun j => CompletedGroup.projection a (D.wall (f j)).label)
    (fun j => CompletedGroup.projection k ((D.image e E hE).wall j).label)
    (fun j l h => D.activeLabels_commute a (f j) (f l) h)
    ((D.image e E hE).activeLabels_commute k) F (fun j => hlabel j)
  -- Move coefficient change through both products and recombine the comparisons.
  have hm := q.map_wallPathProduct
    (fun j => h.realCharacter (D.wall (f j)).normal)
    (fun j => CompletedGroup.projection a (D.wall (f j)).label)
    (fun j l h => D.activeLabels_commute a (f j) (f l) h) F
  have he := hi.trans (hm.trans hr)
  have hm' := p.map_wallPathProduct
    (fun j : D.active a => h.realCharacter (D.wall j).normal)
    (fun j => CompletedGroup.projection a (D.wall j).label)
    (D.activeLabels_commute a) F
  calc
    _ = _ := (D.image e E hE).levelPathProduct_eq_wallPathProduct k _
      ((D.image e E hE).activeLabels_commute k)
    _ = _ := by
      -- The prefunctor composition and its two successive path maps coincide.
      convert he.trans hm'.symm using 1
      simp only [levelPathImage, Prefunctor.mapPath_comp_apply, q, f]
      rfl
    _ = _ := congrArg F (D.levelPathProduct_eq_wallPathProduct a p
      (D.activeLabels_commute a)).symm

/-- Transport a common all-order path. Each target admissibility condition uses
the source condition at its prescribed cutoff modulus. -/
def pathImage : D.Point ⥤q (D.image e E hE).Point where
  obj x := ⟨e x.val, fun k j => by
    have hx := ((D.levelPathImage e E hE k le_rfl).obj
      (CommonWallComplement.projection (E.degreeMap.modulus k) x)).notMem j
    simpa only [levelPathImage_obj_val, CommonWallComplement.projection_val] using hx⟩
  map {x y} a := ⟨fun k => by
    let b := (D.levelPathImage e E hE k le_rfl).map
      ((CommonWallComplement.projectionPrefunctor (E.degreeMap.modulus k)).map a)
    have hb := b.down
    -- The projected endpoints and the finite affine images have the same ambient values.
    convert hb using 1 <;> apply WallComplement.ext <;>
      simp only [levelPathImage_obj_val, CommonWallComplement.projection_val,
        CommonWallComplement.projectionPrefunctor_obj]⟩

/-- All-order allowed points move by the spatial affine equivalence. -/
@[simp]
theorem pathImage_obj_val (x : D.Point) :
    ((D.pathImage e E hE).obj x).val = e x.val := (rfl)

/-- All-order affine path transport preserves reversal. -/
instance : (D.pathImage e E hE).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projecting a transported common path agrees with transporting its projection
from the source cutoff selected by the modulus. -/
theorem pathImage_comp_projection (k : ℕ) :
    D.pathImage e E hE ⋙q CommonWallComplement.projectionPrefunctor k =
      CommonWallComplement.projectionPrefunctor (E.degreeMap.modulus k) ⋙q
        D.levelPathImage e E hE k le_rfl := by
  refine Prefunctor.ext (fun x => ?_) (fun _ _ _ => PLift.ext (Subsingleton.elim _ _))
  apply WallComplement.ext
  simp

/-- Affine coordinate changes carry completed directed path products through the
completed BCH group isomorphism, even when the degree functions differ. -/
@[simp]
theorem pathProduct_image {x y : D.Point} (p : Quiver.Path x y) :
    (D.image e E hE).pathProduct ((D.pathImage e E hE).mapPath p) =
      E.completedEquiv (D.pathProduct p) := by
  apply CompletedGroup.ext
  intro k
  have hp := congrArg
    (fun F : D.Point ⥤q WallComplement
        (fun j : (D.image e E hE).active k => ((D.image e E hE).wall j).support) =>
      (D.image e E hE).levelPathProduct k (F.mapPath p))
    (D.pathImage_comp_projection e E hE k)
  simp only [Prefunctor.mapPath_comp_apply] at hp
  rw [projection_pathProduct, E.completedEquiv_apply,
    E.gradedLieHom.projection_completedMap, projection_pathProduct]
  exact hp.trans (D.levelPathProduct_image e E hE k le_rfl
    ((CommonWallComplement.projectionPrefunctor (E.degreeMap.modulus k)).mapPath p))

end Mei.DirectedDiagram
