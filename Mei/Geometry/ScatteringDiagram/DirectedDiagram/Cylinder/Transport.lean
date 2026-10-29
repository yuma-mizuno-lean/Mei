/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Cylinder.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.Convex.Polyhedron.Path.Cylinder
import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport

/-!
# Transport through cylinder diagrams

Projection of an admissible path through cylinder walls preserves every signed
crossing, including simultaneous crossings of repeated walls. Consequently its
finite-order path product is that of its spatial projection. Cylinder lifting
preserves consistency and finite and completed endpoint transport.

This connects `DirectedDiagram.cylinder` with
`Quiver.Path.wallPathProduct_cylinderProjection`. Principal cylinders and their
path products occur in Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, §1 and Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ K R L V E ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup K]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ Λ × K} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {j : K →+ E} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) ι)
  (h' : TauCeti.Toric.IsIntegralLattice j)

/-- Project a finite-order cylinder path, forgetting the unrestricted coordinates.
The active indices are unchanged because cylinder lifting retains labels. -/
def levelCylinderProjection (k : ℕ) :
    WallComplement (fun a : (D.cylinder h').active k =>
      ((D.cylinder h').wall a).support) ⥤q
      WallComplement (fun a : D.active k => (D.wall a).support) :=
  (ContinuousAffineEquiv.refl ℝ (V × E)).wallComplementMap
      (Set.equivOfEq (D.cylinder_active h' k)) (by
        intro a
        simp) ⋙q
    WallComplement.cylinderProjection (fun a : D.active k => (D.wall a).support)

/-- Projection acts on the actual spatial values of vertices. -/
@[simp]
theorem levelCylinderProjection_obj_val (k : ℕ)
    (x : WallComplement (fun a : (D.cylinder h').active k =>
      ((D.cylinder h').wall a).support)) :
    ((D.levelCylinderProjection h' k).obj x).val = x.val.1 := by
  simp [levelCylinderProjection]

/-- Cylinder projection commutes with reversal. -/
instance (k : ℕ) : (D.levelCylinderProjection h' k).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Cylinder paths have exactly the path products of their spatial projections,
with the original cutoff and every coincident indexed label retained. -/
@[simp]
theorem levelPathProduct_cylinder (k : ℕ)
    {x y : WallComplement (fun a : (D.cylinder h').active k =>
      ((D.cylinder h').wall a).support)} (p : AdmissiblePLPath x y) :
    (D.cylinder h').levelPathProduct k p =
      D.levelPathProduct k ((D.levelCylinderProjection h' k).mapPath p) := by
  let W := fun a : D.active k => (D.wall a).support
  let ν := fun a : D.active k => h.realCharacter (D.wall a).normal
  let label := fun a : D.active k => CompletedGroup.projection k (D.wall a).label
  let comm : ∀ a b : D.active k,
      affineSpan ℝ (W a ×ˢ (univ : Set E)) = affineSpan ℝ (W b ×ˢ univ) →
      Commute (label a) (label b) := fun a b hab => D.activeLabels_commute k a b
    ((Mei.affineSpan_prod_univ_eq_iff (W a) (W b)).mp hab)
  let e := ContinuousAffineEquiv.refl ℝ (V × E)
  let r := Set.equivOfEq (D.cylinder_active h' k)
  have hW : ∀ a, W (r a) ×ˢ (univ : Set E) =
      e '' ((D.cylinder h').wall a).support := by
    intro a
    simp [W, e, r]
  let q := (e.wallComplementMap
    (W' := fun a : D.active k => W a ×ˢ (univ : Set E)) r hW).mapPath p
  have hi := p.wallPathProduct_wallComplementMap
    (W' := fun a : D.active k => W a ×ˢ (univ : Set E)) e r hW
    (fun a => (h.prod h').realCharacter ((D.cylinder h').wall a).normal)
    (fun a => (ν a).comp (LinearMap.fst ℝ V E))
    (by
      intro a
      rw [cylinder_wall, DirectedWall.realCharacter_cylinder_normal]
      simp [ν, e, r])
    (fun a => CompletedGroup.projection k ((D.cylinder h').wall a).label)
    label ((D.cylinder h').activeLabels_commute k) comm
    (MonoidHom.id _) (by intro a; simp [label, r])
  have hp := q.wallPathProduct_cylinderProjection W ν label (D.activeLabels_commute k)
  rw [(D.cylinder h').levelPathProduct_eq_wallPathProduct k p
    ((D.cylinder h').activeLabels_commute k),
    D.levelPathProduct_eq_wallPathProduct k _ (D.activeLabels_commute k)]
  -- The categorical tower carries the same BCH operations. The support equalities
  -- in the two presentations of the reindexing map differ only in their proofs.
  convert hi.symm.trans hp.symm using 1
  · simp only [levelCylinderProjection, Prefunctor.mapPath_comp_apply,
      q, e, r, W, ν, label]
    rfl

variable {D}

/-- Finite-order consistency is preserved by adjoining unrestricted coordinates. -/
theorem LevelConsistent.cylinder {k : ℕ} (hD : D.LevelConsistent k)
    (h' : TauCeti.Toric.IsIntegralLattice j) :
    (D.cylinder h').LevelConsistent k := by
  apply ((D.cylinder h').levelConsistent_def k).mpr
  intro x y p q
  rw [levelPathProduct_cylinder, levelPathProduct_cylinder]
  exact (D.levelConsistent_def k).mp hD _ _

/-- Cylinder lifting preserves consistency at every finite order. -/
theorem Consistent.cylinder (hD : D.Consistent)
    (h' : TauCeti.Toric.IsIntegralLattice j) : (D.cylinder h').Consistent := by
  apply ((D.cylinder h').consistent_iff).mpr
  intro k
  exact ((D.consistent_iff.mp hD) k).cylinder h'

variable (D)

/-- Finite endpoint transport in the cylinder depends only on projected endpoints. -/
theorem levelTransport_cylinder {k : ℕ} (hD : D.LevelConsistent k)
    (x y : WallComplement (fun a : (D.cylinder h').active k =>
      ((D.cylinder h').wall a).support)) :
    (D.cylinder h').levelTransport k (hD.cylinder h') x y =
      D.levelTransport k hD ((D.levelCylinderProjection h' k).obj x)
        ((D.levelCylinderProjection h' k).obj y) := by
  obtain ⟨p⟩ := (D.cylinder h').exists_level_path k x y
  rw [(D.cylinder h').levelTransport_eq_levelPathProduct _ p,
    levelPathProduct_cylinder, D.levelTransport_eq_levelPathProduct hD]

/-- Forget the unrestricted coordinates of a common all-order cylinder path. -/
def pathCylinderProjection : (D.cylinder h').Point ⥤q D.Point where
  obj x := ⟨x.val.1, fun k a ha => by
    have hx := ((D.levelCylinderProjection h' k).obj
      (CommonWallComplement.projection k x)).notMem a
    exact hx (by simpa only [levelCylinderProjection_obj_val,
      CommonWallComplement.projection_val] using ha)⟩
  map {x y} a := ⟨fun k => by
    have hb := ((D.levelCylinderProjection h' k).map
      ((CommonWallComplement.projectionPrefunctor k).map a)).down
    -- Finite projection and all-order projection have the same spatial vertices.
    convert hb using 1 <;> apply WallComplement.ext <;>
      simp only [levelCylinderProjection_obj_val, CommonWallComplement.projection_val,
        CommonWallComplement.projectionPrefunctor_obj]⟩

/-- All-order cylinder projection takes the first spatial coordinate. -/
@[simp]
theorem pathCylinderProjection_obj_val (x : (D.cylinder h').Point) :
    ((D.pathCylinderProjection h').obj x).val = x.val.1 := (rfl)

/-- All-order cylinder projection preserves reversal. -/
instance : (D.pathCylinderProjection h').MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Forgetting unrestricted coordinates commutes with every finite cutoff. -/
theorem pathCylinderProjection_comp_projection (k : ℕ) :
    D.pathCylinderProjection h' ⋙q CommonWallComplement.projectionPrefunctor k =
      CommonWallComplement.projectionPrefunctor k ⋙q D.levelCylinderProjection h' k := by
  refine Prefunctor.ext (fun x => ?_) (fun _ _ _ => PLift.ext (Subsingleton.elim _ _))
  apply WallComplement.ext
  simp

/-- The completed product through cylinder walls is the product along projection.
No consistency hypothesis or locally finite all-order support is needed. -/
@[simp]
theorem pathProduct_cylinder {x y : (D.cylinder h').Point} (p : Quiver.Path x y) :
    (D.cylinder h').pathProduct p =
      D.pathProduct ((D.pathCylinderProjection h').mapPath p) := by
  apply CompletedGroup.ext
  intro k
  have hp := congrArg
    (fun F : (D.cylinder h').Point ⥤q
      WallComplement (fun a : D.active k => (D.wall a).support) =>
      D.levelPathProduct k (F.mapPath p))
    (D.pathCylinderProjection_comp_projection h' k)
  simp only [Prefunctor.mapPath_comp_apply] at hp
  rw [projection_pathProduct, projection_pathProduct, levelPathProduct_cylinder]
  exact hp.symm

/-- Completed endpoint transport is unchanged by spatial projection of cylinders. -/
theorem transport_cylinder (hD : D.Consistent) (x y : (D.cylinder h').Point) :
    (D.cylinder h').transport (hD.cylinder h') x y =
      D.transport hD ((D.pathCylinderProjection h').obj x)
        ((D.pathCylinderProjection h').obj y) := by
  obtain ⟨p⟩ := (D.cylinder h').exists_path x y
  rw [(D.cylinder h').transport_eq_pathProduct _ p,
    pathProduct_cylinder, D.transport_eq_pathProduct hD]

end Mei.DirectedDiagram
