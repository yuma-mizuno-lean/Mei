/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Cylinder.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness
public import Mei.Geometry.Convex.Polyhedron.Path.Cylinder
import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport

/-!
# Transport and consistency of cylinder diagrams

Projection of a path through cylinder walls preserves its signed product at every
cutoff and in the completed group. Endpoint transport depends only on the
projected endpoints. Lifting paths at a fixed extra coordinate proves the converse
consistency implication. Thus a diagram is consistent exactly when its cylinder is, and
cylinder lifting carries outgoing completions to outgoing completions.

We use `WallComplement.cylinderProjection`, its fixed-coordinate section
`WallComplement.cylinderLift`, and `Quiver.Path.wallPathProduct_cylinderProjection`.
The geometric comparison is the principal cylinder construction of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2. No injectivity of the projected degree direction
or local finiteness of the full wall family is required.
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

private def cylinderPathIdentification (k : ℕ) :=
  (ContinuousAffineEquiv.refl ℝ (V × E)).wallComplementMap
    (Set.equivOfEq (D.cylinder_active h' k))
    (W := fun a : (D.cylinder h').active k => ((D.cylinder h').wall a).support)
    (W' := fun a : D.active k => (D.wall a).support ×ˢ (univ : Set E))
    (by intro a; simp)

/-- Project finite-order admissible paths from a cylinder diagram to its base. -/
def cylinderPathProjection (k : ℕ) :
    WallComplement (fun a : (D.cylinder h').active k => ((D.cylinder h').wall a).support) ⥤q
      WallComplement (fun a : D.active k => (D.wall a).support) :=
  D.cylinderPathIdentification h' k ⋙q
    WallComplement.cylinderProjection (fun a : D.active k => (D.wall a).support)

@[simp]
theorem cylinderPathProjection_obj_val (k : ℕ)
    (x : WallComplement
      (fun a : (D.cylinder h').active k => ((D.cylinder h').wall a).support)) :
    ((D.cylinderPathProjection h' k).obj x).val = x.val.1 := by
  simp [cylinderPathProjection, cylinderPathIdentification]

instance (k : ℕ) : (D.cylinderPathProjection h' k).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Lift a finite-order base path while keeping the extra coordinate fixed. -/
def cylinderPathLift (k : ℕ) (e : E) :
    WallComplement (fun a : D.active k => (D.wall a).support) ⥤q
      WallComplement (fun a : (D.cylinder h').active k => ((D.cylinder h').wall a).support) :=
  WallComplement.cylinderLift (fun a : D.active k => (D.wall a).support) e ⋙q
    (ContinuousAffineEquiv.refl ℝ (V × E)).wallComplementMap
      (Set.equivOfEq (D.cylinder_active h' k)).symm
      (by intro a; simp)

@[simp]
theorem cylinderPathLift_obj_val (k : ℕ) (e : E)
    (x : WallComplement (fun a : D.active k => (D.wall a).support)) :
    ((D.cylinderPathLift h' k e).obj x).val = (x.val, e) := by
  simp [cylinderPathLift]

instance (k : ℕ) (e : E) : (D.cylinderPathLift h' k e).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Lifting then projecting recovers the base path prefunctor. -/
@[simp]
theorem cylinderPathLift_comp_projection (k : ℕ) (e : E) :
    D.cylinderPathLift h' k e ⋙q D.cylinderPathProjection h' k = Prefunctor.id _ := by
  refine Prefunctor.ext (fun x => WallComplement.ext ?_) ?_
  · simp
  · intros
    exact PLift.ext (Subsingleton.elim _ _)

/-- Projection retains the finite-order signed product, including simultaneous
crossings of coincident indexed walls. -/
@[simp]
theorem levelPathProduct_cylinderPathProjection (k : ℕ)
    {x y : WallComplement
      (fun a : (D.cylinder h').active k => ((D.cylinder h').wall a).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k ((D.cylinderPathProjection h' k).mapPath p) =
      (D.cylinder h').levelPathProduct k p := by
  let r := Set.equivOfEq (D.cylinder_active h' k)
  let ν := fun a : D.active k => h.realCharacter (D.wall a).normal
  let label : D.active k → d.truncatedGroup ℒ k :=
    fun a => CompletedGroup.projection k (D.wall a).label
  have comm : ∀ a b : D.active k,
      affineSpan ℝ ((D.wall a).support ×ˢ (univ : Set E)) =
        affineSpan ℝ ((D.wall b).support ×ˢ (univ : Set E)) →
          Commute (label a) (label b) := fun a b hab =>
    D.activeLabels_commute k a b ((Mei.affineSpan_prod_univ_eq_iff _ _).mp hab)
  have he := Quiver.Path.wallPathProduct_cylinderProjection (G := d.truncatedGroup ℒ k)
    (fun a : D.active k => (D.wall a).support) ν label (D.activeLabels_commute k)
    ((D.cylinderPathIdentification h' k).mapPath p)
  have hi := p.wallPathProduct_wallComplementMap
    (G := d.truncatedGroup ℒ k) (K := d.truncatedGroup ℒ k)
    (ContinuousAffineEquiv.refl ℝ (V × E)) r (by intro a; simp [r])
    (fun a => (h.prod h').realCharacter ((D.cylinder h').wall a).normal)
    (fun a => (ν a).comp (LinearMap.fst ℝ V E))
    (by
      intro a
      rw [cylinder_wall, DirectedWall.realCharacter_cylinder_normal]
      rfl)
    (fun a => CompletedGroup.projection k ((D.cylinder h').wall a).label)
    label ((D.cylinder h').activeLabels_commute k) comm (MonoidHom.id _)
    (by
      intro a
      simp only [label, r, Set.equivOfEq_apply, cylinder_wall, DirectedWall.cylinder_label]
      rfl)
  rw [D.levelPathProduct_eq_wallPathProduct k _ (D.activeLabels_commute k),
    (D.cylinder h').levelPathProduct_eq_wallPathProduct k _
      ((D.cylinder h').activeLabels_commute k)]
  -- The categorical tower projection and the concrete truncated BCH group have
  -- the same carrier; identify their group instances and the composed path map.
  simp only [cylinderPathProjection, Prefunctor.mapPath_comp_apply]
  convert he.trans hi using 1
  rfl

/-- A fixed-coordinate lift has exactly the original finite-order product. -/
@[simp]
theorem levelPathProduct_cylinderPathLift (k : ℕ) (e : E)
    {x y : WallComplement (fun a : D.active k => (D.wall a).support)}
    (p : AdmissiblePLPath x y) :
    (D.cylinder h').levelPathProduct k ((D.cylinderPathLift h' k e).mapPath p) =
      D.levelPathProduct k p := by
  rw [← levelPathProduct_cylinderPathProjection]
  have he := congrArg
    (fun F : WallComplement (fun a : D.active k => (D.wall a).support) ⥤q
        WallComplement (fun a : D.active k => (D.wall a).support) =>
      D.levelPathProduct k (F.mapPath p)) (D.cylinderPathLift_comp_projection h' k e)
  simp only [Prefunctor.mapPath_comp_apply, Prefunctor.mapPath_id] at he
  -- The endpoints of the composite prefunctor are its successive object maps.
  convert he using 1 <;> rfl

/-- Consistency of the base implies consistency of the cylinder at each cutoff. -/
theorem LevelConsistent.cylinder {k : ℕ} (hD : D.LevelConsistent k) :
    (D.cylinder h').LevelConsistent k := by
  rw [levelConsistent_def]
  intro x y p q
  rw [← levelPathProduct_cylinderPathProjection, ← levelPathProduct_cylinderPathProjection]
  exact (D.levelConsistent_def k).mp hD _ _

/-- A cylinder is consistent at a cutoff exactly when its base is. -/
@[simp]
theorem cylinder_levelConsistent_iff (k : ℕ) :
    (D.cylinder h').LevelConsistent k ↔ D.LevelConsistent k := by
  constructor
  · intro hc
    rw [levelConsistent_def] at hc ⊢
    intro x y p q
    have he := hc ((D.cylinderPathLift h' k (0 : E)).mapPath p)
      ((D.cylinderPathLift h' k (0 : E)).mapPath q)
    simpa only [levelPathProduct_cylinderPathLift] using he
  · exact fun hc => hc.cylinder D h'

/-- Cylinder lifting preserves and reflects all-order consistency. -/
@[simp]
theorem cylinder_consistent_iff : (D.cylinder h').Consistent ↔ D.Consistent := by
  simp only [consistent_iff, cylinder_levelConsistent_iff]

/-- Finite-order endpoint transport in a consistent cylinder depends only on
the projected endpoints, regardless of their extra coordinates. -/
@[simp]
theorem levelTransport_cylinder {k : ℕ} (hD : D.LevelConsistent k)
    (x y : WallComplement
      (fun a : (D.cylinder h').active k => ((D.cylinder h').wall a).support)) :
    (D.cylinder h').levelTransport k (hD.cylinder D h') x y =
      D.levelTransport k hD ((D.cylinderPathProjection h' k).obj x)
        ((D.cylinderPathProjection h' k).obj y) := by
  obtain ⟨p⟩ := (D.cylinder h').exists_level_path k x y
  rw [levelTransport_eq_levelPathProduct _ (hD.cylinder D h') p,
    D.levelTransport_eq_levelPathProduct hD, levelPathProduct_cylinderPathProjection]

/-- Project a path admissible at every cutoff of a cylinder diagram. -/
def pathCylinderProjection : (D.cylinder h').Point ⥤q D.Point where
  obj x := ⟨x.val.1, fun k a ha => by
    have hx := ((D.cylinderPathProjection h' k).obj
      (CommonWallComplement.projection k x)).notMem a
    exact hx (by simpa using ha)⟩
  map a := ⟨fun k => by
    have hb := ((D.cylinderPathProjection h' k).map
      ((CommonWallComplement.projectionPrefunctor k).map a)).down
    -- Finite projection and the common projection have the same endpoint values.
    convert hb using 1 <;> apply WallComplement.ext <;> simp⟩

@[simp]
theorem pathCylinderProjection_obj_val (x : (D.cylinder h').Point) :
    ((D.pathCylinderProjection h').obj x).val = x.val.1 := (rfl)

/-- The cylinder path projection preserves reversed segments and paths. -/
instance : (D.pathCylinderProjection h').MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projecting a common cylinder path and then choosing a cutoff agrees with
projecting first at that cutoff. -/
theorem pathCylinderProjection_comp_projection (k : ℕ) :
    D.pathCylinderProjection h' ⋙q CommonWallComplement.projectionPrefunctor k =
      CommonWallComplement.projectionPrefunctor k ⋙q D.cylinderPathProjection h' k := by
  refine Prefunctor.ext (fun x => WallComplement.ext ?_) ?_
  · simp
  · intros
    exact PLift.ext (Subsingleton.elim _ _)

/-- Cylinder projection preserves the completed path product. -/
@[simp]
theorem pathProduct_pathCylinderProjection {x y : (D.cylinder h').Point}
    (p : Quiver.Path x y) :
    D.pathProduct ((D.pathCylinderProjection h').mapPath p) =
      (D.cylinder h').pathProduct p := by
  apply CompletedGroup.ext
  intro k
  have he := congrArg
    (fun F : (D.cylinder h').Point ⥤q
        WallComplement (fun a : D.active k => (D.wall a).support) =>
      D.levelPathProduct k (F.mapPath p)) (D.pathCylinderProjection_comp_projection h' k)
  simp only [Prefunctor.mapPath_comp_apply] at he
  rw [projection_pathProduct, projection_pathProduct]
  exact he.trans (D.levelPathProduct_cylinderPathProjection h' k
    ((CommonWallComplement.projectionPrefunctor k).mapPath p))

/-- Completed endpoint transport in a consistent cylinder depends only on the
spatial projections of its endpoints. -/
@[simp]
theorem transport_cylinder (hD : D.Consistent) (x y : (D.cylinder h').Point) :
    (D.cylinder h').transport ((D.cylinder_consistent_iff h').mpr hD) x y =
      D.transport hD ((D.pathCylinderProjection h').obj x)
        ((D.pathCylinderProjection h').obj y) := by
  obtain ⟨p⟩ := (D.cylinder h').exists_path x y
  rw [transport_eq_pathProduct _ ((D.cylinder_consistent_iff h').mpr hD) p,
    D.transport_eq_pathProduct hD, pathProduct_pathCylinderProjection]

omit D in
/-- The cylinder over an outgoing completion is an outgoing completion of the
cylinder input, retaining every indexed initial wall. -/
theorem IsOutgoingCompletion.cylinder {ι₀ κ : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h (H.project (AddMonoidHom.fst Λ K))}
    {C : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) (ι₀ ⊕ κ)}
    (hC : IsOutgoingCompletion D₀ C) :
    IsOutgoingCompletion (fun a => (D₀ a).cylinder h') (C.cylinder h') where
  wall_inl a := by rw [cylinder_wall, hC.wall_inl]
  outgoing_inr a := by simpa using hC.outgoing_inr a
  consistent := (C.cylinder_consistent_iff h').mpr hC.consistent

end Mei.DirectedDiagram
