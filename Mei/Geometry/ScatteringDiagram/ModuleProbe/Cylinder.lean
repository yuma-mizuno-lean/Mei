/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Initial
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Projection
public import Mei.Geometry.Convex.Polyhedron.Path.Cylinder
import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport

/-!
# Transport through the charge-zero cylinders of a module probe

Including base labels in a module probe and adjoining the two unrestricted spatial
coordinates preserves every finite-order signed path product. The base inclusion
is split at the same cutoff, so the active indices are unchanged and consistency
is both preserved and reflected. In particular, a cylinder over an outgoing base
completion is an outgoing completion of the cylinder input.

The geometric calculation uses `WallComplement.cylinderProjection` and
`Quiver.Path.wallPathProduct_wallComplementMap`; the coefficient calculation uses
`ModuleProbe.baseQuotientProjection_base`. Labels are included in the larger
semidirect probe group. The module
probe follows Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section

open Set Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := d) h H ι)

/-- Including charge-zero labels preserves precisely the active base walls. -/
@[simp]
theorem cylinderDiagram_active (k : ℕ) :
    (cylinderDiagram d ℳ p ℒ H h h' D).active k = D.active k := by
  have hinj := LieHom.bchGroupMap_injective
    (Function.LeftInverse.injective (baseQuotientProjection_base d ℳ p ℒ k))
  ext a
  simp only [DirectedDiagram.mem_active, cylinderDiagram_wall, baseCylinder_label,
    GradedLieHom.projection_completedMap_of_le (baseGradedLieHom d ℳ p ℒ)
      k (a := k) (by simp), ne_eq]
  exact not_congr (map_eq_one_iff _ hinj)

/-- Project a path through charge-zero probe cylinders to the original base walls. -/
def cylinderPathProjection (k : ℕ) :
    WallComplement (fun a : (cylinderDiagram d ℳ p ℒ H h h' D).active k =>
      ((cylinderDiagram d ℳ p ℒ H h h' D).wall a).support) ⥤q
      WallComplement (fun a : D.active k => (D.wall a).support) :=
  (ContinuousAffineEquiv.refl ℝ (V × E)).wallComplementMap
      (Set.equivOfEq (cylinderDiagram_active d ℳ p ℒ H h h' D k))
      (by intro a; simp) ⋙q
    WallComplement.cylinderProjection (fun a : D.active k => (D.wall a).support)

/-- Path projection forgets exactly the two auxiliary spatial coordinates. -/
@[simp]
theorem cylinderPathProjection_obj_val (k : ℕ)
    (x : WallComplement (fun a : (cylinderDiagram d ℳ p ℒ H h h' D).active k =>
      ((cylinderDiagram d ℳ p ℒ H h h' D).wall a).support)) :
    ((cylinderPathProjection d ℳ p ℒ H h h' D k).obj x).val = x.val.1 := by
  simp [cylinderPathProjection]

instance (k : ℕ) : (cylinderPathProjection d ℳ p ℒ H h h' D k).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- The probe product is the charge-zero inclusion of the base product, at the same
cutoff. This retains every indexed factor of a simultaneous crossing. -/
@[simp]
theorem levelPathProduct_cylinderDiagram (k : ℕ)
    {x y : WallComplement (fun a : (cylinderDiagram d ℳ p ℒ H h h' D).active k =>
      ((cylinderDiagram d ℳ p ℒ H h h' D).wall a).support)}
    (q : AdmissiblePLPath x y) :
    (cylinderDiagram d ℳ p ℒ H h h' D).levelPathProduct k q =
      ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)).bchGroupMap
        (D.levelPathProduct k ((cylinderPathProjection d ℳ p ℒ H h h' D k).mapPath q)) := by
  let C := cylinderDiagram d ℳ p ℒ H h h' D
  let f := ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)).bchGroupMap
  let W := fun a : D.active k => (D.wall a).support
  let ν := fun a : D.active k => h.realCharacter (D.wall a).normal
  let label := fun a : D.active k => f (CompletedGroup.projection k (D.wall a).label)
  let comm : ∀ a b : D.active k,
      affineSpan ℝ (W a ×ˢ (univ : Set E)) = affineSpan ℝ (W b ×ˢ univ) →
      Commute (label a) (label b) := fun a b hab =>
    (D.activeLabels_commute k a b
      ((Mei.affineSpan_prod_univ_eq_iff (W a) (W b)).mp hab)).map f
  let e := ContinuousAffineEquiv.refl ℝ (V × E)
  let r := Set.equivOfEq (cylinderDiagram_active d ℳ p ℒ H h h' D k)
  have hW : ∀ a, W (r a) ×ˢ (univ : Set E) = e '' (C.wall a).support := by
    intro a
    simp [C, W, e, r]
  let q' := (e.wallComplementMap
    (W' := fun a : D.active k => W a ×ˢ (univ : Set E)) r hW).mapPath q
  have hi := q.wallPathProduct_wallComplementMap
    (W' := fun a : D.active k => W a ×ˢ (univ : Set E)) e r hW
    (fun a => (h.prod h').realCharacter (C.wall a).normal)
    (fun a => (ν a).comp (LinearMap.fst ℝ V E))
    (by
      intro a
      simpa [C, baseNormal_def, ν, r, e] using
        ((h.prod h').realCharacter_comp h (AddMonoidHom.fst Λ (ℤ × ℤ))
          (LinearMap.fst ℝ V E) (fun _ => rfl) (D.wall a).normal).symm)
    (fun a => CompletedGroup.projection k (C.wall a).label) label
    (C.activeLabels_commute k) comm (MonoidHom.id _)
    (by intro a; simp [C, label, r, f,
      GradedLieHom.projection_completedMap_of_le (baseGradedLieHom d ℳ p ℒ)
        k (a := k) (by simp)]; rfl)
  have hp := q'.wallPathProduct_cylinderProjection W ν label
    (fun a b hab => (D.activeLabels_commute k a b hab).map f)
  have hm := ((cylinderPathProjection d ℳ p ℒ H h h' D k).mapPath q).map_wallPathProduct
    ν (fun a => CompletedGroup.projection k (D.wall a).label) (D.activeLabels_commute k) f
  have hq : (WallComplement.cylinderProjection W).mapPath q' =
      (cylinderPathProjection d ℳ p ℒ H h h' D k).mapPath q := by
    simp only [cylinderPathProjection, Prefunctor.mapPath_comp_apply, q', e, r, W]
  rw [hq] at hp
  -- The concrete BCH group and the categorical tower object have the same
  -- operations; `convert` identifies their presentations of the three products.
  convert hi.symm.trans (hp.symm.trans hm.symm) using 1
  · exact C.levelPathProduct_eq_wallPathProduct k q (C.activeLabels_commute k)
  · exact congrArg f (D.levelPathProduct_eq_wallPathProduct k _
      (D.activeLabels_commute k))

/-- Lift a base path at a fixed auxiliary position, including its labels in charge zero. -/
def cylinderPathLift (k : ℕ) (v : E) :
    WallComplement (fun a : D.active k => (D.wall a).support) ⥤q
      WallComplement (fun a : (cylinderDiagram d ℳ p ℒ H h h' D).active k =>
        ((cylinderDiagram d ℳ p ℒ H h h' D).wall a).support) :=
  WallComplement.cylinderLift (fun a : D.active k => (D.wall a).support) v ⋙q
    (ContinuousAffineEquiv.refl ℝ (V × E)).wallComplementMap
      (Set.equivOfEq (cylinderDiagram_active d ℳ p ℒ H h h' D k)).symm
      (by intro a; simp)

/-- The lifted vertices have the prescribed constant auxiliary position. -/
@[simp]
theorem cylinderPathLift_obj_val (k : ℕ) (v : E)
    (x : WallComplement (fun a : D.active k => (D.wall a).support)) :
    ((cylinderPathLift d ℳ p ℒ H h h' D k v).obj x).val = (x.val, v) := by
  simp [cylinderPathLift]

instance (k : ℕ) (v : E) : (cylinderPathLift d ℳ p ℒ H h h' D k v).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projection retracts the fixed-coordinate path lift. -/
@[simp]
theorem cylinderPathLift_comp_projection (k : ℕ) (v : E) :
    cylinderPathLift d ℳ p ℒ H h h' D k v ⋙q
      cylinderPathProjection d ℳ p ℒ H h h' D k = Prefunctor.id _ := by
  refine Prefunctor.ext (fun x => WallComplement.ext ?_) ?_
  · simp
  · intros
    exact PLift.ext (Subsingleton.elim _ _)

/-- Products of lifted paths are the finite charge-zero images of the original products. -/
theorem levelPathProduct_cylinderPathLift (k : ℕ) (v : E)
    {x y : WallComplement (fun a : D.active k => (D.wall a).support)}
    (q : AdmissiblePLPath x y) :
    (cylinderDiagram d ℳ p ℒ H h h' D).levelPathProduct k
        ((cylinderPathLift d ℳ p ℒ H h h' D k v).mapPath q) =
      ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)).bchGroupMap
        (D.levelPathProduct k q) := by
  rw [levelPathProduct_cylinderDiagram]
  have he := congrArg
    (fun F : WallComplement (fun a : D.active k => (D.wall a).support) ⥤q
      WallComplement (fun a : D.active k => (D.wall a).support) =>
        D.levelPathProduct k (F.mapPath q))
    (cylinderPathLift_comp_projection d ℳ p ℒ H h h' D k v)
  simp only [Prefunctor.mapPath_comp_apply, Prefunctor.mapPath_id] at he
  exact congrArg _ he

/-- Charge-zero probe cylinders are consistent at exactly the consistent base cutoffs. -/
@[simp]
theorem cylinderDiagram_levelConsistent_iff (k : ℕ) :
    (cylinderDiagram d ℳ p ℒ H h h' D).LevelConsistent k ↔ D.LevelConsistent k := by
  rw [DirectedDiagram.levelConsistent_def, DirectedDiagram.levelConsistent_def]
  constructor
  · intro hc x y q q'
    apply LieHom.bchGroupMap_injective
      (Function.LeftInverse.injective (baseQuotientProjection_base d ℳ p ℒ k))
    simpa only [levelPathProduct_cylinderPathLift] using
      hc ((cylinderPathLift d ℳ p ℒ H h h' D k (0 : E)).mapPath q)
        ((cylinderPathLift d ℳ p ℒ H h h' D k (0 : E)).mapPath q')
  · intro hc x y q q'
    rw [levelPathProduct_cylinderDiagram, levelPathProduct_cylinderDiagram, hc]

/-- The charge-zero cylinder construction preserves and reflects all-order consistency. -/
@[simp]
theorem cylinderDiagram_consistent_iff :
    (cylinderDiagram d ℳ p ℒ H h h' D).Consistent ↔ D.Consistent := by
  simp only [DirectedDiagram.consistent_iff, cylinderDiagram_levelConsistent_iff]

/-- Finite endpoint transport through probe cylinders depends on the base endpoints
through the charge-zero inclusion. -/
@[simp]
theorem levelTransport_cylinderDiagram {k : ℕ} (hD : D.LevelConsistent k)
    (x y : WallComplement (fun a : (cylinderDiagram d ℳ p ℒ H h h' D).active k =>
      ((cylinderDiagram d ℳ p ℒ H h h' D).wall a).support)) :
    (cylinderDiagram d ℳ p ℒ H h h' D).levelTransport k
        ((cylinderDiagram_levelConsistent_iff d ℳ p ℒ H h h' D k).mpr hD) x y =
      ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)).bchGroupMap
        (D.levelTransport k hD ((cylinderPathProjection d ℳ p ℒ H h h' D k).obj x)
          ((cylinderPathProjection d ℳ p ℒ H h h' D k).obj y)) := by
  obtain ⟨q⟩ := (cylinderDiagram d ℳ p ℒ H h h' D).exists_level_path k x y
  rw [DirectedDiagram.levelTransport_eq_levelPathProduct _ _ q,
    levelPathProduct_cylinderDiagram, D.levelTransport_eq_levelPathProduct hD]

/-- Cylinders over an outgoing base completion complete the cylinder input. -/
theorem cylinderDiagram_isOutgoingCompletion {ι₀ κ : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H}
    {C : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)}
    (hC : DirectedDiagram.IsOutgoingCompletion D₀ C) :
    DirectedDiagram.IsOutgoingCompletion (fun a => baseCylinder d ℳ p ℒ H h h' (D₀ a))
      (cylinderDiagram d ℳ p ℒ H h h' C) where
  wall_inl a := by rw [cylinderDiagram_wall, hC.wall_inl]
  outgoing_inr a := by simpa using hC.outgoing_inr a
  consistent := (cylinderDiagram_consistent_iff d ℳ p ℒ H h h' C).mpr hC.consistent

end Mei.ModuleProbe
