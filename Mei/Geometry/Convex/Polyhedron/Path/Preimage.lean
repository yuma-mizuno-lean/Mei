/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Cylinder
public import Mei.Geometry.Convex.Polyhedron.Path.AffineTransport

/-!
# Paths through preimages of walls under linear surjections

A surjective linear map `A : V → V'` from a finite-dimensional real space is the first
coordinate of a continuous linear equivalence `V ≃ V' × ker A`. Under this equivalence the
preimage `A⁻¹(W)` of a wall becomes the cylinder `W × ker A`. Hence `A` carries allowed
points and admissible segments for a pulled-back wall family to allowed points and admissible
segments for the original family. Every polygonal wall product through the preimages is the
product along the image path, for the pulled-back normals `ν ∘ A`. A linear section of `A`
lifts admissible paths back, so `A` induces a retraction of path quivers. Coincident and
repeated walls retain separate factors, and the wall indices may be reindexed.

This combines `LinearMap.prodKerEquiv`, `ContinuousAffineEquiv.wallComplementMap`,
`WallComplement.cylinderProjection` and `WallComplement.cylinderLift`.
-/

public section

open TauCeti (WallComplement AdmissiblePLPath)

noncomputable section

open Set

namespace TauCeti.WallComplement

variable {V V' ι ι' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V]
  (A : V →ₗ[ℝ] V') (hA : Function.Surjective A) (W : ι → Set V') {W' : ι' → Set V}
  (r : ι' ≃ ι) (hW : ∀ j, W' j = A ⁻¹' W (r j))

include hW in
/-- Under the splitting, each preimage wall is the cylinder over the original wall. -/
theorem prod_univ_eq_image_prodKerEquiv (j : ι') :
    W (r j) ×ˢ (univ : Set (LinearMap.ker A)) =
      (A.prodKerEquiv hA).toContinuousLinearEquiv.toContinuousAffineEquiv '' W' j := by
  rw [hW, ContinuousLinearEquiv.coe_toContinuousAffineEquiv,
    LinearEquiv.coe_toContinuousLinearEquiv', A.image_prodKerEquiv_preimage hA]

include hW in
/-- The inverse splitting carries each cylinder wall back to the preimage wall. -/
theorem eq_image_prodKerEquiv_symm (j : ι) :
    W' (r.symm j) = (A.prodKerEquiv hA).toContinuousLinearEquiv.symm.toContinuousAffineEquiv ''
      (W j ×ˢ (univ : Set (LinearMap.ker A))) := by
  rw [hW, r.apply_symm_apply, ContinuousLinearEquiv.coe_toContinuousAffineEquiv,
    LinearEquiv.coe_toContinuousLinearEquiv_symm', A.image_prodKerEquiv_symm_prod_univ hA]

/-- Push allowed points and admissible segments for the preimage walls `A⁻¹(W (r j))`
forward along a linear surjection `A`. Use `Prefunctor.mapPath` for polygonal paths. -/
def preimageProjection : WallComplement W' ⥤q WallComplement W :=
  (A.prodKerEquiv hA).toContinuousLinearEquiv.toContinuousAffineEquiv.wallComplementMap r
      (prod_univ_eq_image_prodKerEquiv A hA W r hW) ⋙q
    cylinderProjection (E := LinearMap.ker A) W

/-- The projection applies the surjection to the actual spatial point. -/
@[simp]
theorem preimageProjection_obj_val (x : WallComplement W') :
    ((preimageProjection A hA W r hW).obj x).val = A x.val := by
  rw [preimageProjection, Prefunctor.comp_obj, cylinderProjection_obj_val,
    ContinuousAffineEquiv.wallComplementMap_obj_val,
    ContinuousLinearEquiv.coe_toContinuousAffineEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearMap.prodKerEquiv_apply_fst]

instance : (preimageProjection A hA W r hW).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Lift allowed points and admissible segments along the linear section of `A` given by
the splitting of `V` with zero kernel coordinate. -/
def preimageLift : WallComplement W ⥤q WallComplement W' :=
  cylinderLift W (0 : LinearMap.ker A) ⋙q
    (A.prodKerEquiv hA).toContinuousLinearEquiv.symm.toContinuousAffineEquiv.wallComplementMap
      r.symm (eq_image_prodKerEquiv_symm A hA W r hW)

/-- The lift of a point is a preimage of it. -/
@[simp]
theorem apply_preimageLift_obj_val (x : WallComplement W) :
    A ((preimageLift A hA W r hW).obj x).val = x.val := by
  rw [preimageLift, Prefunctor.comp_obj, ContinuousAffineEquiv.wallComplementMap_obj_val,
    cylinderLift_obj_val, ContinuousLinearEquiv.coe_toContinuousAffineEquiv,
    LinearEquiv.coe_toContinuousLinearEquiv_symm', LinearMap.apply_prodKerEquiv_symm]

instance : (preimageLift A hA W r hW).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projection is a retraction of the lift. -/
@[simp]
theorem preimageLift_comp_preimageProjection :
    preimageLift A hA W r hW ⋙q preimageProjection A hA W r hW = Prefunctor.id _ := by
  refine Prefunctor.ext (fun x => WallComplement.ext ?_) ?_
  · simp
  · intros
    exact PLift.ext (Subsingleton.elim _ _)

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti.WallComplement

variable {V V' ι ι' G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V] [Finite ι] [Finite ι']
  [Group G] (A : V →ₗ[ℝ] V') (hA : Function.Surjective A) {W : ι → Set V'} {W' : ι' → Set V}
  (r : ι' ≃ ι) (hW : ∀ j, W' j = A ⁻¹' W (r j))
  {x y : WallComplement W'}

/-- The product along the image of a path through preimage walls is the product along the
original path for the pulled-back normals. Simultaneous and repeated crossings are retained. -/
theorem wallPathProduct_preimageProjection (ν : ι → V' →ₗ[ℝ] ℝ) (label : ι → G)
    (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (comm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) →
      Commute (label (r i)) (label (r j)))
    (p : AdmissiblePLPath x y) :
    ((preimageProjection A hA W r hW).mapPath p).wallPathProduct ν label comm =
      p.wallPathProduct (fun j => (ν (r j)).comp A) (fun j => label (r j)) comm' := by
  let e := (A.prodKerEquiv hA).toContinuousLinearEquiv.toContinuousAffineEquiv
  have hp := p.wallPathProduct_wallComplementMap e r
    (prod_univ_eq_image_prodKerEquiv A hA W r hW)
    (fun j => (ν (r j)).comp A) (fun j => (ν j).comp (LinearMap.fst ℝ V' (LinearMap.ker A)))
    (fun j => LinearMap.ext fun v => congrArg (ν (r j)) (A.prodKerEquiv_apply_fst hA v))
    (fun j => label (r j)) label comm' (fun i j h => comm i j
      ((Mei.affineSpan_prod_univ_eq_iff (W i) (W j)).mp h))
    (MonoidHom.id G) (fun _ => rfl)
  rw [preimageProjection, Prefunctor.mapPath_comp_apply]
  exact (wallPathProduct_cylinderProjection W ν label comm _).trans hp

end Quiver.Path
