/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Map
public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.PolyhedralComplex.Itinerary
public import Mei.Geometry.Convex.Polyhedron.Path.Map

/-!
# Affine transport of crossing words and chambers

Integral affine equivalences identify the walls of a complex with the walls
of its image. They transport admissible paths, preserving the ordered crossing
parameters. Transporting normal functionals by the inverse linear map preserves
crossing signs, so the crossing word changes by the induced wall bijection.
This applies to orientation-reversing maps as well as translations.

The chambers of the complement of the walls are identified with those of the image
complement. The positive and negative chambers of a wall go to those of its image
wall for pulled-back coorientations, so the signed crossing letters of a polygonal path are
transported by the wall bijection.

The proofs use Mathlib's `Prefunctor.mapPath` and `FreeGroup.map`, together
with the geometric membership and order characterization of `orderedCrossings`.
-/

public section

noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace Mei.FinitePolyhedralComplex

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  (C : FinitePolyhedralComplex h) (e : Mei.Toric.IntegralAffineEquiv h h')

/-- Transport the allowed vertices and segments to the image complex. -/
def pathImage : WallComplement (fun P : C.walls => (P : Set V)) ⥤q
    WallComplement (fun Q : (C.image e).walls => (Q : Set V')) := by
  letI := h.finiteDimensional
  exact ContinuousAffineEquiv.wallComplementMap e.toAffineEquiv.toContinuousAffineEquiv
    (C.wallImageEquiv e) (fun P => (C.wallImageEquiv_coe e P).trans (by
      rw [AffineEquiv.coe_toContinuousAffineEquiv]))

@[simp]
theorem pathImage_obj_val (x : WallComplement (fun P : C.walls => (P : Set V))) :
    ((C.pathImage e).obj x).val = e x.val := by
  let := h.finiteDimensional
  unfold pathImage
  rw [ContinuousAffineEquiv.wallComplementMap_obj_val, AffineEquiv.coe_toContinuousAffineEquiv]

/-- Pull an admissible path in the image complex back to the original complex.
The target uses the original wall family, without transporting it twice. -/
def pathPreimage : WallComplement (fun Q : (C.image e).walls => (Q : Set V')) ⥤q
    WallComplement (fun P : C.walls => (P : Set V)) := by
  letI := h.finiteDimensional
  letI := h'.finiteDimensional
  exact ContinuousAffineEquiv.wallComplementMap e.symm.toAffineEquiv.toContinuousAffineEquiv
    (C.wallImageEquiv e).symm (fun Q => (C.wallImageEquiv_symm_coe e Q).trans (by
      rw [AffineEquiv.coe_toContinuousAffineEquiv]))

@[simp]
theorem pathPreimage_obj_val
    (x : WallComplement (fun Q : (C.image e).walls => (Q : Set V'))) :
    ((C.pathPreimage e).obj x).val = e.symm x.val := by
  let := h.finiteDimensional
  let := h'.finiteDimensional
  unfold pathPreimage
  rw [ContinuousAffineEquiv.wallComplementMap_obj_val, AffineEquiv.coe_toContinuousAffineEquiv]

instance : (C.pathPreimage e).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Every vertex of a transported polygonal path is its affine image. -/
theorem vertices_pathImage
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) :
    ((C.pathImage e).mapPath p).vertices.map WallComplement.val =
      (p.vertices.map WallComplement.val).map e := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def, pathImage_obj_val]

/-- Every vertex of a pulled-back polygonal path is its inverse affine image. -/
theorem vertices_pathPreimage
    {x y : WallComplement (fun Q : (C.image e).walls => (Q : Set V'))}
    (p : AdmissiblePLPath x y) :
    ((C.pathPreimage e).mapPath p).vertices.map WallComplement.val =
      (p.vertices.map WallComplement.val).map e.symm := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def, pathPreimage_obj_val]

/-- The image of an admissible crossing has the same affine parameter. -/
theorem mem_crossings_pathImage
    (x y : WallComplement (fun P : C.walls => (P : Set V))) (P : C.walls) (t : ℝ) :
    (C.wallImageEquiv e P, t) ∈
      WallComplement.crossings ((C.pathImage e).obj x) ((C.pathImage e).obj y) ↔
        (P, t) ∈ WallComplement.crossings x y := by
  simp only [WallComplement.mem_crossings, pathImage_obj_val, wallImageEquiv_coe]
  have hl := e.toAffineEquiv.apply_lineMap x.val y.val t
  rw [← hl, e.toAffineEquiv.injective.mem_set_image]

instance : (C.pathImage e).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

variable {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- The ordered crossings transform by the wall bijection without reordering. -/
@[simp]
theorem orderedCrossings_pathImage (a : x ⟶ y) :
    (C.image e).orderedCrossings ((C.pathImage e).map a) =
      (C.orderedCrossings a).map (fun b => (C.wallImageEquiv e b.1, b.2)) := by
  symm
  apply ((C.image e).orderedCrossings_eq_iff _ _).mpr
  refine ⟨List.pairwise_map.mpr (C.pairwise_orderedCrossings a), ?_⟩
  rintro ⟨Q, t⟩
  obtain ⟨P, rfl⟩ := (C.wallImageEquiv e).surjective Q
  rw [C.mem_crossings_pathImage]
  exact (List.mem_map_of_injective
    ((C.wallImageEquiv e).injective.prodMap Function.injective_id) (a := (P, t))).trans
      (C.mem_orderedCrossings a _)

/-- Inverse-dual transport preserves each signed crossing letter. The hypothesis
allows any target representatives with the specified pullback. -/
theorem crossingLetter_pathImage
    (ν : C.walls → V →ₗ[ℝ] ℝ) (ν' : (C.image e).walls → V' →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν' (C.wallImageEquiv e P)).comp e.toAffineEquiv.linear.toLinearMap = ν P)
    (P : C.walls) :
    (C.image e).crossingLetter ν' ((C.pathImage e).obj x) ((C.pathImage e).obj y)
        (C.wallImageEquiv e P) = FreeGroup.map (C.wallImageEquiv e) (C.crossingLetter ν x y P) := by
  have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val :=
    e.toAffineEquiv.toAffineMap.linear_apply_vsub y.val x.val
  have hn := congrArg (fun f : V →ₗ[ℝ] ℝ => f (y.val - x.val)) (hν P)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hn
  simp only [crossingLetter_def, pathImage_obj_val, ← hv, hn]
  split <;> simp

/-- Affine transport sends a segment word along the induced free-group map. -/
theorem segmentCrossingWord_pathImage
    (ν : C.walls → V →ₗ[ℝ] ℝ) (ν' : (C.image e).walls → V' →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν' (C.wallImageEquiv e P)).comp e.toAffineEquiv.linear.toLinearMap = ν P)
    (a : x ⟶ y) :
    (C.image e).segmentCrossingWord ν' ((C.pathImage e).map a) =
      FreeGroup.map (C.wallImageEquiv e) (C.segmentCrossingWord ν a) := by
  simp only [segmentCrossingWord_def, orderedCrossings_pathImage, List.map_reverse,
    List.map_map, Function.comp_def, crossingLetter_pathImage C e ν ν' hν,
    MonoidHom.map_list_prod]

/-- The homeomorphism underlying an integral affine equivalence acts as the equivalence. -/
theorem coe_toHomeomorph [FiniteDimensional ℝ V] :
    ⇑e.toAffineEquiv.toContinuousAffineEquiv.toHomeomorph = ⇑e.toAffineEquiv := rfl

/-- Affine transport identifies the chambers of a complex with those of its image. -/
def chamberEquiv : Chamber (fun P : C.walls => (P : Set V)) ≃
    Chamber (fun Q : (C.image e).walls => (Q : Set V')) := by
  letI := h.finiteDimensional
  exact WallComplement.chamberEquiv e.toAffineEquiv.toContinuousAffineEquiv.toHomeomorph
    (C.wallImageEquiv e) (fun P => (C.wallImageEquiv_coe e P).trans (by rw [coe_toHomeomorph]))

/-- The identification of chambers sends the chamber of an allowed point to the chamber of
its image. -/
theorem chamberEquiv_chamber (x : WallComplement (fun P : C.walls => (P : Set V))) :
    (C.chamberEquiv e) (chamber x) = chamber ((C.pathImage e).obj x) := by
  let := h.finiteDimensional
  exact WallComplement.chamberEquiv_chamber _ _ _ x _ (by rw [pathImage_obj_val, coe_toHomeomorph])

/-- A point of the carrier of a chamber is carried into the carrier of the identified
chamber. -/
theorem image_mem_carrier_chamberEquiv {c : Chamber (fun P : C.walls => (P : Set V))}
    {z : V} (hz : z ∈ c.carrier) : e z ∈ ((C.chamberEquiv e) c).carrier := by
  let := h.finiteDimensional
  exact WallComplement.image_mem_carrier_chamberEquiv _ _ _ hz

/-- Affine transport sends the positive chamber of a wall to the positive chamber of its
image wall, for coorientations related by pulling back along the linear part. -/
theorem chamberEquiv_positiveChamber (P : C.walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) (ν' : V' →ₗ[ℝ] ℝ)
    (hν' : LinearMap.ker ν' = (affineSpan ℝ (C.wallImageEquiv e P : Set V')).direction)
    (hνν' : ν'.comp e.toAffineEquiv.linear.toLinearMap = ν) :
    (C.chamberEquiv e) (C.positiveChamber P ν hν) =
      (C.image e).positiveChamber (C.wallImageEquiv e P) ν' hν' := by
  refine (existsUnique_positiveChamber (C := C.image e) (C.wallImageEquiv e P) ν' hν').unique
    ?_ fun q hq v hv => eventually_add_smul_mem_positiveChamber hν' hq hv
  intro q' hq' v' hv'
  let := h.finiteDimensional
  rw [wallImageEquiv_coe, ← AffineEquiv.coe_toContinuousAffineEquiv e.toAffineEquiv,
    ContinuousAffineEquiv.intrinsicInterior_image] at hq'
  obtain ⟨q, hq, rfl⟩ := hq'
  have hv : 0 < ν (e.toAffineEquiv.linear.symm v') := by
    rw [← hνν']
    simpa using hv'
  filter_upwards [eventually_add_smul_mem_positiveChamber hν hq hv] with t ht
  have hmap := C.image_mem_carrier_chamberEquiv e ht
  have hvadd := e.toAffineEquiv.map_vadd q (t • e.toAffineEquiv.linear.symm v')
  simp only [vadd_eq_add, map_smul, LinearEquiv.apply_symm_apply] at hvadd
  rw [add_comm q, hvadd, add_comm] at hmap
  exact hmap

/-- Affine transport sends the negative chamber of a wall to the negative chamber of its
image wall, for coorientations related by pulling back along the linear part. -/
theorem chamberEquiv_negativeChamber (P : C.walls) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) (ν' : V' →ₗ[ℝ] ℝ)
    (hν' : LinearMap.ker ν' = (affineSpan ℝ (C.wallImageEquiv e P : Set V')).direction)
    (hνν' : ν'.comp e.toAffineEquiv.linear.toLinearMap = ν) :
    (C.chamberEquiv e) (C.negativeChamber P ν hν) =
      (C.image e).negativeChamber (C.wallImageEquiv e P) ν' hν' := by
  rw [← positiveChamber_neg hν, ← positiveChamber_neg hν']
  exact C.chamberEquiv_positiveChamber e P (-ν) _ (-ν') _ (by rw [← hνν', LinearMap.neg_comp])

/-- The inverse identification sends the positive chamber of an image wall to the positive
chamber of the wall it comes from. -/
theorem chamberEquiv_symm_positiveChamber (P : C.walls) (Q : (C.image e).walls)
    (hPQ : C.wallImageEquiv e P = Q) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) (ν' : V' →ₗ[ℝ] ℝ)
    (hν' : LinearMap.ker ν' = (affineSpan ℝ (Q : Set V')).direction)
    (hνν' : ν'.comp e.toAffineEquiv.linear.toLinearMap = ν) :
    (C.chamberEquiv e).symm ((C.image e).positiveChamber Q ν' hν') =
      C.positiveChamber P ν hν := by
  subst hPQ
  exact (Equiv.symm_apply_eq _).mpr (C.chamberEquiv_positiveChamber e P ν hν ν' hν' hνν').symm

/-- The inverse identification sends the negative chamber of an image wall to the negative
chamber of the wall it comes from. -/
theorem chamberEquiv_symm_negativeChamber (P : C.walls) (Q : (C.image e).walls)
    (hPQ : C.wallImageEquiv e P = Q) (ν : V →ₗ[ℝ] ℝ)
    (hν : LinearMap.ker ν = (affineSpan ℝ (P : Set V)).direction) (ν' : V' →ₗ[ℝ] ℝ)
    (hν' : LinearMap.ker ν' = (affineSpan ℝ (Q : Set V')).direction)
    (hνν' : ν'.comp e.toAffineEquiv.linear.toLinearMap = ν) :
    (C.chamberEquiv e).symm ((C.image e).negativeChamber Q ν' hν') =
      C.negativeChamber P ν hν := by
  subst hPQ
  exact (Equiv.symm_apply_eq _).mpr (C.chamberEquiv_negativeChamber e P ν hν ν' hν' hνν').symm

/-- The coorientation of an image wall: the original one, pulled back along the inverse
linear part. -/
def imageNormal (ν : C.walls → V →ₗ[ℝ] ℝ) (Q : (C.image e).walls) : V' →ₗ[ℝ] ℝ :=
  (ν ((C.wallImageEquiv e).symm Q)).comp e.toAffineEquiv.linear.symm.toLinearMap

/-- Image coorientations are given by the original ones through the wall bijection. -/
@[simp]
theorem imageNormal_apply (ν : C.walls → V →ₗ[ℝ] ℝ) (Q : (C.image e).walls) :
    C.imageNormal e ν Q = (ν ((C.wallImageEquiv e).symm Q)).comp
      e.toAffineEquiv.linear.symm.toLinearMap := (rfl)

/-- The image coorientation of a wall cuts out exactly the direction of the image wall. -/
theorem ker_imageNormal (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    (Q : (C.image e).walls) :
    LinearMap.ker (C.imageNormal e ν Q) = (affineSpan ℝ (Q : Set V')).direction := by
  obtain ⟨P, rfl⟩ := (C.wallImageEquiv e).surjective Q
  rw [imageNormal_apply, Equiv.symm_apply_apply, LinearMap.ker_comp, hν,
    C.wallImageEquiv_coe]
  have hd : (affineSpan ℝ (e '' (P : Set V))).direction =
      ((affineSpan ℝ (P : Set V)).direction).map e.toAffineEquiv.linear.toLinearMap := by
    simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe] using
      e.toAffineEquiv.toAffineMap.direction_affineSpan_image (P : Set V)
  rw [hd, Submodule.map_equiv_eq_comap_symm]

/-- Pulling the coorientation of an image wall back along the linear part recovers the
coorientation of the original wall. -/
theorem imageNormal_comp_symm (ν : C.walls → V →ₗ[ℝ] ℝ) (Q : (C.image e).walls) :
    (C.imageNormal e ν Q).comp e.toAffineEquiv.linear.toLinearMap =
      ν ((C.wallImageEquiv e).symm Q) := by
  ext v
  simp

/-- Pulling an image coorientation back along the linear part recovers the original. -/
theorem imageNormal_comp (ν : C.walls → V →ₗ[ℝ] ℝ) (P : C.walls) :
    (C.imageNormal e ν (C.wallImageEquiv e P)).comp e.toAffineEquiv.linear.toLinearMap =
      ν P := by
  simpa using C.imageNormal_comp_symm e ν (C.wallImageEquiv e P)

variable (ν : C.walls → V →ₗ[ℝ] ℝ)
  (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
  (ν' : (C.image e).walls → V' →ₗ[ℝ] ℝ)
  (hν' : ∀ Q, LinearMap.ker (ν' Q) = (affineSpan ℝ (Q : Set V')).direction)
  (hνν' : ∀ P, (ν' (C.wallImageEquiv e P)).comp e.toAffineEquiv.linear.toLinearMap = ν P)

include hνν' in
/-- A crossing letter starts at the identified chamber after transport. -/
theorem chamberEquiv_crossingSource (l : C.walls × Bool) :
    (C.chamberEquiv e) (C.crossingSource ν hν l) =
      (C.image e).crossingSource ν' hν' (Prod.map (C.wallImageEquiv e) id l) := by
  obtain ⟨P, _ | _⟩ := l
  · exact C.chamberEquiv_positiveChamber e P (ν P) (hν P) (ν' _) (hν' _) (hνν' P)
  · exact C.chamberEquiv_negativeChamber e P (ν P) (hν P) (ν' _) (hν' _) (hνν' P)

include hνν' in
/-- A crossing letter ends at the identified chamber after transport. -/
theorem chamberEquiv_crossingTarget (l : C.walls × Bool) :
    (C.chamberEquiv e) (C.crossingTarget ν hν l) =
      (C.image e).crossingTarget ν' hν' (Prod.map (C.wallImageEquiv e) id l) := by
  obtain ⟨P, _ | _⟩ := l
  · exact C.chamberEquiv_negativeChamber e P (ν P) (hν P) (ν' _) (hν' _) (hνν' P)
  · exact C.chamberEquiv_positiveChamber e P (ν P) (hν P) (ν' _) (hν' _) (hνν' P)

include hνν' in
/-- The inverse identification of chambers sends the start of a transported crossing letter
back to the start of the letter. -/
theorem chamberEquiv_symm_crossingSource (l : C.walls × Bool) :
    (C.chamberEquiv e).symm
        ((C.image e).crossingSource ν' hν' (Prod.map (C.wallImageEquiv e) id l)) =
      C.crossingSource ν hν l :=
  (Equiv.symm_apply_eq _).mpr (C.chamberEquiv_crossingSource e ν hν ν' hν' hνν' l).symm

include hνν' in
/-- The inverse identification of chambers sends the end of a transported crossing letter
back to the end of the letter. -/
theorem chamberEquiv_symm_crossingTarget (l : C.walls × Bool) :
    (C.chamberEquiv e).symm
        ((C.image e).crossingTarget ν' hν' (Prod.map (C.wallImageEquiv e) id l)) =
      C.crossingTarget ν hν l :=
  (Equiv.symm_apply_eq _).mpr (C.chamberEquiv_crossingTarget e ν hν ν' hν' hνν' l).symm

variable {x y : WallComplement (fun P : C.walls => (P : Set V))}

include hνν' in
/-- Affine transport sends the crossing letters of a segment through the wall bijection,
keeping the signs. -/
theorem segmentCrossingLetters_pathImage (a : x ⟶ y) :
    (C.image e).segmentCrossingLetters ν' ((C.pathImage e).map a) =
      (C.segmentCrossingLetters ν a).map (Prod.map (C.wallImageEquiv e) id) := by
  have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val :=
    e.toAffineEquiv.toAffineMap.linear_apply_vsub y.val x.val
  have hdiff : ((C.pathImage e).obj y).val - ((C.pathImage e).obj x).val =
      e.toAffineEquiv.linear (y.val - x.val) := by
    rw [hv, pathImage_obj_val, pathImage_obj_val]
  simp only [segmentCrossingLetters_def, orderedCrossings_pathImage, List.map_map,
    Function.comp_def]
  refine List.map_congr_left fun b _ => ?_
  have hn := congrArg (fun f : V →ₗ[ℝ] ℝ => f (y.val - x.val)) (hνν' b.1)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hn
  simp only [Prod.map_apply, id_eq, hdiff, hn]

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Affine transport preserves the polygonal crossing word through the wall bijection.
The normals transform by pullback along the inverse linear part; no determinant
sign is inserted. -/
theorem crossingWord_pathImage (p : AdmissiblePLPath x y)
    (e : Mei.Toric.IntegralAffineEquiv h h')
    (ν : C.walls → V →ₗ[ℝ] ℝ) (ν' : (C.image e).walls → V' →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν' (C.wallImageEquiv e P)).comp e.toAffineEquiv.linear.toLinearMap = ν P) :
    ((C.pathImage e).mapPath p).crossingWord ν' =
      FreeGroup.map (C.wallImageEquiv e) (p.crossingWord ν) := by
  induction p with
  | nil => simp
  | cons p a ih =>
    simp [C.segmentCrossingWord_pathImage e ν ν' hν, ih]

/-- Affine transport sends the crossing letters of a polygonal path through the wall
bijection, keeping the order and the signs. -/
theorem crossingLetters_pathImage (p : AdmissiblePLPath x y)
    (e : Mei.Toric.IntegralAffineEquiv h h')
    (ν : C.walls → V →ₗ[ℝ] ℝ) (ν' : (C.image e).walls → V' →ₗ[ℝ] ℝ)
    (hνν' : ∀ P, (ν' (C.wallImageEquiv e P)).comp e.toAffineEquiv.linear.toLinearMap = ν P) :
    ((C.pathImage e).mapPath p).crossingLetters ν' =
      (p.crossingLetters ν).map (Prod.map (C.wallImageEquiv e) id) := by
  induction p with
  | nil => simp
  | cons p a ih =>
    simp [C.segmentCrossingLetters_pathImage e ν ν' hνν', ih]

end Quiver.Path
