/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Map
public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.PathMap

/-!
# Affine transport of crossing words

Integral affine equivalences identify the walls of a complex with the walls
of its image. They transport admissible paths, preserving the ordered crossing
parameters. Transporting normal functionals by the inverse linear map preserves
crossing signs, so the crossing word changes by the induced wall bijection.
This applies to orientation-reversing maps as well as translations.

The proofs use Mathlib's dimension invariance under linear equivalences,
`Prefunctor.mapPath`, and `FreeGroup.map`, together with the geometric
membership and order characterization of `orderedCrossings`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  (C : FinitePolyhedralComplex h) (e : Mei.Toric.IntegralAffineEquiv h h')

/-- Affine transport preserves every exact ambient cell codimension. -/
theorem mem_cellsOfCodimension_image (k : ℕ) (Q : Set V') :
    Q ∈ (C.image e).cellsOfCodimension k ↔
      ∃ P ∈ C.cellsOfCodimension k, e '' P = Q := by
  have hd (P : Set V) : Module.finrank ℝ (affineSpan ℝ (e '' P)).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction := by
    have he : (affineSpan ℝ (e '' P)).direction =
        ((affineSpan ℝ P).direction).map e.toAffineEquiv.linear.toLinearMap := by
      simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe] using
        e.toAffineEquiv.toAffineMap.direction_affineSpan_image P
    rw [he, e.toAffineEquiv.linear.finrank_map_eq]
  have hv := e.toAffineEquiv.linear.finrank_eq
  simp only [mem_cellsOfCodimension, mem_cells_image]
  constructor
  · rintro ⟨⟨P, hP, rfl⟩, hdim⟩
    exact ⟨P, ⟨hP, by rwa [hd, ← hv] at hdim⟩, rfl⟩
  · rintro ⟨P, ⟨hP, hdim⟩, rfl⟩
    exact ⟨⟨P, hP, rfl⟩, by rw [hd, ← hv]; exact hdim⟩

/-- The bijection from original walls to their actual affine image carriers. -/
def wallImageEquiv : C.walls ≃ (C.image e).walls :=
  Equiv.ofBijective
    (fun P => ⟨e '' (P : Set V), (C.mem_cellsOfCodimension_image e 1 _).mpr
      ⟨P, P.property, rfl⟩⟩)
    ⟨fun P Q he => Subtype.ext (e.toAffineEquiv.injective.image_injective
        (congrArg Subtype.val he)),
      fun Q => by
        obtain ⟨P, hP, hPQ⟩ := (C.mem_cellsOfCodimension_image e 1 Q).mp Q.property
        exact ⟨⟨P, hP⟩, Subtype.ext hPQ⟩⟩

@[simp]
theorem wallImageEquiv_coe (P : C.walls) :
    (C.wallImageEquiv e P : Set V') = e '' (P : Set V) := (rfl)

/-- The inverse wall bijection takes the inverse image carrier. -/
@[simp]
theorem wallImageEquiv_symm_coe (Q : (C.image e).walls) :
    ((C.wallImageEquiv e).symm Q : Set V) = e.symm '' (Q : Set V') := by
  have he := C.wallImageEquiv_coe e ((C.wallImageEquiv e).symm Q)
  rw [Equiv.apply_symm_apply] at he
  have hi := congrArg (fun P : Set V' => e.symm '' P) he
  simpa only [Mei.Toric.IntegralAffineEquiv.symm_image_image] using hi.symm

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
  constructor
  · intro hb
    obtain ⟨⟨P', s⟩, hb', he'⟩ := List.mem_map.mp hb
    have hp := congrArg Prod.fst he'
    have hs := congrArg Prod.snd he'
    dsimp only at hp hs
    obtain rfl := (C.wallImageEquiv e).injective hp
    obtain rfl := hs
    exact (C.mem_orderedCrossings a _).mp hb'
  · intro hb
    exact List.mem_map.mpr ⟨(P, t), (C.mem_orderedCrossings a _).mpr hb, rfl⟩

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

end Quiver.Path
