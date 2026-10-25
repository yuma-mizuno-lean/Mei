/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Map
public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.AffinePath

/-!
# Affine covariance of signed crossing words

Integral affine equivalences carry admissible polygonal paths to paths through
the image complex. The ordered geometric crossing list changes only by the wall
bijection: times and signs are unchanged when normals are pulled back by the
inverse linear part. The resulting crossing word is the image under
`FreeGroup.map`, including for orientation-reversing coordinate changes.

This uses Mathlib's `Prefunctor.mapPath`, `FreeGroup.map` and list operations,
and the membership and strict-order characterization of Mei's crossing lists.
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
  (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')

/-- Transport admissible paths through a complex to its integral affine image.
Use `Prefunctor.mapPath` to apply this to an entire polygonal chain. -/
def imagePrefunctor :
    WallComplement (fun P : C.walls => (P : Set V)) ⥤q
      WallComplement (fun P : (C.image e).walls => (P : Set V')) := by
  letI := h.finiteDimensional
  exact e.toAffineEquiv.imagePrefunctor (C.wallImageEquiv e) _ _
    (C.coe_wallImageEquiv e)

/-- The affine path map sends vertices to their actual coordinate images. -/
@[simp]
theorem imagePrefunctor_obj_val (x : WallComplement (fun P : C.walls => (P : Set V))) :
    ((C.imagePrefunctor e).obj x).val = e x.val := by
  simp [imagePrefunctor]

variable {C} {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Transporting a segment bijects its wall crossings, with unchanged parameters. -/
@[simp high]
theorem mem_crossings_image (P : C.walls) (t : ℝ) :
    (C.wallImageEquiv e P, t) ∈ WallComplement.crossings
        ((C.imagePrefunctor e).obj x) ((C.imagePrefunctor e).obj y) ↔
      (P, t) ∈ WallComplement.crossings x y := by
  let := h.finiteDimensional
  exact e.toAffineEquiv.mem_crossings_image (C.wallImageEquiv e) _ _
    (C.coe_wallImageEquiv e) x y P t

/-- Affine transport changes only the wall indices of the ordered crossing list. -/
theorem orderedCrossings_image (a : x ⟶ y) :
    (C.image e).orderedCrossings ((C.imagePrefunctor e).map a) =
      (C.orderedCrossings a).map (fun b => (C.wallImageEquiv e b.1, b.2)) := by
  symm
  apply ((C.image e).orderedCrossings_eq_iff _ _).mpr
  constructor
  · exact List.pairwise_map.mpr (C.pairwise_orderedCrossings a)
  · intro b
    obtain ⟨P, hP⟩ := (C.wallImageEquiv e).surjective b.1
    obtain ⟨Q, t⟩ := b
    dsimp at hP
    subst Q
    simp only [List.mem_map, mem_crossings_image]
    constructor
    · rintro ⟨⟨Q, s⟩, ha, he⟩
      obtain ⟨heQ, rfl⟩ := Prod.mk.inj he
      obtain rfl := (C.wallImageEquiv e).injective heQ
      exact (C.mem_orderedCrossings a _).mp ha
    · intro hb
      exact ⟨(P, t), (C.mem_orderedCrossings a _).mpr hb, rfl⟩

/-- The inverse-dual normal has the same crossing sign in the image coordinates. -/
theorem crossingLetter_image (ν : C.walls → V →ₗ[ℝ] ℝ) (P : C.walls) :
    (C.image e).crossingLetter
        (fun Q => (ν ((C.wallImageEquiv e).symm Q)).comp
          e.toAffineEquiv.linear.symm.toLinearMap)
        ((C.imagePrefunctor e).obj x) ((C.imagePrefunctor e).obj y)
        (C.wallImageEquiv e P) =
      FreeGroup.map (C.wallImageEquiv e) (C.crossingLetter ν x y P) := by
  have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val :=
    e.toAffineEquiv.toAffineMap.linear_apply_vsub y.val x.val
  simp only [crossingLetter_def, imagePrefunctor_obj_val, Equiv.symm_apply_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, ← hv, LinearEquiv.symm_apply_apply]
  split_ifs <;> simp only [map_inv, FreeGroup.map.of]

/-- Signed segment words are covariant under the induced wall bijection. -/
@[simp]
theorem segmentCrossingWord_image (ν : C.walls → V →ₗ[ℝ] ℝ) (a : x ⟶ y) :
    (C.image e).segmentCrossingWord
        (fun Q => (ν ((C.wallImageEquiv e).symm Q)).comp
          e.toAffineEquiv.linear.symm.toLinearMap)
        ((C.imagePrefunctor e).map a) =
      FreeGroup.map (C.wallImageEquiv e) (C.segmentCrossingWord ν a) := by
  simp only [segmentCrossingWord_def, orderedCrossings_image,
    ← List.map_reverse, List.map_map, Function.comp_def, crossingLetter_image,
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

/-- Integral affine coordinate changes transport signed words by their wall bijection. -/
@[simp]
theorem crossingWord_image (p : AdmissiblePLPath x y)
    (e : Mei.Toric.IntegralAffineEquiv h h') (ν : C.walls → V →ₗ[ℝ] ℝ) :
    ((C.imagePrefunctor e).mapPath p).crossingWord
        (fun Q => (ν ((C.wallImageEquiv e).symm Q)).comp
          e.toAffineEquiv.linear.symm.toLinearMap) =
      FreeGroup.map (C.wallImageEquiv e) (p.crossingWord ν) := by
  induction p with
  | nil => simp only [Prefunctor.mapPath_nil, crossingWord_nil, map_one]
  | cons p a ih =>
    simp only [Prefunctor.mapPath_cons, crossingWord_cons,
      Mei.FinitePolyhedralComplex.segmentCrossingWord_image, ih, map_mul]

end Quiver.Path
