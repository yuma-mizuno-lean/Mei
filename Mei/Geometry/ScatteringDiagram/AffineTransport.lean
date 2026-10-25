/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Finite
public import Mei.Geometry.Convex.PolyhedralComplex.AffineTransport

/-!
# Affine transport of finite wall diagrams

Transport wall labels to the image complex and normal functionals by the inverse
linear part. The product along the transported path equals the original path
product, including for translations and orientation-reversing equivalences.
The construction uses the wall bijection and crossing-word transport together
with Mathlib's `FreeGroup.lift_unique`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N N' V V' H : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {C : FinitePolyhedralComplex h}
  (D : FiniteWallDiagram C H) (e : Mei.Toric.IntegralAffineEquiv h h')

/-- Transport labels by the wall bijection and normals by the inverse linear part. -/
def image : FiniteWallDiagram (C.image e) H where
  normal Q := (D.normal ((C.wallImageEquiv e).symm Q)).comp
    e.toAffineEquiv.linear.symm.toLinearMap
  ker_normal Q := by
    obtain ⟨P, rfl⟩ := (C.wallImageEquiv e).surjective Q
    rw [Equiv.symm_apply_apply, LinearMap.ker_comp, D.ker_normal, C.wallImageEquiv_coe]
    have hd : (affineSpan ℝ (e '' (P : Set V))).direction =
        ((affineSpan ℝ (P : Set V)).direction).map e.toAffineEquiv.linear.toLinearMap := by
      simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe] using
        e.toAffineEquiv.toAffineMap.direction_affineSpan_image (P : Set V)
    rw [hd, Submodule.map_equiv_eq_comap_symm]
  label Q := D.label ((C.wallImageEquiv e).symm Q)

@[simp]
theorem image_normal (Q : (C.image e).walls) :
    (D.image e).normal Q = (D.normal ((C.wallImageEquiv e).symm Q)).comp
      e.toAffineEquiv.linear.symm.toLinearMap := (rfl)

@[simp]
theorem image_label (Q : (C.image e).walls) :
    (D.image e).label Q = D.label ((C.wallImageEquiv e).symm Q) := (rfl)

/-- Pulling a transported normal back by the forward linear map recovers it. -/
theorem image_normal_comp (P : C.walls) :
    ((D.image e).normal (C.wallImageEquiv e P)).comp e.toAffineEquiv.linear.toLinearMap =
      D.normal P := by
  ext v
  simp

variable [Group H]
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Transporting a path and its labelled diagram preserves the entire path product. -/
@[simp]
theorem pathProduct_image (p : AdmissiblePLPath x y) :
    (D.image e).pathProduct ((C.pathImage e).mapPath p) = D.pathProduct p := by
  rw [pathProduct_def, p.crossingWord_pathImage e D.normal (D.image e).normal
    (D.image_normal_comp e), pathProduct_def]
  exact FreeGroup.lift_unique
    ((FreeGroup.lift (D.image e).label).comp (FreeGroup.map (C.wallImageEquiv e)))
    (by simp)

end Mei.FiniteWallDiagram
