/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Equivalence
public import Mei.Geometry.Convex.PolyhedralComplex.AffineTransport

/-!
# Affine transport of finite wall diagrams

Transport wall labels to the image complex and normal functionals by the inverse
linear part. The product along the transported path equals the original path
product, including for translations and orientation-reversing equivalences.
Affine images preserve and reflect equivalence and consistency. Identity,
composition and inverse transport hold up to diagram equivalence, so coordinate
changes act on diagrams independently of their polyhedral presentation.
The construction uses the wall bijection and crossing-word transport together
with Mathlib's `FreeGroup.lift_unique`. Inverse path transport compares arbitrary
test paths in image complexes by their ambient vertex lists.
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

/-- Pulling an arbitrary image path back recovers its product in the original diagram. -/
@[simp]
theorem pathProduct_pathPreimage
    {x' y' : WallComplement (fun Q : (C.image e).walls => (Q : Set V'))}
    (q : AdmissiblePLPath x' y') :
    D.pathProduct ((C.pathPreimage e).mapPath q) = (D.image e).pathProduct q := by
  rw [← D.pathProduct_image e ((C.pathPreimage e).mapPath q)]
  apply pathProduct_eq_of_vertices_eq
  rw [C.vertices_pathImage, C.vertices_pathPreimage, List.map_map]
  simp [Function.comp_def]

variable {C' : FinitePolyhedralComplex h}
  {D : FiniteWallDiagram C H} {E : FiniteWallDiagram C' H}

/-- Affine images preserve equivalence, even for diagrams on different complexes. -/
theorem Equivalent.image (hDE : D.Equivalent E) (e : Toric.IntegralAffineEquiv h h') :
    (D.image e).Equivalent (E.image e) := by
  apply (equivalent_def _ _).mpr
  intro x y x' y' p q hpq
  rw [← D.pathProduct_pathPreimage e p, ← E.pathProduct_pathPreimage e q]
  apply (equivalent_def _ _).mp hDE
  rw [C.vertices_pathPreimage, C'.vertices_pathPreimage, hpq]

/-- Affine images preserve and reflect equivalence. -/
@[simp]
theorem equivalent_image_iff (D : FiniteWallDiagram C H) (E : FiniteWallDiagram C' H)
    (e : Toric.IntegralAffineEquiv h h') :
    (D.image e).Equivalent (E.image e) ↔ D.Equivalent E := by
  constructor
  · intro hDE
    apply (equivalent_def _ _).mpr
    intro x y x' y' p q hpq
    rw [← D.pathProduct_image e p, ← E.pathProduct_image e q]
    apply (equivalent_def _ _).mp hDE
    rw [C.vertices_pathImage, C'.vertices_pathImage, hpq]
  · exact fun hDE => hDE.image e

/-- Affine images preserve and reflect endpoint independence. -/
@[simp]
theorem consistent_image_iff (D : FiniteWallDiagram C H) (e : Toric.IntegralAffineEquiv h h') :
    (D.image e).Consistent ↔ D.Consistent := by
  rw [consistent_def, consistent_def]
  constructor
  · intro hc x y p q
    rw [← D.pathProduct_image e p, ← D.pathProduct_image e q]
    exact hc _ _
  · intro hc x y p q
    rw [← D.pathProduct_pathPreimage e p, ← D.pathProduct_pathPreimage e q]
    exact hc _ _

/-- Transport by the identity is equivalent to the original diagram. -/
theorem image_refl_equivalent (D : FiniteWallDiagram C H) :
    (D.image (Toric.IntegralAffineEquiv.refl h)).Equivalent D := by
  apply (equivalent_def _ _).mpr
  intro x y x' y' p q hpq
  rw [← D.pathProduct_image (Toric.IntegralAffineEquiv.refl h) q]
  apply pathProduct_eq_of_vertices_eq
  rw [C.vertices_pathImage]
  simpa using hpq

variable {N'' V'' : Type*} [AddCommGroup N'']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {i'' : N'' →+ V''} {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- Successive coordinate changes agree with their composite up to equivalence. -/
theorem image_trans_equivalent (D : FiniteWallDiagram C H)
    (e : Toric.IntegralAffineEquiv h h') (f : Toric.IntegralAffineEquiv h' h'') :
    ((D.image e).image f).Equivalent (D.image (e.trans f)) := by
  apply (equivalent_def _ _).mpr
  intro x y x' y' p q hpq
  rw [← (D.image e).pathProduct_pathPreimage f p,
    ← D.pathProduct_pathPreimage e _, ← D.pathProduct_pathPreimage (e.trans f) q]
  apply D.pathProduct_eq_of_vertices_eq
  rw [C.vertices_pathPreimage, (C.image e).vertices_pathPreimage,
    C.vertices_pathPreimage, List.map_map, hpq]
  apply List.map_congr_left
  intro a _
  apply (e.toAffineEquiv.trans f.toAffineEquiv).injective
  simp

/-- A coordinate change followed by its inverse recovers the diagram up to equivalence. -/
theorem image_symm_equivalent (D : FiniteWallDiagram C H)
    (e : Toric.IntegralAffineEquiv h h') :
    ((D.image e).image e.symm).Equivalent D := by
  have he := D.image_trans_equivalent e e.symm
  rw [Toric.IntegralAffineEquiv.self_trans_symm] at he
  exact he.trans (D.image_refl_equivalent)

end Mei.FiniteWallDiagram
