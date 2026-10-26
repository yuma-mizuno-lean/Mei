/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Span
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.CoordinateChange

/-!
# Affine transport of directed walls

An integral affine equivalence of the spatial lattices, together with compatible
coordinate changes of the degree and Lie data, transports directed affine walls.
Supports move by the affine map, normals by the inverse tangent map, primitive
rays by the degree isomorphism and labels by the completed group isomorphism.
The linear part transports the spatial velocity and preserves incomingness and
outgoingness. Translation vectors and changes of the positive degree function
are allowed, including walls with zero spatial velocity.

The construction combines `Mei.DirectedWallSpaces.CoordinateChange` and its
`completedMap_mem_wallGroup_iff` with the existing integral affine image of
rational-normal polyhedra. Recession directions are transported using
`AffineEquiv.linear_mem_recessionCone_image`. No additional wall carrier or
completion is introduced.
-/

public section

noncomputable section

namespace Mei.DirectedWall

open Set

universe u

variable {Γ Γ' Γ'' Λ Λ' Λ'' R V V' V'' : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'} {d'' : PositiveDegrees Γ''}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
  {i : Λ →+ V} {i' : Λ' →+ V'} {i'' : Λ'' →+ V''}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {H'' : DirectedWallSpaces ρ'' ℋ}
  (W : DirectedWall (d := d) h H)
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- Transport all directed wall data through compatible spatial and algebraic
coordinate changes. The two positive degree functions need not agree. -/
def image : DirectedWall (d := d') h' H' where
  normal := W.normal.comp E.tangentEquiv.symm
  normal_ne_zero := by
    intro hz
    apply W.normal_ne_zero
    ext n
    have hn := DFunLike.congr_fun hz (E.tangentEquiv n)
    simpa using hn
  ray := E.rayEquiv W.ray
  normal_direction := by
    simp [E.rayEquiv_generator, ← E.map_direction, W.normal_direction]
  support := e '' W.support
  support_nonempty := W.support_nonempty.image e
  rational_support := W.rational_support.image e
  direction_support := by
    have hn : h'.realCharacter (W.normal.comp E.tangentEquiv.symm) =
        (h.realCharacter W.normal).comp e.toAffineEquiv.linear.symm.toLinearMap := by
      rw [hE]
      simpa only [Toric.IntegralAffineEquiv.symm_latticeEquiv,
        Toric.IntegralAffineEquiv.symm_toAffineEquiv, AffineEquiv.linear_symm] using
        h'.realCharacter_comp h e.symm.latticeEquiv
          e.symm.toAffineEquiv.linear.toLinearMap e.symm.map_lattice W.normal
    have hd : (affineSpan ℝ (e '' W.support)).direction =
        (affineSpan ℝ W.support).direction.map e.toAffineEquiv.linear.toLinearMap := by
      simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe] using
        e.toAffineEquiv.toAffineMap.direction_affineSpan_image W.support
    rw [hd, W.direction_support, hn, LinearMap.ker_comp,
      Submodule.map_equiv_eq_comap_symm]
  label := E.completedEquiv W.label
  label_mem := by
    rw [E.completedEquiv_apply]
    exact (E.completedMap_mem_wallGroup_iff W.ray W.normal W.label).mpr W.label_mem

/-- The transported integral normal is the inverse-dual normal. -/
@[simp]
theorem image_normal :
    (W.image e E hE).normal = W.normal.comp (E.tangentEquiv.symm : Λ' →+ Λ) := (rfl)

/-- The transported degree ray uses the degree isomorphism, not the spatial map. -/
@[simp]
theorem image_ray : (W.image e E hE).ray = E.rayEquiv W.ray := (rfl)

/-- The transported support is the exact affine image of the original support. -/
@[simp]
theorem image_support : (W.image e E hE).support = e '' W.support := (rfl)

/-- The transported label is the existing completed coordinate comparison. -/
@[simp]
theorem image_label : (W.image e E hE).label = E.completedEquiv W.label := (rfl)

/-- Evaluating the transported real normal on a transported vector preserves its value. -/
theorem realCharacter_image_normal (v : V) :
    h'.realCharacter (W.image e E hE).normal (e.toAffineEquiv.linear v) =
      h.realCharacter W.normal v := by
  rw [image_normal, hE]
  have hn := h'.realCharacter_comp h e.symm.latticeEquiv
    e.symm.toAffineEquiv.linear.toLinearMap e.symm.map_lattice W.normal
  simp only [Toric.IntegralAffineEquiv.symm_latticeEquiv,
    Toric.IntegralAffineEquiv.symm_toAffineEquiv, AffineEquiv.linear_symm] at hn
  rw [hn]
  simp

/-- The geometric degree direction transforms by the linear part, including when zero. -/
theorem geometricDirection_image :
    i' (ρ' (W.image e E hE).ray.generator) =
      e.toAffineEquiv.linear (i (ρ W.ray.generator)) := by
  rw [image_ray, E.rayEquiv_generator, ← E.map_direction, hE, e.map_lattice]

/-- Spatial velocities transform by the linear part of the affine equivalence. -/
@[simp]
theorem direction_image : (W.image e E hE).direction = e.toAffineEquiv.linear W.direction := by
  rw [direction_def, geometricDirection_image, direction_def, map_neg]

/-- Incomingness is preserved and reflected by affine coordinate changes. -/
@[simp]
theorem incoming_image_iff : (W.image e E hE).Incoming ↔ W.Incoming := by
  rw [incoming_iff, ← mem_recessionCone, geometricDirection_image, image_support,
    e.toAffineEquiv.linear_mem_recessionCone_image, mem_recessionCone, ← incoming_iff]

/-- Outgoingness is preserved and reflected by affine coordinate changes. -/
@[simp]
theorem outgoing_image_iff : (W.image e E hE).Outgoing ↔ W.Outgoing := by
  rw [outgoing_iff, incoming_image_iff, outgoing_iff]

/-- Identity coordinate changes leave every wall datum unchanged. -/
@[simp]
theorem image_refl :
    W.image (Toric.IntegralAffineEquiv.refl h)
      (DirectedWallSpaces.CoordinateChange.refl H) (by simp) = W := by
  apply DirectedWall.ext
  · ext n
    simp
  · simp
  · simp [Toric.IntegralAffineEquiv.refl_toAffineEquiv]
  · simp

/-- Transporting first by one coordinate change and then another agrees with
transport by their composite. -/
theorem image_image
    (f : Toric.IntegralAffineEquiv h' h'')
    (F : DirectedWallSpaces.CoordinateChange (d := d') (e := d'') H' H'')
    (hF : F.tangentEquiv = f.latticeEquiv) :
    (W.image e E hE).image f F hF =
      W.image (e.trans f) (E.trans F) (by simp [hE, hF]) := by
  apply DirectedWall.ext
  · ext n
    simp
  · simp
  · simp [Set.image_image, Toric.IntegralAffineEquiv.trans_toAffineEquiv]
  · simp

/-- Applying the inverse spatial and algebraic coordinate changes recovers the wall. -/
@[simp]
theorem image_symm_image :
    (W.image e E hE).image e.symm E.symm (by simp [hE]) = W := by
  rw [image_image]
  simp

omit W in
/-- Directed wall transport is an equivalence of the existing wall carriers. -/
def imageEquiv : DirectedWall (d := d) h H ≃ DirectedWall (d := d') h' H' where
  toFun W := W.image e E hE
  invFun W := W.image e.symm E.symm (by simp [hE])
  left_inv W := W.image_symm_image e E hE
  right_inv W := by
    have he := W.image_symm_image e.symm E.symm (by simp [hE])
    simpa using he

/-- The wall equivalence acts by affine image and the completed label comparison. -/
@[simp]
theorem imageEquiv_apply (W : DirectedWall (d := d) h H) :
    imageEquiv e E hE W = W.image e E hE := (rfl)

/-- The inverse wall equivalence uses the inverse coordinate changes. -/
@[simp]
theorem imageEquiv_symm_apply (W : DirectedWall (d := d') h' H') :
    (imageEquiv e E hE).symm W = W.image e.symm E.symm (by simp [hE]) := (rfl)

end Mei.DirectedWall
