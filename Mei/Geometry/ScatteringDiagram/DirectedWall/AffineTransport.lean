/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Map
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.WallSpace.CoordinateChange

/-!
# Affine transport of directed walls

An integral affine equivalence of the spatial lattices, together with compatible
coordinate changes of the degree and Lie data, transports directed affine walls.
Supports move by the affine map, normals by the inverse tangent map, primitive
rays by the degree isomorphism and labels by the completed group isomorphism.
The linear part transports the spatial velocity and preserves incomingness and
outgoingness. Translation vectors and changes of the positive degree function
are allowed, including walls with zero spatial velocity. This transport is the
pushforward along `DirectedWall.Pushforward.ofCoordinateChange`, whose normal
comparison scalars are all one.

The construction combines `TauCeti.DirectedWallSpaces.CoordinateChange` and its
`completedMap_mem_wallGroup_iff` with the existing integral affine image of
rational-normal polyhedra. Recession directions are transported using
`AffineEquiv.linear_mem_recessionCone_image`. No additional wall carrier or
completion is introduced.
-/

public section

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei

open Set

universe u

variable {Γ Γ' Γ'' Λ Λ' Λ'' R V V' V'' : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'} {d'' : PositiveDegrees Γ''}
  {i : Λ →+ V} {i' : Λ' →+ V'} {i'' : Λ'' →+ V''}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {H'' : DirectedWallSpaces ρ'' ℋ}

/-- Compatible spatial and algebraic coordinate changes pull real normals back
along the inverse linear map. -/
theorem _root_.TauCeti.DirectedWallSpaces.CoordinateChange.realCharacter_comp_tangentEquiv_symm
    (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
    (e : Toric.IntegralAffineEquiv h h') (hE : E.tangentEquiv = e.latticeEquiv)
    (m : Λ →+ ℤ) :
    h'.realCharacter (m.comp E.tangentEquiv.symm) =
      (h.realCharacter m).comp e.toAffineEquiv.linear.symm.toLinearMap := by
  rw [hE]
  simpa only [Toric.IntegralAffineEquiv.symm_latticeEquiv,
    Toric.IntegralAffineEquiv.symm_toAffineEquiv, AffineEquiv.linear_symm] using
    h'.realCharacter_comp h e.symm.latticeEquiv
      e.symm.toAffineEquiv.linear.toLinearMap e.symm.map_lattice m

/-- Compatible spatial and algebraic coordinate changes, with inverse-dual normals. -/
def DirectedWall.Pushforward.ofCoordinateChange (e : Toric.IntegralAffineEquiv h h')
    (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
    (hE : E.tangentEquiv = e.latticeEquiv) : DirectedWall.Pushforward d d' h h' H H' where
  degreeMap := E.degreeMap
  lieHom := E.gradedLieHom
  rayMap := E.rayEquiv
  mem_rayDegrees_rayMap w n hn := by
    rw [E.degreeMap_apply]
    exact (E.mem_rayDegrees_rayEquiv w n).mpr hn
  normalMap m := m.comp E.tangentEquiv.symm
  wall_mem n _ m x hx := by
    rw [E.gradedLieHom_apply, E.degreeMap_apply]
    exact (E.wall_mem_iff n m x).mpr hx
  spatialMap := e.toContinuousAffineEquiv
  map_direction n _ := ⟨1, one_pos, by
    rw [one_smul, Toric.IntegralAffineEquiv.toContinuousAffineEquiv_toAffineEquiv,
      E.degreeMap_apply, ← E.map_direction, hE, e.map_lattice]⟩
  realCharacter_normalMap m := ⟨1, one_pos, by
    rw [E.realCharacter_comp_tangentEquiv_symm e hE]
    ext v
    simp⟩

section ofCoordinateChange

variable (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- The degree map of a coordinate change is its degree isomorphism. -/
@[simp]
theorem DirectedWall.Pushforward.ofCoordinateChange_degreeMap :
    (Pushforward.ofCoordinateChange e E hE).degreeMap = E.degreeMap := (rfl)

/-- The Lie map of a coordinate change has the values of its graded Lie map. -/
@[simp]
theorem DirectedWall.Pushforward.ofCoordinateChange_lieHom_apply (x : L) :
    (Pushforward.ofCoordinateChange e E hE).lieHom x = E.gradedLieHom x := (rfl)

/-- The ray map of a coordinate change is its ray equivalence. -/
@[simp]
theorem DirectedWall.Pushforward.ofCoordinateChange_rayMap (w : SupportedRay d) :
    (Pushforward.ofCoordinateChange e E hE).rayMap w = E.rayEquiv w := (rfl)

/-- The normal map of a coordinate change is the inverse-dual map. -/
@[simp]
theorem DirectedWall.Pushforward.ofCoordinateChange_normalMap (m : Λ →+ ℤ) :
    (Pushforward.ofCoordinateChange e E hE).normalMap m =
      m.comp (E.tangentEquiv.symm : Λ' →+ Λ) := (rfl)

/-- The spatial map of a coordinate change is the integral affine equivalence. -/
@[simp]
theorem DirectedWall.Pushforward.ofCoordinateChange_spatialMap :
    (Pushforward.ofCoordinateChange e E hE).spatialMap = e.toContinuousAffineEquiv := (rfl)

end ofCoordinateChange

namespace DirectedWall

variable [Algebra ℚ R]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
  (W : DirectedWall (d := d) h H)
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- The Lie map of a coordinate change has the completed map of its graded Lie map. -/
@[simp]
theorem Pushforward.ofCoordinateChange_lieHom_completedMap :
    (Pushforward.ofCoordinateChange e E hE).lieHom.completedMap = E.gradedLieHom.completedMap :=
  (rfl)

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
    have hd : (affineSpan ℝ (e '' W.support)).direction =
        (affineSpan ℝ W.support).direction.map e.toAffineEquiv.linear.toLinearMap := by
      simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe] using
        e.toAffineEquiv.toAffineMap.direction_affineSpan_image W.support
    rw [hd, W.direction_support, E.realCharacter_comp_tangentEquiv_symm e hE,
      LinearMap.ker_comp, Submodule.map_equiv_eq_comap_symm]
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

/-- Coordinate changes of directed walls are pushforwards. -/
@[simp]
theorem pushforward_ofCoordinateChange :
    W.pushforward (Pushforward.ofCoordinateChange e E hE) = W.image e E hE := by
  apply DirectedWall.ext
  · rw [pushforward_normal, image_normal, Pushforward.ofCoordinateChange_normalMap]
  · rw [pushforward_ray, image_ray, Pushforward.ofCoordinateChange_rayMap]
  · rw [pushforward_support, image_support, Pushforward.ofCoordinateChange_spatialMap]
    ext
    simp
  · rw [pushforward_label, image_label, E.completedEquiv_apply,
      Pushforward.ofCoordinateChange_lieHom_completedMap]

/-- Evaluating the transported real normal on a transported vector preserves its value. -/
theorem realCharacter_image_normal (v : V) :
    h'.realCharacter (W.image e E hE).normal (e.toAffineEquiv.linear v) =
      h.realCharacter W.normal v := by
  simp [E.realCharacter_comp_tangentEquiv_symm e hE]

/-- A full affine hyperplane stays full under coordinate change; its offset also
records the translation of the origin. -/
theorem image_support_eq_hyperplane {a : ℝ}
    (ha : W.support = {x | h.realCharacter W.normal x = a}) :
    (W.image e E hE).support =
      {y | h'.realCharacter (W.image e E hE).normal y =
        a + h'.realCharacter (W.image e E hE).normal (e 0)} := by
  have hval (x : V) : h'.realCharacter (W.image e E hE).normal (e x) =
      h.realCharacter W.normal x + h'.realCharacter (W.image e E hE).normal (e 0) := by
    have hx := e.toAffineEquiv.map_vadd (0 : V) x
    simp only [vadd_eq_add, add_zero] at hx
    rw [hx, map_add, W.realCharacter_image_normal e E hE]
  rw [image_support, ha]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hval x).trans (congrArg (· + _) hx)
  · intro hy
    refine ⟨e.toAffineEquiv.symm y, ?_, e.toAffineEquiv.apply_symm_apply y⟩
    have hv := hval (e.toAffineEquiv.symm y)
    simp only [AffineEquiv.apply_symm_apply] at hv
    simp only [Set.mem_ofPred_eq] at hy ⊢
    linarith

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
  rw [← pushforward_ofCoordinateChange, incoming_pushforward_iff]

/-- Outgoingness is preserved and reflected by affine coordinate changes. -/
@[simp]
theorem outgoing_image_iff : (W.image e E hE).Outgoing ↔ W.Outgoing := by
  rw [← pushforward_ofCoordinateChange, outgoing_pushforward_iff]

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

end DirectedWall
end Mei
