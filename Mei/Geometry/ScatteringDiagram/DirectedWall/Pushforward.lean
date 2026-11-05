/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Affine.Span
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Hom
public import Mei.Topology.Algebra.ContinuousAffineEquiv

/-!
# Pushing directed walls forward along degree-changing maps

A `DirectedWall.Pushforward` packages the data needed to push directed walls along a
graded Lie homomorphism whose positive degree map `T` may change the degree lattice,
merge degrees and carry its own cutoff modulus:

* a graded Lie homomorphism `f` over `T`;
* a reindexing of supported rays, with every actual degree `n` on a ray `w` sent to an
  actual degree on the target ray. Thus the image of the primitive generator is a
  positive multiple `T(w) = b • w'` of the target generator whenever the target degree
  group is torsion free; with a free target it is `SupportedRay.map`;
* a map of integral normals together with a continuous affine equivalence `A` of the
  spatial supports. The real normal of `S(ν)` pulls back along the linear part of `A`
  to a positive rational multiple `r • ν` of the original real normal, and `A` carries
  the geometric image of every positive degree `n` to that of `T n`;
* preservation of homogeneous wall spaces: the image of a wall element of degree `n` and
  normal `ν` is a wall element of degree `T n` and normal `S(ν)`.

Two such data agree when their degree maps, ray maps, normal maps and spatial maps agree and
their Lie maps agree pointwise (`DirectedWall.Pushforward.ext`).

The positive rational scalar is what a tropical pairing provides: for the rational
inverse dual of a finite-index embedding, `S(ν)` is only a rational multiple of a
primitive integral normal. Positivity keeps the crossing signs, so path products are
unchanged. Rationality of the scalar makes the inverse spatial map rational, hence
supports remain rational-normal polyhedra. The spatial map must be an equivalence, since
supports of directed walls have codimension one on both sides.

Pushforward retains the support's image, sends the label through
`GradedLieHom.completedMap` and preserves incomingness and outgoingness. The fixed-degree
coefficient maps `DirectedWall.map` and the coordinate changes `DirectedWall.image` are
special cases. The mathematical setting is Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5),
Example 2.1(i) and Definition 2.2.
-/

public section

noncomputable section

namespace Mei

open Set

universe u

variable {Γ Γ' Γ'' Λ Λ' Λ'' R V V' V'' : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'} {d'' : PositiveDegrees Γ''}
  {i : Λ →+ V} {i' : Λ' →+ V'} {i'' : Λ'' →+ V''}

namespace DirectedWall

variable (d d') (h : TauCeti.Toric.IsIntegralLattice i)
  (h' : TauCeti.Toric.IsIntegralLattice i')
  (H : DirectedWallSpaces ρ ℒ) (H' : DirectedWallSpaces ρ' ℳ)

/-- Data for pushing directed walls along a degree-changing graded Lie homomorphism
with a compatible spatial affine equivalence. -/
structure Pushforward where
  /-- The positive degree map, including its cutoff modulus. -/
  degreeMap : PositiveDegreeMap d d'
  /-- The graded Lie homomorphism carrying the labels. -/
  lieHom : GradedLieHom degreeMap ℒ ℳ
  /-- The reindexing of supported rays. -/
  rayMap : SupportedRay d → SupportedRay d'
  /-- Actual degrees on a ray map to actual degrees on its image ray. -/
  mem_rayDegrees_rayMap :
    ∀ w : SupportedRay d, ∀ n ∈ w.rayDegrees, degreeMap n ∈ (rayMap w).rayDegrees
  /-- The map of integral normals. -/
  normalMap : (Λ →+ ℤ) → (Λ' →+ ℤ)
  /-- Homogeneous wall spaces map to the wall spaces of the image degree and normal. -/
  wall_mem : ∀ n ∈ d.monoid, ∀ m, ∀ x ∈ H.wall n m,
    lieHom x ∈ H'.wall (degreeMap n) (normalMap m)
  /-- The spatial affine equivalence. -/
  spatialMap : V ≃ᴬ[ℝ] V'
  /-- The spatial map carries geometric positive degrees to their images. -/
  map_direction : ∀ n ∈ d.monoid,
    i' (ρ' (degreeMap n)) = spatialMap.toAffineEquiv.linear (i (ρ n))
  /-- Image normals pull back to positive rational multiples of the original normals. -/
  realCharacter_normalMap : ∀ m : Λ →+ ℤ, ∃ r : ℚ, 0 < r ∧
    (h'.realCharacter (normalMap m)).comp spatialMap.toAffineEquiv.linear.toLinearMap =
      (r : ℝ) • h.realCharacter m

variable {d d' h h' H H'} {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H'' : DirectedWallSpaces ρ'' ℋ}

namespace Pushforward

/-- Pushforward data are determined by the degree map, the values of the Lie map, the ray map,
the normal map and the spatial map. -/
@[ext]
theorem ext {P Q : Pushforward d d' h h' H H'} (hdeg : P.degreeMap = Q.degreeMap)
    (hlie : ∀ x, P.lieHom x = Q.lieHom x) (hray : P.rayMap = Q.rayMap)
    (hnormal : P.normalMap = Q.normalMap) (hspatial : P.spatialMap = Q.spatialMap) :
    P = Q := by
  cases P
  cases Q
  cases hdeg
  cases hray
  cases hnormal
  cases hspatial
  congr
  exact GradedLieHom.ext hlie

variable (P : Pushforward d d' h h' H H')

/-- The real image normal, evaluated on a transported vector, is a positive rational
multiple of the original real normal. -/
theorem exists_realCharacter_normalMap_apply (m : Λ →+ ℤ) : ∃ r : ℚ, 0 < r ∧
    ∀ v : V, h'.realCharacter (P.normalMap m) (P.spatialMap.toAffineEquiv.linear v) =
      r * h.realCharacter m v := by
  obtain ⟨r, hr, he⟩ := P.realCharacter_normalMap m
  exact ⟨r, hr, fun v => by simpa using LinearMap.congr_fun he v⟩

/-- The integral image normal vanishes on the image of a positive degree exactly when the
original normal vanishes on that degree. -/
theorem normalMap_apply_degreeMap_eq_zero_iff (m : Λ →+ ℤ) {n : Γ} (hn : n ∈ d.monoid) :
    P.normalMap m (ρ' (P.degreeMap n)) = 0 ↔ m (ρ n) = 0 := by
  obtain ⟨r, hr, he⟩ := P.exists_realCharacter_normalMap_apply m
  have hv := he (i (ρ n))
  rw [← P.map_direction n hn, h'.realCharacter_apply, h.realCharacter_apply] at hv
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  constructor
  · intro hz
    rw [hz, Int.cast_zero, eq_comm, mul_eq_zero] at hv
    exact_mod_cast hv.resolve_left hr'
  · intro hz
    rw [hz, Int.cast_zero, mul_zero] at hv
    exact_mod_cast hv

/-- Nonzero normals have nonzero images. -/
theorem normalMap_ne_zero {m : Λ →+ ℤ} (hm : m ≠ 0) : P.normalMap m ≠ 0 := by
  intro hz
  apply hm
  obtain ⟨r, hr, he⟩ := P.exists_realCharacter_normalMap_apply m
  ext n
  have hv := he (i n)
  rw [hz, map_zero, LinearMap.zero_apply, h.realCharacter_apply, eq_comm,
    mul_eq_zero] at hv
  exact_mod_cast hv.resolve_left (by exact_mod_cast hr.ne')

/-- The inverse spatial map pulls rational functionals back to rational functionals,
because the normal comparison scalars are rational. -/
theorem isRationalLinearMap_symm :
    Toric.IsRationalLinearMap h' h
      P.spatialMap.symm.toContinuousAffineMap.toAffineMap.linear := by
  rw [Toric.isRationalLinearMap_iff]
  intro f hf
  obtain ⟨q, m, rfl⟩ := (Toric.IsRationalFunctional.iff_exists_character).mp hf
  rw [Toric.IsRationalFunctional.iff_exists_character]
  obtain ⟨r, hr, he⟩ := P.exists_realCharacter_normalMap_apply m.toAddMonoidHom
  refine ⟨q * r⁻¹, (P.normalMap m.toAddMonoidHom).toIntLinearMap, ?_⟩
  ext v
  have hv := he (P.spatialMap.symm.toAffineEquiv.linear v)
  have hs : P.spatialMap.toAffineEquiv.linear (P.spatialMap.symm.toAffineEquiv.linear v) = v := by
    rw [ContinuousAffineEquiv.toAffineEquiv_symm, AffineEquiv.linear_symm,
      LinearEquiv.apply_symm_apply]
  rw [hs] at hv
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hm : (P.normalMap m.toAddMonoidHom).toIntLinearMap.toAddMonoidHom =
      P.normalMap m.toAddMonoidHom :=
    AddMonoidHom.ext fun _ => by simp
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, Rat.cast_mul,
    Rat.cast_inv, ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
    AffineEquiv.linear_toAffineMap, LinearEquiv.coe_coe, hm, hv]
  field_simp

/-- Rational-normal polyhedra have rational-normal images. -/
theorem isRationalNormalPolyhedron_image {S : Set V} (hS : IsRationalNormalPolyhedron h S) :
    IsRationalNormalPolyhedron h' (P.spatialMap '' S) := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hS
  refine isRationalNormalPolyhedron_iff.mpr
    ⟨Q.preimage _ P.isRationalLinearMap_symm, ?_⟩
  rw [RationalAffinePolyhedron.carrier_preimage]
  ext y
  simp [ContinuousAffineEquiv.coe_toContinuousAffineMap, Set.mem_image,
    eq_comm]

/-- The image of an affine span direction is cut out by the image normal. -/
theorem direction_affineSpan_image {S : Set V} {m : Λ →+ ℤ}
    (hS : (affineSpan ℝ S).direction = LinearMap.ker (h.realCharacter m)) :
    (affineSpan ℝ (P.spatialMap '' S)).direction =
      LinearMap.ker (h'.realCharacter (P.normalMap m)) := by
  obtain ⟨r, hr, he⟩ := P.realCharacter_normalMap m
  have hd : (affineSpan ℝ (P.spatialMap '' S)).direction =
      (affineSpan ℝ S).direction.map P.spatialMap.toAffineEquiv.linear.toLinearMap := by
    have hA := P.spatialMap.toAffineEquiv.toAffineMap.direction_affineSpan_image S
    rwa [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_toAffineMap,
      ContinuousAffineEquiv.coe_coe] at hA
  rw [hd, hS, Submodule.map_equiv_eq_comap_symm]
  ext v
  have hv := LinearMap.congr_fun he (P.spatialMap.toAffineEquiv.linear.symm v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.smul_apply, smul_eq_mul] at hv
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_coe]
  rw [hv]
  simp [hr']

/-- Compose pushforward data, applying `P` first. Degree maps, cutoff moduli, ray and
normal maps compose, spatial maps compose and the normal scalars multiply. -/
def comp (Q : Pushforward d' d'' h' h'' H' H'') (P : Pushforward d d' h h' H H') :
    Pushforward d d'' h h'' H H'' where
  degreeMap := Q.degreeMap.comp P.degreeMap
  lieHom := Q.lieHom.comp P.lieHom
  rayMap := Q.rayMap ∘ P.rayMap
  mem_rayDegrees_rayMap w n hn := by
    simpa only [PositiveDegreeMap.comp_apply, Function.comp_apply] using
      Q.mem_rayDegrees_rayMap _ _ (P.mem_rayDegrees_rayMap w n hn)
  normalMap := Q.normalMap ∘ P.normalMap
  wall_mem n hn m x hx := by
    simpa only [GradedLieHom.comp_apply, PositiveDegreeMap.comp_apply, Function.comp_apply] using
      Q.wall_mem _ (P.degreeMap.map_mem hn) _ _ (P.wall_mem n hn m x hx)
  spatialMap := P.spatialMap.trans Q.spatialMap
  map_direction n hn := by
    rw [PositiveDegreeMap.comp_apply, Q.map_direction _ (P.degreeMap.map_mem hn),
      P.map_direction n hn, ContinuousAffineEquiv.linear_trans_apply]
  realCharacter_normalMap m := by
    obtain ⟨r, hr, hP⟩ := P.exists_realCharacter_normalMap_apply m
    obtain ⟨s, hs, hQ⟩ := Q.exists_realCharacter_normalMap_apply (P.normalMap m)
    refine ⟨s * r, mul_pos hs hr, ?_⟩
    ext v
    simp only [Function.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousAffineEquiv.linear_trans_apply, LinearMap.smul_apply, smul_eq_mul, Rat.cast_mul,
      hQ, hP]
    ring

/-- The ray map of composite data is the composite of the ray maps. -/
@[simp]
theorem comp_rayMap (Q : Pushforward d' d'' h' h'' H' H'') (P : Pushforward d d' h h' H H')
    (w : SupportedRay d) : (Q.comp P).rayMap w = Q.rayMap (P.rayMap w) := (rfl)

/-- The normal map of composite data is the composite of the normal maps. -/
@[simp]
theorem comp_normalMap (Q : Pushforward d' d'' h' h'' H' H'') (P : Pushforward d d' h h' H H')
    (m : Λ →+ ℤ) : (Q.comp P).normalMap m = Q.normalMap (P.normalMap m) := (rfl)

/-- The spatial map of composite data is the composite of the spatial maps. -/
@[simp]
theorem comp_spatialMap (Q : Pushforward d' d'' h' h'' H' H'') (P : Pushforward d d' h h' H H') :
    (Q.comp P).spatialMap = P.spatialMap.trans Q.spatialMap := (rfl)

end Pushforward

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]

variable (W : DirectedWall (d := d) h H) (P : Pushforward d d' h h' H H')

/-- Push a directed wall forward: the support moves by the spatial map, the normal and
ray are reindexed, and the label is sent through the completed group map. -/
def pushforward : DirectedWall (d := d') h' H' where
  normal := P.normalMap W.normal
  normal_ne_zero := P.normalMap_ne_zero W.normal_ne_zero
  ray := P.rayMap W.ray
  normal_direction := by
    obtain ⟨n, hn⟩ := W.ray.rayDegrees_nonempty
    obtain ⟨hnP, a, ha, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
    obtain ⟨-, c, hc, hTc⟩ :=
      SupportedRay.mem_rayDegrees.mp (P.mem_rayDegrees_rayMap W.ray _ hn)
    have hz := (P.normalMap_apply_degreeMap_eq_zero_iff W.normal hnP).mpr (by
      rw [map_zsmul, map_zsmul, W.normal_direction, smul_zero])
    rw [hTc, map_zsmul, map_zsmul, smul_eq_mul, mul_eq_zero] at hz
    exact hz.resolve_left hc.ne'
  support := P.spatialMap '' W.support
  support_nonempty := W.support_nonempty.image _
  rational_support := P.isRationalNormalPolyhedron_image W.rational_support
  direction_support := P.direction_affineSpan_image W.direction_support
  label := P.lieHom.completedMap W.label
  label_mem := P.lieHom.completedMap_mem_wallGroup (P.mem_rayDegrees_rayMap W.ray)
    (fun n hn x hx => P.wall_mem n (SupportedRay.mem_rayDegrees.mp hn).1 W.normal x hx)
    W.label_mem

/-- The pushed normal is the image normal. -/
@[simp]
theorem pushforward_normal : (W.pushforward P).normal = P.normalMap W.normal := (rfl)

/-- The pushed ray is the reindexed ray. -/
@[simp]
theorem pushforward_ray : (W.pushforward P).ray = P.rayMap W.ray := (rfl)

/-- The pushed support is the spatial image of the support. -/
@[simp]
theorem pushforward_support : (W.pushforward P).support = P.spatialMap '' W.support := (rfl)

/-- The pushed label is the completed image of the label. -/
@[simp]
theorem pushforward_label : (W.pushforward P).label = P.lieHom.completedMap W.label := (rfl)

/-- With a free target degree group, the ray reindexing is forced to be the canonical
transport of supported rays: the image of the primitive generator is a positive multiple
of the target primitive generator. -/
theorem pushforward_ray_eq_map [Module.Free ℤ Γ'] :
    (W.pushforward P).ray = W.ray.map P.degreeMap.toAddMonoidHom
      (fun _ hn => P.degreeMap.map_mem hn) (fun _ hn h0 => P.degreeMap.map_ne_zero hn h0) := by
  obtain ⟨n, hn⟩ := W.ray.rayDegrees_nonempty
  exact ((W.ray.map_eq_iff_exists_mem_rayDegrees _ _ _ _).mpr
    ⟨n, hn, P.mem_rayDegrees_rayMap W.ray n hn⟩).symm

/-- The image of an actual degree of the wall is an actual degree of the pushed wall. -/
theorem degreeMap_mem_pushforward_rayDegrees {n : Γ} (hn : n ∈ W.ray.rayDegrees) :
    P.degreeMap n ∈ (W.pushforward P).ray.rayDegrees :=
  P.mem_rayDegrees_rayMap W.ray n hn

/-- The geometric direction of the pushed wall is a positive multiple of the spatial image
of the original geometric direction, including when it is zero. -/
theorem exists_geometricDirection_pushforward : ∃ t : ℝ, 0 < t ∧
    i' (ρ' (W.pushforward P).ray.generator) =
      t • P.spatialMap.toAffineEquiv.linear (i (ρ W.ray.generator)) := by
  obtain ⟨n, hn⟩ := W.ray.rayDegrees_nonempty
  obtain ⟨hnP, a, ha, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
  obtain ⟨-, c, hc, hTc⟩ :=
    SupportedRay.mem_rayDegrees.mp (P.mem_rayDegrees_rayMap W.ray _ hn)
  have hd := P.map_direction _ hnP
  rw [hTc] at hd
  simp only [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ] at hd
  refine ⟨(a : ℝ) / c, div_pos (by exact_mod_cast ha) (by exact_mod_cast hc), ?_⟩
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [pushforward_ray, div_eq_inv_mul, mul_smul, ← map_smul, ← hd, smul_smul,
    inv_mul_cancel₀ hc', one_smul]

/-- The spatial velocity of the pushed wall is a positive multiple of the spatial image of
the original velocity. -/
theorem exists_direction_pushforward : ∃ t : ℝ, 0 < t ∧
    (W.pushforward P).direction = t • P.spatialMap.toAffineEquiv.linear W.direction := by
  obtain ⟨t, ht, he⟩ := W.exists_geometricDirection_pushforward P
  exact ⟨t, ht, by rw [direction_def, he, direction_def, map_neg, smul_neg]⟩

/-- Pushforward preserves and reflects incomingness. -/
@[simp]
theorem incoming_pushforward_iff : (W.pushforward P).Incoming ↔ W.Incoming := by
  obtain ⟨n, hn⟩ := W.ray.rayDegrees_nonempty
  rw [(W.pushforward P).incoming_iff_of_mem_rayDegrees
      (W.degreeMap_mem_pushforward_rayDegrees P hn),
    W.incoming_iff_of_mem_rayDegrees hn,
    P.map_direction n (SupportedRay.mem_rayDegrees.mp hn).1, pushforward_support]
  simpa only [ContinuousAffineEquiv.coe_coe] using
    P.spatialMap.toAffineEquiv.linear_mem_recessionCone_image W.support (i (ρ n))

/-- Pushforward preserves and reflects outgoingness. -/
@[simp]
theorem outgoing_pushforward_iff : (W.pushforward P).Outgoing ↔ W.Outgoing := by
  have hi := W.incoming_pushforward_iff P
  rw [incoming_iff, incoming_iff, ← mem_recessionCone, ← mem_recessionCone] at hi
  rw [outgoing_iff, outgoing_iff]
  exact not_congr hi

/-- Successive pushforwards agree with the pushforward along the composite data. -/
@[simp]
theorem pushforward_pushforward (Q : Pushforward d' d'' h' h'' H' H'') :
    (W.pushforward P).pushforward Q = W.pushforward (Q.comp P) := by
  apply DirectedWall.ext
  · simp only [pushforward_normal, Pushforward.comp_normalMap]
  · simp only [pushforward_ray, Pushforward.comp_rayMap]
  · simp only [pushforward_support, Set.image_image, Pushforward.comp_spatialMap,
      ContinuousAffineEquiv.coe_trans, Function.comp_def]
  · simp only [pushforward_label]
    exact (DFunLike.congr_fun (GradedLieHom.completedMap_comp Q.lieHom P.lieHom) _).symm

end DirectedWall
end Mei
