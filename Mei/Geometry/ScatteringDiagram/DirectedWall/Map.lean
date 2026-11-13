/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Pushforward

/-!
# Fixed-degree coefficient maps of directed walls

A graded Lie homomorphism preserving homogeneous wall spaces maps directed wall
labels while retaining the normal, supported ray and affine support. Incomingness
and outgoingness are therefore preserved even when a label becomes trivial.
Such a map is the pushforward along `DirectedWall.Pushforward.ofFixedDegree`, with
identity spatial map, rays and normals.

The construction uses `GradedLieHom.completedMap_mem_wallGroup` to restrict the
existing completed coefficient map. No injectivity or surjectivity is required.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading SupportedRay GradedLieHom)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.DirectedWall

universe u

variable {Γ Λ R V : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'} {ℋ : Γ → Submodule R L''}
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  {H'' : DirectedWallSpaces ρ ℋ}
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m)

/-- A fixed-degree coefficient map, with identity spatial map, rays and normals. -/
def Pushforward.ofFixedDegree : Pushforward d d h h H H' where
  degreeMap := PositiveDegreeMap.id d
  lieHom := f
  rayMap := id
  mem_rayDegrees_rayMap _ _ hn := by simpa using hn
  normalMap := id
  wall_mem n _ m x hx := by simpa using hf n m x hx
  spatialMap := ContinuousAffineEquiv.refl ℝ V
  map_direction _ _ := ⟨1, one_pos, by simp⟩
  realCharacter_normalMap _ := ⟨1, one_pos, by ext; simp⟩

/-- The degree map of a fixed-degree coefficient map is the identity. -/
@[simp]
theorem Pushforward.ofFixedDegree_degreeMap :
    (Pushforward.ofFixedDegree (h := h) f hf).degreeMap = PositiveDegreeMap.id d := (rfl)

/-- The Lie map of a fixed-degree coefficient map has the values of the given map. -/
@[simp]
theorem Pushforward.ofFixedDegree_lieHom_apply (x : L) :
    (Pushforward.ofFixedDegree (h := h) f hf).lieHom x = f x := (rfl)

/-- The ray map of a fixed-degree coefficient map is the identity. -/
@[simp]
theorem Pushforward.ofFixedDegree_rayMap (w : SupportedRay d) :
    (Pushforward.ofFixedDegree (h := h) f hf).rayMap w = w := (rfl)

/-- The normal map of a fixed-degree coefficient map is the identity. -/
@[simp]
theorem Pushforward.ofFixedDegree_normalMap (m : Λ →+ ℤ) :
    (Pushforward.ofFixedDegree (h := h) f hf).normalMap m = m := (rfl)

/-- The spatial map of a fixed-degree coefficient map is the identity. -/
@[simp]
theorem Pushforward.ofFixedDegree_spatialMap :
    (Pushforward.ofFixedDegree (h := h) f hf).spatialMap = ContinuousAffineEquiv.refl ℝ V :=
  (rfl)

/-- The truncations of the Lie map of a fixed-degree coefficient map are those of the
given map. -/
@[simp]
theorem Pushforward.ofFixedDegree_lieHom_truncatedMap [DecidableEq Γ]
    [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
    {a : ℕ} (k : ℕ) (ha : (Pushforward.ofFixedDegree (h := h) f hf).degreeMap.modulus k ≤ a) :
    (Pushforward.ofFixedDegree (h := h) f hf).lieHom.truncatedMap k ha =
      f.truncatedMap k (by simpa using ha) := (rfl)

/-- The identity pushforward data: identity degree map, Lie map, spatial map, rays and
normals. -/
def Pushforward.id : Pushforward d d h h H H :=
  Pushforward.ofFixedDegree (GradedLieHom.id ℒ) (fun _ _ _ hx => by simpa using hx)

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ] [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]
  (W : DirectedWall (d := d) h H)

/-- The Lie map of a fixed-degree coefficient map has the completed map of the given map. -/
@[simp]
theorem Pushforward.ofFixedDegree_lieHom_completedMap :
    (Pushforward.ofFixedDegree (h := h) f hf).lieHom.completedMap = f.completedMap := (rfl)

/-- Map the completed label of a directed wall, retaining all its geometric data. -/
def map : DirectedWall (d := d) h H' where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := W.support
  support_nonempty := W.support_nonempty
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := f.completedMap W.label
  label_mem := f.completedMap_mem_wallGroup
    (fun _ hn => by simpa using hn) (fun n _ x hx => by simpa using hf n W.normal x hx)
    W.label_mem

@[simp]
theorem map_normal : (W.map f hf).normal = W.normal := (rfl)

@[simp]
theorem map_ray : (W.map f hf).ray = W.ray := (rfl)

@[simp]
theorem map_support : (W.map f hf).support = W.support := (rfl)

@[simp]
theorem map_label : (W.map f hf).label = f.completedMap W.label := (rfl)

@[simp]
theorem direction_map : (W.map f hf).direction = W.direction := by
  simp only [direction_def, map_ray]

@[simp]
theorem incoming_map_iff : (W.map f hf).Incoming ↔ W.Incoming := by
  simp only [incoming_iff, map_ray, map_support]

@[simp]
theorem outgoing_map_iff : (W.map f hf).Outgoing ↔ W.Outgoing := by
  simp only [outgoing_iff, map_ray, map_support]

/-- Fixed-degree coefficient maps are pushforwards. -/
@[simp]
theorem pushforward_ofFixedDegree :
    W.pushforward (Pushforward.ofFixedDegree f hf) = W.map f hf := by
  apply DirectedWall.ext
  · rw [pushforward_normal, map_normal, Pushforward.ofFixedDegree_normalMap]
  · rw [pushforward_ray, map_ray, Pushforward.ofFixedDegree_rayMap]
  · rw [pushforward_support, map_support, Pushforward.ofFixedDegree_spatialMap,
      ContinuousAffineEquiv.coe_refl, Set.image_id]
  · rw [pushforward_label, map_label, Pushforward.ofFixedDegree_lieHom_completedMap]

/-- The identity coefficient map fixes every directed wall. -/
@[simp]
theorem map_id : W.map (GradedLieHom.id ℒ) (fun _ _ _ hx => by simpa using hx) = W := by
  apply DirectedWall.ext <;> simp

/-- Successive fixed-degree coefficient maps agree with their composite. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (hg : ∀ n m, ∀ x ∈ H'.wall n m, g x ∈ H''.wall n m) :
    (W.map f hf).map g hg = W.map
      (g.compId f)
      (fun n m x hx => by
        simpa only [GradedLieHom.compId_apply] using hg n m _ (hf n m x hx)) := by
  apply DirectedWall.ext
  · rfl
  · rfl
  · rfl
  · simp only [map_label, GradedLieHom.completedMap_compId, MonoidHom.comp_apply]

/-- The identity pushforward fixes every directed wall. -/
@[simp]
theorem pushforward_id : W.pushforward Pushforward.id = W := by
  rw [Pushforward.id, pushforward_ofFixedDegree, map_id]

end Mei.DirectedWall
