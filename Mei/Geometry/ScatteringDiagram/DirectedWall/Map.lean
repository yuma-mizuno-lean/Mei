/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Hom

/-!
# Fixed-degree coefficient maps of directed walls

A graded Lie homomorphism preserving homogeneous wall spaces maps directed wall
labels while retaining the normal, supported ray and affine support. Incomingness
and outgoingness are therefore preserved even when a label becomes trivial.

The construction uses `GradedLieHom.completedMap_mem_wallGroup` to restrict the
existing completed coefficient map. No injectivity or surjectivity is required.
-/

public section

noncomputable section

namespace Mei.DirectedWall

universe u

variable {Γ Λ R V : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'} {ℋ : Γ → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  {H'' : DirectedWallSpaces ρ ℋ}
  (W : DirectedWall (d := d) h H)
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m)

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

/-- The identity coefficient map fixes every directed wall. -/
@[simp]
theorem map_id : W.map (GradedLieHom.id ℒ) (fun _ _ _ hx => by simpa using hx) = W := by
  apply DirectedWall.ext <;> simp

/-- Successive fixed-degree coefficient maps agree with their composite. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (hg : ∀ n m, ∀ x ∈ H'.wall n m, g x ∈ H''.wall n m) :
    (W.map f hf).map g hg = W.map
      { toLieHom := g.toLieHom.comp f.toLieHom
        map_mem hx := by simpa using g.map_mem (f.map_mem hx) }
      (fun n m x hx => hg n m _ (hf n m x hx)) := by
  apply DirectedWall.ext
  · rfl
  · rfl
  · rfl
  · simp only [map_label]
    rw [← MonoidHom.comp_apply, ← GradedLieHom.completedMap_comp]
    exact DFunLike.congr_fun
      (GradedLieHom.completedMap_eq_of_toLieHom_eq (g.comp f)
        ({ toLieHom := g.toLieHom.comp f.toLieHom
           map_mem hx := by simpa using g.map_mem (f.map_mem hx) } :
          GradedLieHom (PositiveDegreeMap.id d) ℒ ℋ) (by simp)) W.label

end Mei.DirectedWall
