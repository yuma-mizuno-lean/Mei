/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Map
public import Mei.Geometry.ScatteringDiagram.WallSpace.RestrictScalars

/-!
# Restriction of scalars for directed walls

Let `H` be directed wall spaces of a positively graded Lie algebra over a commutative
`ℚ`-algebra `R`, and let `K` be a smaller scalar ring. The restricted wall spaces
`H.restrictScalars K` have the same elements, and the scalar-restriction comparison
`PositiveDegrees.completedBCHRestrictScalarsEquiv` identifies the completed BCH groups and their
wall groups (`DirectedWallSpaces.mem_wallGroup_restrictScalars_iff`). Hence a directed wall for
`H` is a directed wall for the restricted wall spaces with the same normal, supported ray and
support (`DirectedWall.restrictScalars`), and conversely (`DirectedWall.ofRestrictScalars`);
the two constructions are mutually inverse.

This allows coefficient maps between different coefficient rings over a common base ring `K`.
A `K`-linear fixed-degree graded Lie homomorphism `f` between the restricted gradings of
algebras over `R` and over `S` that preserves the restricted wall spaces maps a wall for `H` to
a wall for the wall spaces `H'` over `S` (`DirectedWall.mapRestrictScalars`): restrict scalars,
apply the fixed-degree map `DirectedWall.map` and undo the restriction. The normal, supported
ray and support are retained, so incomingness and outgoingness are preserved.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading GradedLieHom)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.DirectedWall

universe u

variable {Γ Λ K R V : Type*} {L : Type u} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing K] [CommRing R] [Algebra ℚ K] [Algebra ℚ R] [SMul K R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra K L] [LieAlgebra ℚ L]
  [IsScalarTower K R L] [IsScalarTower ℚ K L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}

section Restrict

variable (K) in
/-- Regard a directed wall as a wall for the wall spaces over the smaller scalar ring `K`, with
the same normal, supported ray and support, and the label transported by the inverse
scalar-restriction comparison of completed BCH groups. -/
def restrictScalars (W : DirectedWall (d := d) h H) :
    DirectedWall (d := d) h (H.restrictScalars K) where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := W.support
  support_nonempty := W.support_nonempty
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := (d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label
  label_mem := (H.mem_wallGroup_restrictScalars_iff W.ray W.normal _).mp (by
    rw [MulEquiv.apply_symm_apply]
    exact W.label_mem)

/-- Regard a directed wall for the restricted wall spaces as a wall for the original wall
spaces, with the label transported by the scalar-restriction comparison. -/
def ofRestrictScalars (W : DirectedWall (d := d) h (H.restrictScalars K)) :
    DirectedWall (d := d) h H where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := W.support
  support_nonempty := W.support_nonempty
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := d.completedBCHRestrictScalarsEquiv (R := K) ℒ W.label
  label_mem := (H.mem_wallGroup_restrictScalars_iff W.ray W.normal _).mpr W.label_mem

variable (W : DirectedWall (d := d) h H) (W' : DirectedWall (d := d) h (H.restrictScalars K))

/-- Restricting scalars keeps the normal. -/
@[simp]
theorem restrictScalars_normal : (W.restrictScalars K).normal = W.normal := (rfl)

/-- Restricting scalars keeps the supported ray. -/
@[simp]
theorem restrictScalars_ray : (W.restrictScalars K).ray = W.ray := (rfl)

/-- Restricting scalars keeps the support. -/
@[simp]
theorem restrictScalars_support : (W.restrictScalars K).support = W.support := (rfl)

/-- The restricted label is the inverse scalar-restriction comparison of the label. -/
@[simp]
theorem restrictScalars_label :
    (W.restrictScalars K).label = (d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label :=
  (rfl)

/-- Undoing a restriction of scalars keeps the normal. -/
@[simp]
theorem ofRestrictScalars_normal : W'.ofRestrictScalars.normal = W'.normal := (rfl)

/-- Undoing a restriction of scalars keeps the supported ray. -/
@[simp]
theorem ofRestrictScalars_ray : W'.ofRestrictScalars.ray = W'.ray := (rfl)

/-- Undoing a restriction of scalars keeps the support. -/
@[simp]
theorem ofRestrictScalars_support : W'.ofRestrictScalars.support = W'.support := (rfl)

/-- The label is transported by the scalar-restriction comparison. -/
@[simp]
theorem ofRestrictScalars_label :
    W'.ofRestrictScalars.label = d.completedBCHRestrictScalarsEquiv (R := K) ℒ W'.label := (rfl)

/-- Undoing a restriction of scalars recovers the wall. -/
@[simp]
theorem ofRestrictScalars_restrictScalars : (W.restrictScalars K).ofRestrictScalars = W := by
  apply DirectedWall.ext <;> simp

/-- Restricting the scalars of a wall obtained from the restricted wall spaces recovers it. -/
@[simp]
theorem restrictScalars_ofRestrictScalars : W'.ofRestrictScalars.restrictScalars K = W' := by
  apply DirectedWall.ext <;> simp

/-- Restricting scalars keeps the label trivial exactly when it was trivial. -/
theorem restrictScalars_label_eq_one_iff : (W.restrictScalars K).label = 1 ↔ W.label = 1 := by
  rw [restrictScalars_label, MulEquiv.map_eq_one_iff]

/-- Restricting scalars keeps the label trivial at a finite order exactly when it was trivial
there. -/
theorem projection_restrictScalars_label_eq_one_iff (k : ℕ) :
    TauCeti.CompletedGroup.projection k (W.restrictScalars K).label = 1 ↔
      TauCeti.CompletedGroup.projection k W.label = 1 := by
  rw [← PositiveDegrees.projection_completedBCHRestrictScalarsEquiv_eq_one_iff,
    restrictScalars_label, MulEquiv.apply_symm_apply]

/-- Restricting scalars preserves and reflects incomingness. -/
@[simp]
theorem incoming_restrictScalars_iff : (W.restrictScalars K).Incoming ↔ W.Incoming := by
  simp only [incoming_iff, restrictScalars_ray, restrictScalars_support]

/-- Restricting scalars preserves and reflects outgoingness. -/
@[simp]
theorem outgoing_restrictScalars_iff : (W.restrictScalars K).Outgoing ↔ W.Outgoing := by
  simp only [outgoing_iff, restrictScalars_ray, restrictScalars_support]

end Restrict

section Map

variable {S : Type*} {L' : Type u} [CommRing S] [Algebra ℚ S] [SMul K S]
  [LieRing L'] [LieAlgebra S L'] [LieAlgebra K L'] [LieAlgebra ℚ L']
  [IsScalarTower K S L'] [IsScalarTower ℚ K L'] [IsScalarTower ℚ S L']
  {ℳ : Γ → Submodule S L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
  {H' : DirectedWallSpaces ρ ℳ}
  (f : GradedLieHom (PositiveDegreeMap.id d) (fun n => (ℒ n).restrictScalars K)
    (fun n => (ℳ n).restrictScalars K))
  (hf : ∀ n m, ∀ x ∈ (H.restrictScalars K).wall n m, f x ∈ (H'.restrictScalars K).wall n m)
  (W : DirectedWall (d := d) h H)

/-- Change the coefficient ring of a directed wall along a `K`-linear fixed-degree graded Lie
homomorphism `f` of the restricted gradings preserving the restricted wall spaces: restrict
scalars, apply `f` to the label and undo the restriction. The normal, supported ray and support
are retained. -/
def mapRestrictScalars : DirectedWall (d := d) h H' :=
  ((W.restrictScalars K).map f hf).ofRestrictScalars

/-- The coefficient change is the fixed-degree map of the restricted wall, read back over the
target coefficient ring. -/
theorem mapRestrictScalars_def :
    W.mapRestrictScalars f hf = ((W.restrictScalars K).map f hf).ofRestrictScalars := (rfl)

/-- Changing the coefficient ring keeps the normal. -/
@[simp]
theorem mapRestrictScalars_normal : (W.mapRestrictScalars f hf).normal = W.normal := by
  rw [mapRestrictScalars_def, ofRestrictScalars_normal, map_normal, restrictScalars_normal]

/-- Changing the coefficient ring keeps the supported ray. -/
@[simp]
theorem mapRestrictScalars_ray : (W.mapRestrictScalars f hf).ray = W.ray := by
  rw [mapRestrictScalars_def, ofRestrictScalars_ray, map_ray, restrictScalars_ray]

/-- Changing the coefficient ring keeps the support. -/
@[simp]
theorem mapRestrictScalars_support : (W.mapRestrictScalars f hf).support = W.support := by
  rw [mapRestrictScalars_def, ofRestrictScalars_support, map_support, restrictScalars_support]

/-- The label is transported by `f` through the two scalar-restriction comparisons. -/
@[simp]
theorem mapRestrictScalars_label :
    (W.mapRestrictScalars f hf).label = d.completedBCHRestrictScalarsEquiv (R := K) ℳ
      (f.completedMap ((d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label)) := by
  rw [mapRestrictScalars_def, ofRestrictScalars_label, map_label, restrictScalars_label]

/-- Restricting the scalars of the coefficient change gives the fixed-degree map of the
restricted wall. -/
@[simp]
theorem restrictScalars_mapRestrictScalars :
    (W.mapRestrictScalars f hf).restrictScalars K = (W.restrictScalars K).map f hf := by
  rw [mapRestrictScalars_def, restrictScalars_ofRestrictScalars]

/-- Changing the coefficient ring preserves and reflects incomingness. -/
@[simp]
theorem incoming_mapRestrictScalars_iff : (W.mapRestrictScalars f hf).Incoming ↔ W.Incoming := by
  simp only [incoming_iff, mapRestrictScalars_ray, mapRestrictScalars_support]

/-- Changing the coefficient ring preserves and reflects outgoingness. -/
@[simp]
theorem outgoing_mapRestrictScalars_iff : (W.mapRestrictScalars f hf).Outgoing ↔ W.Outgoing := by
  simp only [outgoing_iff, mapRestrictScalars_ray, mapRestrictScalars_support]

end Map

end Mei.DirectedWall
