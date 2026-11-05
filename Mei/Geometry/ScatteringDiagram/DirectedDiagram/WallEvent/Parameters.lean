/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3.1 Pro
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic

/-!
# Basic data indexed by an active wall of a directed diagram

The support, real normal and offset of every directed wall are collected as
families indexed by the walls active at a given cutoff. These are the families
used by simultaneous-event encounters, keeping definitions and statements short
without hiding the underlying `DirectedWall` data.
-/

public noncomputable section

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι)

/-- The support family of the walls active at cutoff `k`. -/
abbrev activeSupport (k : ℕ) : D.active k → Set V := fun c => (D.wall c).support

@[simp]
theorem activeSupport_apply (k : ℕ) (c : D.active k) :
    D.activeSupport k c = (D.wall c).support := (rfl)

/-- The real conormal family of the walls active at cutoff `k`. -/
abbrev activeNormal (k : ℕ) : D.active k → V →L[ℝ] ℝ := fun c =>
  h.continuousRealCharacter (D.wall c).normal

@[simp]
theorem activeNormal_apply (k : ℕ) (c : D.active k) :
    D.activeNormal k c = h.continuousRealCharacter (D.wall c).normal := (rfl)

/-- The real offset family of the walls active at cutoff `k`. -/
abbrev activeOffset (k : ℕ) : D.active k → ℝ := fun c => (D.wall c).offset

@[simp]
theorem activeOffset_apply (k : ℕ) (c : D.active k) :
    D.activeOffset k c = (D.wall c).offset := (rfl)

end Mei.DirectedDiagram
