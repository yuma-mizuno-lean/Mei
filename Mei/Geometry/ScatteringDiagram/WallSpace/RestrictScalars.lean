/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Basic
public import Mei.Algebra.Lie.Graded.RestrictScalars

/-!
# Restriction of scalars for directed wall spaces

Directed wall spaces retain their homogeneous carriers and bracket laws over any
compatible smaller scalar ring. This permits comparison of wall labels with
different coefficient rings over a common base. The construction uses Mathlib's
`Submodule.restrictScalars` and the existing scalar restriction of Lie gradings.
-/

public section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R S L : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [CommRing S] [LieRing L] [LieAlgebra S L] [LieAlgebra R L]
  [SMul R S] [IsScalarTower R S L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule S L}

/-- Regard directed wall spaces over a compatible smaller scalar ring, without
changing their elements or normals. -/
def restrictScalars (H : DirectedWallSpaces ρ ℒ) (R : Type*) [CommRing R]
    [LieAlgebra R L] [SMul R S] [IsScalarTower R S L] :
    DirectedWallSpaces ρ (fun n => (ℒ n).restrictScalars R) where
  wall n m := (H.wall n m).restrictScalars R
  wall_le_piece n m := H.wall_le_piece n m
  zero_normal n := by simp [H.zero_normal]
  nontangent n m hm := by simp [H.nontangent n m hm]
  rescale n m c hc := by rw [H.rescale n m c hc]
  bracket_mem hx hy := H.bracket_mem hx hy

/-- Restricting wall spaces restricts their underlying submodules. -/
@[simp]
theorem restrictScalars_wall (H : DirectedWallSpaces ρ ℒ) (n : Γ) (m : Λ →+ ℤ) :
    (H.restrictScalars R).wall n m = (H.wall n m).restrictScalars R := (rfl)

end Mei.DirectedWallSpaces
