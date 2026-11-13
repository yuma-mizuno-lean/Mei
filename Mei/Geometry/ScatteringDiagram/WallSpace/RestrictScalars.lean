/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Algebra.Lie.BCH.RestrictScalars
public import Mei.Algebra.Lie.Graded.RestrictScalars

/-!
# Restriction of scalars for directed wall spaces

Directed wall spaces retain their homogeneous carriers and bracket laws over any
compatible smaller scalar ring. This permits comparison of wall labels with
different coefficient rings over a common base. The construction uses Mathlib's
`Submodule.restrictScalars` and the existing scalar restriction of Lie gradings.

The supported-ray wall sums restrict in the same way
(`DirectedWallSpaces.raySubmodule_restrictScalars`), so the scalar-restriction comparison
`TauCeti.PositiveDegrees.completedBCHRestrictScalarsEquiv` of completed BCH groups identifies
the wall
groups of the restricted wall spaces with the original wall groups
(`DirectedWallSpaces.mem_wallGroup_restrictScalars_iff`).
-/

public section

open TauCeti (SupportedRay)

open TauCeti (DirectedWallSpaces)

namespace TauCeti.DirectedWallSpaces

open Mei

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

section Group

variable {Γ Λ R S L : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [CommRing S] [LieRing L] [LieAlgebra S L] [LieAlgebra R L]
  [SMul R S] [IsScalarTower R S L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule S L} {d : TauCeti.PositiveDegrees Γ} (H : DirectedWallSpaces ρ ℒ)

/-- The supported-ray wall sums of the restricted wall spaces are the restrictions of the
original ray sums. -/
@[simp]
theorem raySubmodule_restrictScalars (w : SupportedRay d) (m : Λ →+ ℤ) :
    (H.restrictScalars R).raySubmodule w m = (H.raySubmodule w m).restrictScalars R := by
  simp only [raySubmodule_def, restrictScalars_wall, Submodule.restrictScalars_iSup]

variable [DecidableEq Γ] [GradedLieAlgebra ℒ] [TauCeti.IsPositiveGrading d ℒ]

/-- The finite truncation comparison identifies the truncated supported-ray wall algebras. -/
theorem truncatedRestrictScalarsEquiv_mem_truncatedRayLieSubalgebra_iff (w : SupportedRay d)
    (m : Λ →+ ℤ) (k : ℕ) (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k x ∈ H.truncatedRayLieSubalgebra w m k ↔
      x ∈ (H.restrictScalars R).truncatedRayLieSubalgebra w m k := by
  simp only [mem_truncatedRayLieSubalgebra, raySubmodule_restrictScalars,
    Submodule.restrictScalars_mem, LieIdeal.mkQ_apply]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [← TauCeti.PositiveDegrees.truncatedRestrictScalarsEquiv_mk (R := R) ℒ d k y,
    EquivLike.apply_eq_iff_eq]

variable [Algebra ℚ R] [Algebra ℚ S] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [IsScalarTower ℚ S L]

/-- The scalar-restriction comparison of completed BCH groups identifies the wall groups of the
restricted wall spaces with the original wall groups. -/
theorem mem_wallGroup_restrictScalars_iff (w : SupportedRay d) (m : Λ →+ ℤ)
    (g : d.completedBCHGroup (fun n => (ℒ n).restrictScalars R)) :
    d.completedBCHRestrictScalarsEquiv (R := R) ℒ g ∈ H.wallGroup w m ↔
      g ∈ (H.restrictScalars R).wallGroup w m := by
  simp only [mem_wallGroup, TauCeti.PositiveDegrees.projection_completedBCHRestrictScalarsEquiv]
  refine forall_congr' fun k => ?_
  -- The projection has a categorical tower-object type; re-elaborate it as a BCH group element.
  generalize (TauCeti.CompletedGroup.projection k g :
    BCHGroup (d.truncatedLie (fun n => (ℒ n).restrictScalars R) k)) = x
  rw [LieHom.log_bchGroupMap (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom x]
  exact H.truncatedRestrictScalarsEquiv_mem_truncatedRayLieSubalgebra_iff w m k _

end Group

end TauCeti.DirectedWallSpaces
