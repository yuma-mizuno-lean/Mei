/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Action

/-!
# Projection of geometric directions

A map of tangent monoids projects directed wall spaces by pulling back integral
normals. The degree monoid, Lie algebra and homogeneous pieces stay fixed. The
contracted-bracket law survives projection, even when the tangent map has a kernel.
Ray subalgebras and completed wall groups agree exactly with those for the pulled
back normal, so this comparison preserves the actual labels at every order.
Wall-annihilating coefficient actions also survive projection.

This construction supplies the algebraic comparison between principal cylinder
walls and their projected walls. We use `DirectedWallSpaces`, its supported-ray
sums and its completed wall groups; no new group or completion is constructed.
-/

public section

namespace Mei

variable {Γ Λ Λ' Λ'' R L : Type*} [AddCommMonoid Γ]
  [AddCommMonoid Λ] [AddCommMonoid Λ'] [AddCommMonoid Λ'']
  [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Pulling back a contracted normal is the contraction of the pulled back normals. -/
theorem wallBracketNormal_comp (ρ : Γ →+ Λ) (π : Λ →+ Λ')
    (n n' : Γ) (m m' : Λ' →+ ℤ) :
    (wallBracketNormal (π.comp ρ) n n' m m').comp π =
      wallBracketNormal ρ n n' (m.comp π) (m'.comp π) := by
  ext v
  simp

namespace DirectedWallSpaces

variable {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}
  (H : DirectedWallSpaces ρ ℒ)

/-- Project geometric directions, retaining precisely the wall spaces for normals
pulled back along the tangent map. No surjectivity assumption is required. -/
def project (π : Λ →+ Λ') : DirectedWallSpaces (π.comp ρ) ℒ where
  wall n m := H.wall n (m.comp π)
  wall_le_piece n m := H.wall_le_piece n (m.comp π)
  zero_normal n := by simpa using H.zero_normal n
  nontangent n m hm := H.nontangent n (m.comp π) hm
  rescale n m c hc := by
    have he : (c • m).comp π = c • m.comp π := by ext v; rfl
    rw [he, H.rescale n (m.comp π) c hc]
  bracket_mem hx hy := by
    rw [wallBracketNormal_comp]
    exact H.bracket_mem hx hy

/-- Projected homogeneous wall spaces use the pulled back normal. -/
@[simp]
theorem project_wall (π : Λ →+ Λ') (n : Γ) (m : Λ' →+ ℤ) :
    (H.project π).wall n m = H.wall n (m.comp π) := (rfl)

/-- Projection by the identity preserves the wall-space datum. -/
@[simp]
theorem project_id : H.project (AddMonoidHom.id Λ) = H := by
  ext n m
  simp

/-- Successive spatial projections compose. -/
@[simp]
theorem project_project (π : Λ →+ Λ') (π' : Λ' →+ Λ'') :
    (H.project π).project π' = H.project (π'.comp π) := by
  ext n m
  rfl

/-- A wall-annihilating action remains so after projection of directions. -/
instance project_isWallAnnihilating {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule L M] (𝒜 : Γ → Submodule R M) [IsWallAnnihilating H 𝒜]
    (π : Λ →+ Λ') : IsWallAnnihilating (H.project π) 𝒜 where
  lie_eq_zero hx ha hm :=
    IsWallAnnihilating.lie_eq_zero (H := H) (𝒜 := 𝒜) hx ha hm

end DirectedWallSpaces

namespace DirectedWallSpaces

variable {Γ Λ Λ' R L : Type*} [AddCommGroup Γ]
  [AddCommMonoid Λ] [AddCommMonoid Λ']
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  (H : DirectedWallSpaces ρ ℒ) (π : Λ →+ Λ')

/-- Projection retains the full supported-ray sum for the pulled back normal. -/
@[simp]
theorem project_raySubmodule (w : SupportedRay d) (m : Λ' →+ ℤ) :
    (H.project π).raySubmodule w m = H.raySubmodule w (m.comp π) := by
  simp only [raySubmodule_def, project_wall]

variable [DecidableEq Γ] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Finite ray logarithms agree under spatial projection. -/
@[simp]
theorem project_truncatedRayLieSubalgebra (w : SupportedRay d) (m : Λ' →+ ℤ) (k : ℕ) :
    (H.project π).truncatedRayLieSubalgebra w m k =
      H.truncatedRayLieSubalgebra w (m.comp π) k := by
  ext x
  simp

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Spatial projection preserves the completed wall group as an actual subgroup
of the same completed BCH group, with its original cutoff projections. -/
@[simp]
theorem project_wallGroup (w : SupportedRay d) (m : Λ' →+ ℤ) :
    (H.project π).wallGroup w m = H.wallGroup w (m.comp π) := by
  ext g
  simp only [mem_wallGroup, project_truncatedRayLieSubalgebra]

end DirectedWallSpaces
end Mei
