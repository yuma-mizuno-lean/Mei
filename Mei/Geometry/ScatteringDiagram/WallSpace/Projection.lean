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

open TauCeti (SupportedRay)

open TauCeti (DirectedWallSpaces)

namespace TauCeti

open Mei

variable {Γ Λ Λ' Λ'' R L : Type*} [AddCommMonoid Γ]
  [AddCommMonoid Λ] [AddCommMonoid Λ'] [AddCommMonoid Λ'']
  [CommRing R] [LieRing L] [LieAlgebra R L]

namespace DirectedWallSpaces

variable {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}
  (H : DirectedWallSpaces ρ ℒ)

/-- Projection by the identity preserves the wall-space datum. -/
@[simp]
theorem mapTangent_id : H.mapTangent (AddMonoidHom.id Λ) = H := by
  ext n m
  simp

/-- Successive spatial projections compose. -/
@[simp]
theorem mapTangent_mapTangent (π : Λ →+ Λ') (π' : Λ' →+ Λ'') :
    (H.mapTangent π).mapTangent π' = H.mapTangent (π'.comp π) := by
  ext n m
  simp only [mapTangent_wall, AddMonoidHom.comp_assoc]

/-- A wall-annihilating action remains so after projection of directions. -/
instance mapTangent_isWallAnnihilating {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule L M] (𝒜 : Γ → Submodule R M) [IsWallAnnihilating H 𝒜]
    (π : Λ →+ Λ') : IsWallAnnihilating (H.mapTangent π) 𝒜 where
  lie_eq_zero hx ha hm := by
    rw [mapTangent_wall] at hx
    exact IsWallAnnihilating.lie_eq_zero (H := H) (𝒜 := 𝒜) hx ha hm

end DirectedWallSpaces

namespace DirectedWallSpaces

variable {Γ Λ Λ' R L : Type*} [AddCommGroup Γ]
  [AddCommMonoid Λ] [AddCommMonoid Λ']
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : TauCeti.PositiveDegrees Γ}
  (H : DirectedWallSpaces ρ ℒ) (π : Λ →+ Λ')

/-- Projection retains the full supported-ray sum for the pulled back normal. -/
@[simp]
theorem mapTangent_raySubmodule (w : SupportedRay d) (m : Λ' →+ ℤ) :
    (H.mapTangent π).raySubmodule w m = H.raySubmodule w (m.comp π) := by
  simp only [raySubmodule_def, mapTangent_wall]

variable [DecidableEq Γ] [GradedLieAlgebra ℒ] [TauCeti.IsPositiveGrading d ℒ]

/-- Finite ray logarithms agree under spatial projection. -/
@[simp]
theorem mapTangent_truncatedRayLieSubalgebra (w : SupportedRay d) (m : Λ' →+ ℤ) (k : ℕ) :
    (H.mapTangent π).truncatedRayLieSubalgebra w m k =
      H.truncatedRayLieSubalgebra w (m.comp π) k := by
  ext x
  simp

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Spatial projection preserves the completed wall group as an actual subgroup
of the same completed BCH group, with its original cutoff projections. -/
@[simp]
theorem mapTangent_wallGroup (w : SupportedRay d) (m : Λ' →+ ℤ) :
    (H.mapTangent π).wallGroup w m = H.wallGroup w (m.comp π) := by
  ext g
  simp only [mem_wallGroup, mapTangent_truncatedRayLieSubalgebra]

end DirectedWallSpaces
end TauCeti
