/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.CoordinateChange

/-!
# Tangent coordinate changes of directed wall spaces

An additive equivalence `T : Λ ≃+ Λ'` of tangent monoids relabels the tangent
directions of a directed wall space and leaves the degrees and the Lie algebra
untouched. The geometric direction becomes `T ∘ ρ`, and the wall spaces with
normal `m` are those of the original with normal `m ∘ T`; equivalently, the
original normal `m` becomes `m ∘ T⁻¹`. This is the algebraic half of a linear
integral affine isomorphism whose degree lattice is fixed.

`DirectedWallSpaces.CoordinateChange.ofTangentEquiv` packages this relabelling as a
`CoordinateChange` with identity degree and Lie coordinates. Its completed comparison
is the identity, so labels of transported walls are literally unchanged.
-/

public section

open TauCeti (SupportedRay)

open TauCeti (DirectedWallSpaces)

namespace TauCeti.DirectedWallSpaces

open Mei

universe u

variable {Γ Λ Λ' R : Type*} {L : Type u}
  [AddCommGroup Γ] [AddCommMonoid Λ] [AddCommMonoid Λ'] [CommRing R]
  [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ) (T : Λ ≃+ Λ')

namespace CoordinateChange

variable {d : TauCeti.PositiveDegrees Γ}

/-- A tangent coordinate change fixes every supported ray. -/
@[simp]
theorem ofTangentEquiv_rayEquiv :
    (ofTangentEquiv (d := d) H T).rayEquiv = Equiv.refl (SupportedRay d) := by
  apply Equiv.ext
  intro w
  apply SupportedRay.ext
  simp

variable [DecidableEq Γ] [GradedLieAlgebra ℒ] [TauCeti.IsPositiveGrading d ℒ] [Algebra ℚ R]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A tangent coordinate change acts as the identity on completed labels. -/
@[simp]
theorem ofTangentEquiv_completedEquiv :
    (ofTangentEquiv (d := d) H T).completedEquiv = MulEquiv.refl (d.completedBCHGroup ℒ) := by
  apply MulEquiv.ext
  intro g
  rw [completedEquiv_apply, MulEquiv.refl_apply]
  exact DFunLike.congr_fun
    ((Mei.GradedLieHom.completedMap_eq_of_toLieHom_eq _ (Mei.GradedLieHom.id ℒ)
      (by ext x; simp)).trans Mei.GradedLieHom.completedMap_id) g

end CoordinateChange

end TauCeti.DirectedWallSpaces
