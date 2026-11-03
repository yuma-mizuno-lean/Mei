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

namespace Mei.DirectedWallSpaces

universe u

variable {Γ Λ Λ' R : Type*} {L : Type u}
  [AddCommGroup Γ] [AddCommMonoid Λ] [AddCommMonoid Λ'] [CommRing R]
  [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ) (T : Λ ≃+ Λ')

/-- Relabel the tangent directions of a directed wall space along an additive equivalence.
The wall space of degree `n` and normal `m` is the original one with normal `m ∘ T`. -/
def mapTangent : DirectedWallSpaces ((T : Λ →+ Λ').comp ρ) ℒ where
  wall n m := H.wall n (m.comp T)
  wall_le_piece n m := H.wall_le_piece n _
  zero_normal n := H.zero_normal n
  nontangent n m hm := H.nontangent n _ hm
  rescale n m c hc := by
    have hc' : (c • m).comp (T : Λ →+ Λ') = c • m.comp (T : Λ →+ Λ') := by
      ext v
      simp
    simpa only [hc'] using H.rescale n (m.comp (T : Λ →+ Λ')) c hc
  bracket_mem {n n' m m' x y} hx hy := by
    have hn : wallBracketNormal ρ n n' (m.comp T) (m'.comp T) =
        (wallBracketNormal ((T : Λ →+ Λ').comp ρ) n n' m m').comp T := by
      ext v
      simp
    exact hn ▸ H.bracket_mem hx hy

/-- The wall space of the relabelled tangent directions is that of the original with
the normal precomposed by `T`. -/
@[simp]
theorem mapTangent_wall (n : Γ) (m : Λ' →+ ℤ) :
    (H.mapTangent T).wall n m = H.wall n (m.comp T) := (rfl)

/-- Transporting a normal `m` along `T` and pulling it back by `T⁻¹` gives the same wall
space as the original. -/
theorem mapTangent_wall_comp_symm (n : Γ) (m : Λ →+ ℤ) :
    (H.mapTangent T).wall n (m.comp (T.symm : Λ' →+ Λ)) = H.wall n m := by
  rw [mapTangent_wall]
  congr 1
  ext v
  simp

namespace CoordinateChange

variable {d : PositiveDegrees Γ}

/-- Relabelling tangent directions along `T` is a coordinate change with identity degree
and Lie coordinates. -/
def ofTangentEquiv : CoordinateChange (d := d) (e := d) H (H.mapTangent T) where
  degreeEquiv := AddEquiv.refl Γ
  tangentEquiv := T
  lieEquiv := LieEquiv.refl
  monoid_mem_iff _ := Iff.rfl
  map_direction _ := rfl
  piece_mem_iff _ _ := Iff.rfl
  wall_mem_iff n m x := by
    rw [LieEquiv.refl_apply, AddEquiv.refl_apply, H.mapTangent_wall_comp_symm T n m]

@[simp]
theorem ofTangentEquiv_degreeEquiv :
    (ofTangentEquiv (d := d) H T).degreeEquiv = AddEquiv.refl Γ := (rfl)

@[simp]
theorem ofTangentEquiv_tangentEquiv : (ofTangentEquiv (d := d) H T).tangentEquiv = T := (rfl)

@[simp]
theorem ofTangentEquiv_lieEquiv : (ofTangentEquiv (d := d) H T).lieEquiv = LieEquiv.refl := (rfl)

/-- A tangent coordinate change fixes every supported ray. -/
@[simp]
theorem ofTangentEquiv_rayEquiv :
    (ofTangentEquiv (d := d) H T).rayEquiv = Equiv.refl (SupportedRay d) := by
  apply Equiv.ext
  intro w
  apply SupportedRay.ext
  simp

variable [DecidableEq Γ] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [Algebra ℚ R]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A tangent coordinate change acts as the identity on completed labels. -/
@[simp]
theorem ofTangentEquiv_completedEquiv :
    (ofTangentEquiv (d := d) H T).completedEquiv = MulEquiv.refl (d.completedBCHGroup ℒ) := by
  apply MulEquiv.ext
  intro g
  rw [completedEquiv_apply, MulEquiv.refl_apply]
  exact DFunLike.congr_fun
    ((GradedLieHom.completedMap_eq_of_toLieHom_eq _ (GradedLieHom.id ℒ)
      (by ext x; simp)).trans GradedLieHom.completedMap_id) g

end CoordinateChange

end Mei.DirectedWallSpaces
