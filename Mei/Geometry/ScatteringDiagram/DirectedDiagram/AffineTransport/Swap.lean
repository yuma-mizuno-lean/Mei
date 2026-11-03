/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.AffineTransport.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.WallSpace.TangentChange
public import Mei.Geometry.Toric.Algebraic.IntegralAffine.Swap

/-!
# Transporting directed walls and diagrams along the coordinate swap

The swap `(x, y) ↦ (y, x)` of `ℤ² ⊆ ℝ²` has determinant `-1`. It reverses the orientation
of the plane, yet it carries the wall `{x = 0}` with normal `e₁*` to the wall `{y = 0}`
with normal `e₂*`, keeping its ray and label, and the pairing `⟨m ∘ T⁻¹, T v⟩ = ⟨m, v⟩` of
a normal with a displacement is unchanged. The crossing factor of a wall along a path is
read off from this pairing, so no determinant sign enters: transporting a directed diagram
along the swap does not change its path products.

The swap acts on directed wall spaces through
`DirectedWallSpaces.CoordinateChange.ofTangentEquiv`, which relabels the tangent
directions and leaves the degrees and the Lie algebra alone.
-/

public section

noncomputable section

open TauCeti.Toric

namespace Mei.DirectedWall

open Mei.DirectedWallSpaces

universe u

variable {Γ R : Type*} {L : Type u} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  {ρ : Γ →+ ℤ × ℤ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] {H : DirectedWallSpaces ρ ℒ}
  {h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))}
  (W : DirectedWall (d := d) h H)

/-- Transport a directed wall along the coordinate swap of the plane. -/
def swapImage : DirectedWall (d := d) h (H.mapTangent AddEquiv.prodComm) :=
  W.image (Toric.IntegralAffineEquiv.swap h) (CoordinateChange.ofTangentEquiv H AddEquiv.prodComm)
    (by simp)

/-- The normal of the swapped wall is the original normal pulled back along the swap. -/
theorem swapImage_normal :
    W.swapImage.normal =
      W.normal.comp ((AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).symm : ℤ × ℤ →+ ℤ × ℤ) := by
  simp [swapImage]

/-- A wall with normal `e₁*` is carried to a wall with normal `e₂*`. -/
theorem swapImage_normal_eq_snd (hW : W.normal = AddMonoidHom.fst ℤ ℤ) :
    W.swapImage.normal = AddMonoidHom.snd ℤ ℤ := by
  rw [swapImage_normal, hW]
  ext x
  simp

/-- The support of the swapped wall is the swap of the support. -/
theorem swapImage_support : W.swapImage.support = Prod.swap ⁻¹' W.support := by
  simp [swapImage, Set.image_swap_eq_preimage_swap]

/-- A wall supported on `{x = 0}` is carried to a wall supported on `{y = 0}`. -/
theorem swapImage_support_eq (hW : W.support = {x | x.1 = 0}) :
    W.swapImage.support = {x | x.2 = 0} := by
  rw [swapImage_support, hW]
  ext x
  simp

/-- The swap keeps the degree ray of a wall. -/
@[simp]
theorem swapImage_ray : W.swapImage.ray = W.ray := by
  simp [swapImage]

/-- The swap keeps the label of a wall: the orientation reversal does not invert it. -/
@[simp]
theorem swapImage_label : W.swapImage.label = W.label := by
  simp [swapImage]

/-- Pairing the swapped normal with a swapped vector gives the original pairing, with no
sign from the determinant `-1`. -/
theorem realCharacter_swapImage_normal_swap (v : ℝ × ℝ) :
    h.realCharacter W.swapImage.normal v.swap = h.realCharacter W.normal v := by
  simpa [swapImage] using
    W.realCharacter_image_normal (Toric.IntegralAffineEquiv.swap h)
      (CoordinateChange.ofTangentEquiv H AddEquiv.prodComm) (by simp) v

/-- The wall on the line `{x = 0}` with normal `e₁*`, a given ray and a given label is
carried to the wall on `{y = 0}` with normal `e₂*`, the same ray and the same label. -/
theorem swapImage_ofLinearHyperplane_fst (hm : AddMonoidHom.fst ℤ ℤ ≠ 0) (w : SupportedRay d)
    (hw : AddMonoidHom.fst ℤ ℤ (ρ w.generator) = 0) (g : H.wallGroup w (AddMonoidHom.fst ℤ ℤ)) :
    (ofLinearHyperplane h H (AddMonoidHom.fst ℤ ℤ) hm w hw g).swapImage.normal =
        AddMonoidHom.snd ℤ ℤ ∧
      (ofLinearHyperplane h H (AddMonoidHom.fst ℤ ℤ) hm w hw g).swapImage.support =
        {x | x.2 = 0} ∧
      (ofLinearHyperplane h H (AddMonoidHom.fst ℤ ℤ) hm w hw g).swapImage.ray = w ∧
      (ofLinearHyperplane h H (AddMonoidHom.fst ℤ ℤ) hm w hw g).swapImage.label = g := by
  refine ⟨swapImage_normal_eq_snd _ (by simp), swapImage_support_eq _ ?_, by simp, by simp⟩
  ext x
  simp

end Mei.DirectedWall

namespace Mei.DirectedDiagram

universe u

variable {Γ R ι : Type*} {L : Type u} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  {ρ : Γ →+ ℤ × ℤ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] {H : DirectedWallSpaces ρ ℒ}
  {h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))}
  (D : DirectedDiagram (d := d) h H ι)

/-- Transport a directed diagram along the coordinate swap of the plane. -/
def swapImage : DirectedDiagram (d := d) h (H.mapTangent AddEquiv.prodComm) ι :=
  D.image (Toric.IntegralAffineEquiv.swap h)
    (DirectedWallSpaces.CoordinateChange.ofTangentEquiv H AddEquiv.prodComm) (by simp)

/-- Transport the points and paths of a directed diagram along the coordinate swap. -/
def swapPathImage : D.Point ⥤q D.swapImage.Point :=
  D.pathImage (Toric.IntegralAffineEquiv.swap h)
    (DirectedWallSpaces.CoordinateChange.ofTangentEquiv H AddEquiv.prodComm) (by simp)

/-- The coordinate swap does not change path products: the completed product along a
path and along its swapped path agree, although the swap reverses orientation. -/
theorem pathProduct_swapImage {x y : D.Point} (p : Quiver.Path x y) :
    D.swapImage.pathProduct (D.swapPathImage.mapPath p) = D.pathProduct p := by
  exact (D.pathProduct_image _ _ _ p).trans (by simp)

end Mei.DirectedDiagram

end
