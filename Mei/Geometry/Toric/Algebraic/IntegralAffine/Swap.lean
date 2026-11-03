/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Toric.Algebraic.IntegralAffine
public import Mathlib.LinearAlgebra.Determinant

/-!
# The coordinate swap of the plane

The swap `(x, y) ↦ (y, x)` of `ℤ² ⊆ ℝ²` is an integral affine self-equivalence of the
standard lattice with zero translation. It reverses orientation: its linear part has
determinant `-1`. The two coordinate characters of `ℤ²` extend to the two real coordinates.
-/

public section

noncomputable section

open TauCeti.Toric

namespace Mei.Toric.IntegralAffineEquiv

variable (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The coordinate swap of `ℝ²` as an integral affine equivalence of the standard
lattice `ℤ²`, with zero translation. -/
def swap : IntegralAffineEquiv h h := ofLatticeEquiv h h AddEquiv.prodComm

/-- The swap exchanges the two coordinates. -/
@[simp]
theorem swap_apply (x : ℝ × ℝ) : swap h x = x.swap := by
  have hx := congrArg (fun g : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ => g x)
    (h.eq_extend (i' := (Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))
      (f := AddEquiv.prodComm.toAddMonoidHom)
      (g := (LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.fst ℝ ℝ ℝ)) (fun n => Prod.ext rfl rfl))
  simpa [swap, Prod.swap] using hx.symm

/-- The swap exchanges the two lattice coordinates. -/
@[simp]
theorem swap_latticeEquiv : (swap h).latticeEquiv = AddEquiv.prodComm := by
  simp [swap]

/-- The linear part of the swap exchanges the two coordinates. -/
@[simp]
theorem swap_linear_apply (x : ℝ × ℝ) : (swap h).toAffineEquiv.linear x = x.swap := by
  simpa using ((swap h).toAffineEquiv.map_vadd 0 x).symm.trans (swap_apply h _)

/-- The swap reverses orientation: its linear part has determinant `-1`. -/
theorem det_swap : LinearMap.det ((swap h).toAffineEquiv.linear : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) = -1 := by
  let b := Module.Basis.finTwoProd ℝ
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, b]

end Mei.Toric.IntegralAffineEquiv

namespace TauCeti.Toric.IsIntegralLattice

variable (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The first coordinate character of `ℤ²` extends to the first real coordinate. -/
@[simp]
theorem realCharacter_fst : h.realCharacter (AddMonoidHom.fst ℤ ℤ) = LinearMap.fst ℝ ℝ ℝ :=
  (h.eq_realCharacter (by intro x; simp)).symm

/-- The second coordinate character of `ℤ²` extends to the second real coordinate. -/
@[simp]
theorem realCharacter_snd : h.realCharacter (AddMonoidHom.snd ℤ ℤ) = LinearMap.snd ℝ ℝ ℝ :=
  (h.eq_realCharacter (by intro x; simp)).symm

end TauCeti.Toric.IsIntegralLattice

end
