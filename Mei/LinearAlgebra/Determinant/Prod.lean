/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The determinant bilinear form on pairs

`Prod.det` is the alternating bilinear form `x₁ y₂ - x₂ y₁` on `R × R`.
Over a linearly ordered field, `Prod.det_trans` expresses transitivity of its sign relative
to a scalar for vectors in the open half-plane `x₁ + x₂ < 0`.
-/

public section

namespace Prod

/-- The determinant bilinear form on pairs over a commutative ring. -/
def det {R : Type*} [CommRing R] : (R × R) →ₗ[R] (R × R) →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y => x.1 * y.2 - x.2 * y.1) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- Evaluate the determinant bilinear form in coordinates. -/
@[simp] theorem det_apply {R : Type*} [CommRing R] (x y : R × R) :
    det x y = x.1 * y.2 - x.2 * y.1 := by
  simp [det]

/-- The determinant bilinear form is alternating. -/
theorem det_isAlt {R : Type*} [CommRing R] : (det (R := R)).IsAlt := fun x => by
  rw [det_apply]
  ring

/-- For vectors in the open half-plane `x₁ + x₂ < 0`, the relation "`det x y` is a positive
multiple of `c`" is transitive. -/
theorem det_trans {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {c : R} {x y z : R × R} (hx : x.1 + x.2 < 0) (hy : y.1 + y.2 < 0)
    (hz : z.1 + z.2 < 0) (hxy : ∃ α > 0, det x y = c * α)
    (hyz : ∃ α > 0, det y z = c * α) : ∃ α > 0, det x z = c * α := by
  obtain ⟨α, hα, hxy⟩ := hxy
  obtain ⟨γ, hγ, hyz⟩ := hyz
  refine ⟨(γ * (x.1 + x.2) + α * (z.1 + z.2)) / (y.1 + y.2),
    div_pos_of_neg_of_neg (by nlinarith) hy, ?_⟩
  rw [det_apply] at hxy hyz ⊢
  rw [mul_div_assoc', eq_div_iff hy.ne]
  linear_combination (z.1 + z.2) * hxy + (x.1 + x.2) * hyz

end Prod
