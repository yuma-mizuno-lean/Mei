/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Skew.Grading

/-!
# Radical degrees of the skew Lie algebra

Let `β` be an alternating form on an abelian group `Γ`. A degree `n` lies in the radical of
`β` when `β(-, n) = 0`. In the skew Lie algebra the bracket `[X_a, X_b] = β(b, a) X_(a+b)`
only depends on the total degree in this respect: `β(b, a) = β(b, a + b)`. Hence two
homogeneous elements whose degrees add up to a radical degree commute
(`SkewLieAlgebra.lie_eq_zero_of_flip_add_eq_zero`), even when neither degree is radical.

The action `X_n(z^p) = β(p, n) z^(n+p)` on the monoid algebra kills every generator of radical
degree (`SkewLieAlgebra.action_single_eq_zero_of_flip_eq_zero`). For the zero form the whole
action is zero (`SkewLieAlgebra.action_eq_zero_of_eq_zero`), although the skew Lie algebra
keeps a free generator in every degree.

The bracket and action conventions are those of Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1 (arXiv:1411.1394v2).
-/

public section

open TauCeti (PositiveDegrees)

namespace Mei.SkewLieAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt)

/-- Two generators whose degrees add up to a radical degree commute. -/
theorem single_bracket_single_eq_zero_of_flip_add_eq_zero {a b : Γ}
    (hab : β.flip (a + b) = 0) (r s : R) :
    ⁅single β hβ a r, single β hβ b s⁆ = 0 := by
  -- The structure constant `β(b, a)` is `β(b, a + b)`, since `β(b, b) = 0`.
  have hb : β b a = 0 := by
    have he := LinearMap.congr_fun hab b
    rwa [LinearMap.flip_apply, map_add, hβ b, add_zero] at he
  rw [single_bracket_single, hb, mul_zero, map_zero]

/-- Homogeneous elements whose degrees add up to a radical degree commute. -/
theorem lie_eq_zero_of_flip_add_eq_zero {a b : Γ} (hab : β.flip (a + b) = 0)
    {x y : SkewLieAlgebra β hβ} (hx : x ∈ grade β hβ a) (hy : y ∈ grade β hβ b) :
    ⁅x, y⁆ = 0 := by
  obtain ⟨r, rfl⟩ := (mem_grade_iff β hβ a x).mp hx
  obtain ⟨s, rfl⟩ := (mem_grade_iff β hβ b y).mp hy
  exact single_bracket_single_eq_zero_of_flip_add_eq_zero β hβ hab r s

/-- In the positive skew Lie algebra, homogeneous elements whose degrees add up to a radical
degree commute. -/
theorem positiveGrading_lie_eq_zero_of_flip_add_eq_zero (d : PositiveDegrees Γ) {a b : Γ}
    (hab : β.flip (a + b) = 0) {x y : positiveLieAlgebra β hβ d}
    (hx : x ∈ positiveGrading β hβ d a) (hy : y ∈ positiveGrading β hβ d b) :
    ⁅x, y⁆ = 0 :=
  Subtype.ext (lie_eq_zero_of_flip_add_eq_zero β hβ hab
    ((mem_positiveGrading_iff β hβ d a x).mp hx) ((mem_positiveGrading_iff β hβ d b y).mp hy))

/-- A generator of radical degree acts by zero on the monoid algebra. -/
theorem action_single_eq_zero_of_flip_eq_zero {n : Γ} (hn : β.flip n = 0) (r : R) :
    action β hβ (single β hβ n r) = 0 := by
  have h0 : (β.flip n).toAddMonoidHom = 0 := by
    ext p
    simp [hn]
  rw [action_single, h0, map_zero, smul_zero]

/-- Every generator of the zero form acts by zero: the action of the zero form vanishes,
although the skew Lie algebra keeps a free generator in every degree. -/
theorem action_eq_zero_of_eq_zero (hβ0 : β = 0) : action β hβ = 0 := by
  ext x : 1
  rw [zero_apply]
  induction x using induction_on β hβ with
  | h0 => exact map_zero _
  | hs n r =>
    exact action_single_eq_zero_of_flip_eq_zero β hβ (by ext; simp [hβ0]) r
  | ha x y hx hy => rw [map_add, hx, hy, add_zero]

end Mei.SkewLieAlgebra
