/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Action
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Basic
public import Mei.Algebra.Lie.Logarithmic.Coefficient

/-!
# Tropical vertex wall annihilation

The tropical vertex coefficient action annihilates every homogeneous coefficient
piece tangent to a wall normal. The action and its exponent-grading instance live
in the algebraic coefficient-action module; this module connects that action to
the logarithmic directed wall spaces. Its degree indices may be any additive
commutative monoid, and the coefficient action need not be faithful.

The logarithmic action and tangent-annihilation condition follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§2.1 and Example 2.1(i) (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.TropicalVertexCoefficientAction

open _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Λ]

section Annihilation

variable [AddCommMonoid Γ] [Algebra ℚ R]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (Q : AddSubmonoid Γ)
  [Fact (d.monoid ≤ Q)]

/-- Tropical vertex wall fields kill every homogeneous coefficient tangent to
their integral normal, including when the coefficient action is not faithful. -/
scoped instance instIsWallAnnihilating :
    IsWallAnnihilating (tropicalVertexWallSpaces (R := R) d ρ)
      (gradeBy R Q.subtype) where
  lie_eq_zero := by
    intro n p m x a hx ha hp
    by_cases hx0 : x = 0
    · simp [hx0]
    have hn : n ∈ d.monoid := by
      by_contra hn
      have hmem := (tropicalVertexWallSpaces (R := R) d ρ).wall_le_piece n m hx
      rw [IsPositiveGrading.eq_bot (d := d)
        (ℒ := tropicalVertexGrading (R := R) d ρ) n (Or.inl hn), Submodule.mem_bot] at hmem
      exact hx0 hmem
    have hm := (tropicalVertexWallSpaces (R := R) d ρ).normal_apply_eq_zero hx hx0
    obtain ⟨c, hc⟩ := (mem_tropicalVertexWallSpaces_iff_of_tangent d ρ n m hm x).mp hx
    have hc' : LogarithmicVectorField.single ρ n
        (c • (Int.castAddHom R).comp m) = x.val := by
      simpa only [map_smul] using hc
    rw [lie_eq, tropicalVertexCoefficientAction_of_homogeneous d ρ Q Fact.out hn x _ hc']
    rw [← sum_coeff_single a, Finsupp.sum, map_sum]
    apply Finset.sum_eq_zero
    intro q hq
    have hq' : (q : Γ) = p := ha q hq
    simp only [AddMonoidAlgebra.monomialDerivation_single, AddMonoidHom.comp_apply,
      AddSubmonoid.subtype_apply, AddMonoidHom.smul_apply, hq', hp, map_zero,
      smul_zero, mul_zero, single_zero]

end Annihilation

end Mei.TropicalVertexCoefficientAction
