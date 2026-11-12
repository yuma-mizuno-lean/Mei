/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.RestrictScalars
public import Mei.Algebra.Lie.Logarithmic.Specialization

/-!
# Coefficient specializations of tropical vertex wall spaces

Let `φ : R → S` be a homomorphism of algebras over a common base ring `K`, and `χ` a
multiplicative weight on a coefficient monoid `Q` containing the allowed degrees. The twisted
coefficient specialization `z^n ∂_m ↦ χ(n) z^n ∂_(φ ∘ m)` of the positive tropical vertex
algebras (`LogarithmicVectorField.coefficientMonoidGradedLieHom`) preserves every tropical vertex
wall space, viewed over `K` (`LogarithmicVectorField.coefficientMonoidGradedLieHom_mem_wall`):
it keeps the degree and sends the generator `z^n ∂_m` of an integral normal `m` to a scalar
multiple of the generator over `S`. Specializations may kill labels. This supplies the
wall-preservation hypothesis of the coefficient changes of directed diagrams in
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.RestrictScalars`. The twisted coefficient
changes follow Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(i), arXiv:1503.06183v5.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

namespace Mei.LogarithmicVectorField

variable {K R S Γ Λ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [Algebra ℚ R] [Algebra ℚ S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (φ : R →ₐ[K] S) (Q : AddSubmonoid Γ)
  (χ : Multiplicative Q →* S) (hQ : d.monoid ≤ Q)

/-- The twisted coefficient specialization preserves every tropical vertex wall space, viewed
over the common base ring. -/
theorem coefficientMonoidGradedLieHom_mem_wall (n : Γ) (m : Λ →+ ℤ)
    (x : tropicalVertexLieAlgebra (R := R) d ρ)
    (hx : x ∈ ((tropicalVertexWallSpaces (R := R) d ρ).restrictScalars K).wall n m) :
    coefficientMonoidGradedLieHom ρ φ Q χ d hQ x ∈
      ((tropicalVertexWallSpaces (R := S) d ρ).restrictScalars K).wall n m := by
  rw [DirectedWallSpaces.restrictScalars_wall, Submodule.restrictScalars_mem] at hx ⊢
  by_cases hm : m (ρ n) = 0
  · obtain ⟨r, hr⟩ := (mem_tropicalVertexWallSpaces_iff_of_tangent d ρ n m hm x).mp hx
    refine (mem_tropicalVertexWallSpaces_iff_of_tangent d ρ n m hm _).mpr ?_
    by_cases hn : n ∈ d.monoid
    · refine ⟨χ (.ofAdd ⟨n, hQ hn⟩) * φ r, ?_⟩
      rw [coe_coefficientMonoidGradedLieHom_of_homogeneous ρ φ Q χ d hQ hn x _
        ((map_smul (single ρ n) r _).trans hr), ← map_smul]
      congr 1
      ext l
      simp [mul_assoc]
    · -- Outside the allowed degrees the positive wall spaces vanish.
      have h0 := (tropicalVertexWallSpaces (R := R) d ρ).wall_le_piece n m hx
      rw [IsPositiveGrading.eq_bot (d := d) (ℒ := tropicalVertexGrading (R := R) d ρ) n
        (Or.inl hn), Submodule.mem_bot] at h0
      exact ⟨0, by rw [h0, map_zero, zero_smul, ZeroMemClass.coe_zero]⟩
  · rw [mem_tropicalVertexWallSpaces_iff, wallSubmodule_of_nontangent ρ n m hm,
      Submodule.mem_bot] at hx ⊢
    rw [show x = 0 from Subtype.ext hx, map_zero, ZeroMemClass.coe_zero]

end Mei.LogarithmicVectorField
