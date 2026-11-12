/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Fan

/-!
# Consistency of the hexagon configuration

Let `ℓ₁, ℓ₂` be the real extensions of two integral normals `μ₁, μ₂`, neither of whose kernels
contains the other. A directed diagram is in *hexagon configuration*
(`DirectedDiagram.IsHexagonConfiguration`) when it has exactly four walls: the hyperplanes
`{ℓ₁ = 0}` and `{ℓ₂ = 0}`, cooriented by `μ₁` and `μ₂`, and the half-hyperplanes
`{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` and `{ℓ₁ + 2 ℓ₂ = 0, ℓ₁ ≥ 0}`, cooriented by `μ₁ + μ₂` and `μ₁ + 2 μ₂`.
Write `A`, `B`, `C` and `E` for the labels of the four walls. If they satisfy the relation
`B A = A C E B`, the diagram is consistent
(`DirectedDiagram.IsHexagonConfiguration.consistent`).

A hexagon configuration is a fan configuration with the two outgoing walls
`{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` and `{ℓ₁ + 2 ℓ₂ = 0, ℓ₁ ≥ 0}`
(`DirectedDiagram.IsHexagonConfiguration.isFanConfiguration`), listed in the order in which the
positive side of the second, on `{ℓ₁ > 0}`, lies in that of the first, and its consistency is
the case of two outgoing walls of `DirectedDiagram.IsFanConfiguration.consistent`. Walls whose
labels vanish at an order are allowed.

For the binomial labels of `1 + c₁ z^{n₁}` and `(1 + c₂ z^{n₂})^2` the relation is the hexagon
identity `Mei.binomialLabel_hexagon`, and the configuration is the consistent scattering diagram of
type `B₂` (Gross–Pandharipande–Siebert, *Quivers, curves, and the tropical vertex*, Example 1.6,
arXiv:0902.0779v3); see `Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hexagon.Binomial`.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- A directed diagram is in *hexagon configuration* with walls `j₁, j₂, j₃, j₄` and integral
normals `μ₁, μ₂`, with real extensions `ℓ₁, ℓ₂`, when `j₁, j₂, j₃, j₄` are all its walls, the
walls `j₁` and `j₂` are the hyperplanes `{ℓ₁ = 0}` and `{ℓ₂ = 0}` cooriented by `μ₁` and `μ₂`,
the walls `j₃` and `j₄` are the half-hyperplanes `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` and
`{ℓ₁ + 2 ℓ₂ = 0, ℓ₁ ≥ 0}` cooriented by `μ₁ + μ₂` and `μ₁ + 2 μ₂`, and each of the kernels of `ℓ₁`
and `ℓ₂` contains a vector outside the other. -/
structure IsHexagonConfiguration (j₁ j₂ j₃ j₄ : ι) (μ₁ μ₂ : Λ →+ ℤ) : Prop where
  /-- Every wall is one of the four. -/
  eq_or_eq_or_eq_or_eq (j : ι) : j = j₁ ∨ j = j₂ ∨ j = j₃ ∨ j = j₄
  /-- The first wall is cooriented by `μ₁`. -/
  normal_fst : (D.wall j₁).normal = μ₁
  /-- The second wall is cooriented by `μ₂`. -/
  normal_snd : (D.wall j₂).normal = μ₂
  /-- The third wall is cooriented by `μ₁ + μ₂`. -/
  normal_add : (D.wall j₃).normal = μ₁ + μ₂
  /-- The fourth wall is cooriented by `μ₁ + 2 μ₂`. -/
  normal_add_two : (D.wall j₄).normal = μ₁ + 2 • μ₂
  /-- The first wall is the hyperplane `{ℓ₁ = 0}`. -/
  support_fst : (D.wall j₁).support = {x | h.realCharacter μ₁ x = 0}
  /-- The second wall is the hyperplane `{ℓ₂ = 0}`. -/
  support_snd : (D.wall j₂).support = {x | h.realCharacter μ₂ x = 0}
  /-- The third wall is the half-hyperplane `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}`. -/
  support_add : (D.wall j₃).support =
    {x | h.realCharacter μ₁ x + h.realCharacter μ₂ x = 0 ∧ 0 ≤ h.realCharacter μ₁ x}
  /-- The fourth wall is the half-hyperplane `{ℓ₁ + 2 ℓ₂ = 0, ℓ₁ ≥ 0}`. -/
  support_add_two : (D.wall j₄).support =
    {x | h.realCharacter μ₁ x + 2 * h.realCharacter μ₂ x = 0 ∧ 0 ≤ h.realCharacter μ₁ x}
  /-- The kernel of `ℓ₁` is not contained in that of `ℓ₂`. -/
  exists_fst : ∃ x, h.realCharacter μ₁ x = 0 ∧ h.realCharacter μ₂ x ≠ 0
  /-- The kernel of `ℓ₂` is not contained in that of `ℓ₁`. -/
  exists_snd : ∃ x, h.realCharacter μ₂ x = 0 ∧ h.realCharacter μ₁ x ≠ 0

namespace IsHexagonConfiguration

variable {D} {j₁ j₂ j₃ j₄ : ι} {μ₁ μ₂ : Λ →+ ℤ}
  (hD : D.IsHexagonConfiguration j₁ j₂ j₃ j₄ μ₁ μ₂)
include hD

/-- The first wall is not the third. -/
theorem fst_ne_add : j₁ ≠ j₃ := fun he => by
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  have hx := congrArg (fun j => h.realCharacter (D.wall j).normal x) he
  exact hx₂ (by simpa [hD.normal_fst, hD.normal_add, hx₁] using hx.symm)

/-- The first wall is not the fourth. -/
theorem fst_ne_add_two : j₁ ≠ j₄ := fun he => by
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  have hx := congrArg (fun j => h.realCharacter (D.wall j).normal x) he
  exact hx₂ (by simpa [hD.normal_fst, hD.normal_add_two, hx₁] using hx.symm)

/-- The second wall is not the third. -/
theorem snd_ne_add : j₂ ≠ j₃ := fun he => by
  obtain ⟨y, hy₂, hy₁⟩ := hD.exists_snd
  have hy := congrArg (fun j => h.realCharacter (D.wall j).normal y) he
  exact hy₁ (by simpa [hD.normal_snd, hD.normal_add, hy₂] using hy.symm)

/-- The second wall is not the fourth. -/
theorem snd_ne_add_two : j₂ ≠ j₄ := fun he => by
  obtain ⟨y, hy₂, hy₁⟩ := hD.exists_snd
  have hy := congrArg (fun j => h.realCharacter (D.wall j).normal y) he
  exact hy₁ (by simpa [hD.normal_snd, hD.normal_add_two, hy₂] using hy.symm)

/-- The third wall is not the fourth. -/
theorem add_ne_add_two : j₃ ≠ j₄ := fun he => by
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  have hx : h.realCharacter μ₂ x = 2 * h.realCharacter μ₂ x := by
    simpa [hD.normal_add, hD.normal_add_two, hx₁] using
      congrArg (fun j => h.realCharacter (D.wall j).normal x) he
  exact hx₂ (by linarith)

/-- A hexagon configuration is a fan configuration whose outgoing walls are the half-hyperplanes
`{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` and `{ℓ₁ + 2 ℓ₂ = 0, ℓ₁ ≥ 0}`. -/
theorem isFanConfiguration : D.IsFanConfiguration j₁ j₂ μ₁ μ₂ where
  normal_fst := hD.normal_fst
  normal_snd := hD.normal_snd
  support_fst := hD.support_fst
  support_snd := hD.support_snd
  exists_apply_eq_of_ne j hj₁ hj₂ := by
    rcases (hD.eq_or_eq_or_eq_or_eq j).resolve_left hj₁ |>.resolve_left hj₂ with rfl | rfl
    · exact ⟨1, 1, one_pos, one_pos, fun x => by simp [hD.normal_add]⟩
    · exact ⟨1, 2, one_pos, two_pos, fun x => by simp [hD.normal_add_two]⟩
  support_of_ne j hj₁ hj₂ := by
    rcases (hD.eq_or_eq_or_eq_or_eq j).resolve_left hj₁ |>.resolve_left hj₂ with rfl | rfl
    · simp only [hD.support_add, hD.normal_add, map_add, LinearMap.add_apply]
    · simp only [hD.support_add_two, hD.normal_add_two, map_add, map_nsmul, LinearMap.add_apply,
        LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  exists_fst := hD.exists_fst
  exists_snd := hD.exists_snd

/-- **Consistency of the hexagon configuration.** A directed diagram in hexagon configuration
whose labels `A, B, C, E` of the walls `{ℓ₁ = 0}`, `{ℓ₂ = 0}`, `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` and
`{ℓ₁ + 2 ℓ₂ = 0, ℓ₁ ≥ 0}` satisfy `B A = A C E B` is consistent. -/
theorem consistent (hhex : (D.wall j₂).label * (D.wall j₁).label =
    (D.wall j₁).label * (D.wall j₃).label * (D.wall j₄).label * (D.wall j₂).label) :
    D.Consistent :=
  hD.isFanConfiguration.consistent fun k => by
    -- On `{ℓ₁ > 0}`, the positive side `{ℓ₁ + 2 ℓ₂ > 0}` of `j₄` lies in the positive side
    -- `{ℓ₁ + ℓ₂ > 0}` of `j₃`, so the outgoing walls are listed as `[j₃, j₄]`.
    refine ⟨[j₃, j₄], by simpa using hD.add_ne_add_two, ?_, ?_, fun j _ hj₁ hj₂ => ?_,
      List.pairwise_pair.mpr fun x hx₁ hx₄ => ?_, ?_⟩
    · simpa using ⟨hD.fst_ne_add, hD.fst_ne_add_two⟩
    · simpa using ⟨hD.snd_ne_add, hD.snd_ne_add_two⟩
    · rcases (hD.eq_or_eq_or_eq_or_eq j).resolve_left hj₁ |>.resolve_left hj₂ with rfl | rfl
      <;> simp
    · simp only [hD.normal_add, hD.normal_add_two, map_add, map_nsmul, LinearMap.add_apply,
        LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at hx₄ ⊢
      linarith
    · simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul,
        mul_assoc] using congrArg (CompletedGroup.projection k) hhex

end IsHexagonConfiguration

end Mei.DirectedDiagram
