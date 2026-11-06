/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Fan

/-!
# Consistency of the pentagon configuration

Let `ℓ₁, ℓ₂` be the real extensions of two integral normals `μ₁, μ₂`, neither of whose kernels
contains the other. A directed diagram is in *pentagon configuration*
(`DirectedDiagram.IsPentagonConfiguration`) when it has exactly three walls: the hyperplanes
`{ℓ₁ = 0}` and `{ℓ₂ = 0}`, cooriented by `μ₁` and `μ₂`, and the half-hyperplane
`{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}`, cooriented by `μ₁ + μ₂`. Write `A`, `B` and `C` for their labels. If
they satisfy the pentagon relation `B A = A C B`, the diagram is consistent
(`DirectedDiagram.IsPentagonConfiguration.consistent`).

A pentagon configuration is a fan configuration with the single outgoing wall
`{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` (`DirectedDiagram.IsPentagonConfiguration.isFanConfiguration`), and its
consistency is the case of one outgoing wall of `DirectedDiagram.IsFanConfiguration.consistent`.
Walls whose labels vanish at an order are allowed.

For dilogarithm labels the relation is the pentagon identity, and the configuration is the
consistent scattering diagram of type `A₂` (Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1, arXiv:1411.1394v2); see
`Mei.Geometry.ScatteringDiagram.Skew.Principal.Pentagon`.
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

/-- A directed diagram is in *pentagon configuration* with walls `j₁, j₂, j₃` and integral
normals `μ₁, μ₂`, with real extensions `ℓ₁, ℓ₂`, when `j₁, j₂, j₃` are all its walls, the walls
`j₁` and `j₂` are the hyperplanes `{ℓ₁ = 0}` and `{ℓ₂ = 0}` cooriented by `μ₁` and `μ₂`, the
wall `j₃` is the half-hyperplane `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` cooriented by `μ₁ + μ₂`, and each of
the kernels of `ℓ₁` and `ℓ₂` contains a vector outside the other. -/
structure IsPentagonConfiguration (j₁ j₂ j₃ : ι) (μ₁ μ₂ : Λ →+ ℤ) : Prop where
  /-- Every wall is one of the three. -/
  eq_or_eq_or_eq (j : ι) : j = j₁ ∨ j = j₂ ∨ j = j₃
  /-- The first wall is cooriented by `μ₁`. -/
  normal_fst : (D.wall j₁).normal = μ₁
  /-- The second wall is cooriented by `μ₂`. -/
  normal_snd : (D.wall j₂).normal = μ₂
  /-- The half-hyperplane wall is cooriented by `μ₁ + μ₂`. -/
  normal_half : (D.wall j₃).normal = μ₁ + μ₂
  /-- The first wall is the hyperplane `{ℓ₁ = 0}`. -/
  support_fst : (D.wall j₁).support = {x | h.realCharacter μ₁ x = 0}
  /-- The second wall is the hyperplane `{ℓ₂ = 0}`. -/
  support_snd : (D.wall j₂).support = {x | h.realCharacter μ₂ x = 0}
  /-- The third wall is the half-hyperplane `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}`. -/
  support_half : (D.wall j₃).support =
    {x | h.realCharacter μ₁ x + h.realCharacter μ₂ x = 0 ∧ 0 ≤ h.realCharacter μ₁ x}
  /-- The kernel of `ℓ₁` is not contained in that of `ℓ₂`. -/
  exists_fst : ∃ x, h.realCharacter μ₁ x = 0 ∧ h.realCharacter μ₂ x ≠ 0
  /-- The kernel of `ℓ₂` is not contained in that of `ℓ₁`. -/
  exists_snd : ∃ x, h.realCharacter μ₂ x = 0 ∧ h.realCharacter μ₁ x ≠ 0

namespace IsPentagonConfiguration

variable {D} {j₁ j₂ j₃ : ι} {μ₁ μ₂ : Λ →+ ℤ} (hD : D.IsPentagonConfiguration j₁ j₂ j₃ μ₁ μ₂)
include hD

/-- The first wall is not the half-hyperplane wall. -/
private theorem fst_ne_half : j₁ ≠ j₃ := by
  rintro rfl
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  have he := congrArg (fun μ => h.realCharacter μ x) (hD.normal_fst.symm.trans hD.normal_half)
  simp only [map_add, LinearMap.add_apply, hx₁, zero_add] at he
  exact hx₂ he.symm

/-- The second wall is not the half-hyperplane wall. -/
private theorem snd_ne_half : j₂ ≠ j₃ := by
  rintro rfl
  obtain ⟨y, hy₂, hy₁⟩ := hD.exists_snd
  have he := congrArg (fun μ => h.realCharacter μ y) (hD.normal_snd.symm.trans hD.normal_half)
  simp only [map_add, LinearMap.add_apply, hy₂, add_zero] at he
  exact hy₁ he.symm

/-- A pentagon configuration is a fan configuration whose only outgoing wall is the
half-hyperplane `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}`. -/
theorem isFanConfiguration : D.IsFanConfiguration j₁ j₂ μ₁ μ₂ where
  normal_fst := hD.normal_fst
  normal_snd := hD.normal_snd
  support_fst := hD.support_fst
  support_snd := hD.support_snd
  exists_apply_eq_of_ne j hj₁ hj₂ := by
    obtain rfl := (hD.eq_or_eq_or_eq j).resolve_left hj₁ |>.resolve_left hj₂
    exact ⟨1, 1, one_pos, one_pos, fun x => by simp [hD.normal_half]⟩
  support_of_ne j hj₁ hj₂ := by
    obtain rfl := (hD.eq_or_eq_or_eq j).resolve_left hj₁ |>.resolve_left hj₂
    rw [hD.support_half, hD.normal_half, map_add]
    rfl
  exists_fst := hD.exists_fst
  exists_snd := hD.exists_snd

/-- **Consistency of the pentagon configuration.** A directed diagram in pentagon configuration
whose labels `A, B, C` of the walls `{ℓ₁ = 0}`, `{ℓ₂ = 0}` and `{ℓ₁ + ℓ₂ = 0, ℓ₁ ≥ 0}` satisfy
`B A = A C B` is consistent. -/
theorem consistent (hpent : (D.wall j₂).label * (D.wall j₁).label =
    (D.wall j₁).label * (D.wall j₃).label * (D.wall j₂).label) : D.Consistent :=
  hD.isFanConfiguration.consistent fun k => by
    refine ⟨[j₃], List.nodup_singleton _, ?_, ?_, fun j _ hj₁ hj₂ => ?_,
      List.pairwise_singleton _ _, ?_⟩
    · simpa using hD.fst_ne_half
    · simpa using hD.snd_ne_half
    · obtain rfl := (hD.eq_or_eq_or_eq j).resolve_left hj₁ |>.resolve_left hj₂
      exact List.mem_singleton_self _
    · simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul]
        using congrArg (CompletedGroup.projection k) hpent

end IsPentagonConfiguration

end Mei.DirectedDiagram
