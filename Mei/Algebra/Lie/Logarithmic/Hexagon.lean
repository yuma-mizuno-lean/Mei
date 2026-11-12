/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pentagon

/-!
# The hexagon identity of type `B₂` in the tropical vertex group

Let `n₁, n₂` be nonzero allowed degrees and `μ₁, μ₂` integral characters of the spatial lattice
with `μ₁(ρ n₁) = μ₂(ρ n₂) = 0`, `μ₁(ρ n₂) = -1` and `μ₂(ρ n₁) = 1`, and write `θ[μ, n, c]` for
the binomial label `exp(log(1 + c z^n) ∂_μ)` (`Mei.binomialLabel`). Its square `θ[μ, n, c]^2` is
the wall-crossing automorphism of the wall function `(1 + c z^n)^2`
(`Mei.completedBCHAction_binomialLabel_pow`). For all coefficients `c₁, c₂` the completed tropical
vertex group satisfies the six-factor identity
`θ[μ₂, n₂, c₂]^2 θ[μ₁, n₁, c₁] =
  θ[μ₁, n₁, c₁] θ[μ₁ + μ₂, n₁ + n₂, c₁ c₂]^2 θ[μ₁ + 2 μ₂, n₁ + 2 n₂, c₁ c₂^2] θ[μ₂, n₂, c₂]^2`
(`Mei.binomialLabel_hexagon`), the analogue of type `B₂` of the pentagon identity
`Mei.binomialLabel_pentagon`. No condition on the positive degree data, on the spatial
projection `ρ` or on the coefficients is imposed beyond these pairings; the degrees and lattices
live in `Type`.

This is the case `ℓ₁ = 1`, `ℓ₂ = 2` of the commutator of `θ_{(1 + t x)^{ℓ₁}}` and
`θ_{(1 + t y)^{ℓ₂}}` in Gross–Pandharipande–Siebert, *Quivers, curves, and the tropical vertex*,
Example 1.6 (arXiv:0902.0779v3), here with coefficients: the two outgoing rays carry the wall
functions `(1 + c₁ c₂ z^{n₁ + n₂})^2` and `1 + c₁ c₂^2 z^{n₁ + 2 n₂}`. The identity follows from
two applications of the pentagon identity, first to `(μ₁, n₁)` and `(μ₂, n₂)` and then to
`(μ₁ + μ₂, n₁ + n₂)` and `(μ₂, n₂)`.
-/

public section

noncomputable section

namespace Mei

/-- **Hexagon identity of type `B₂` in the tropical vertex group.** Let `n₁, n₂` be nonzero
allowed degrees and `μ₁, μ₂` integral characters with `μ₁(ρ n₁) = μ₂(ρ n₂) = 0`,
`μ₁(ρ n₂) = -1` and `μ₂(ρ n₁) = 1`. For all coefficients `c₁, c₂`, the binomial labels
`θ[μ, n, c] = exp(log(1 + c z^n) ∂_μ)` satisfy
`θ[μ₂, n₂, c₂]^2 θ[μ₁, n₁, c₁] =
  θ[μ₁, n₁, c₁] θ[μ₁ + μ₂, n₁ + n₂, c₁ c₂]^2 θ[μ₁ + 2 μ₂, n₁ + 2 n₂, c₁ c₂^2] θ[μ₂, n₂, c₂]^2`. -/
theorem binomialLabel_hexagon {R : Type*} [CommRing R] [Algebra ℚ R] {Γ Λ : Type}
    [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ] (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)
    {n₁ n₂ : Γ} (hn₁ : n₁ ∈ d.monoid) (hn₂ : n₂ ∈ d.monoid) (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0)
    {μ₁ μ₂ : Λ →+ ℤ} (h₁₁ : μ₁ (ρ n₁) = 0) (h₂₂ : μ₂ (ρ n₂) = 0) (h₁₂ : μ₁ (ρ n₂) = -1)
    (h₂₁ : μ₂ (ρ n₁) = 1) (c₁ c₂ : R) :
    binomialLabel d ρ μ₂ hn₂ hn₂0 h₂₂ c₂ ^ 2 * binomialLabel d ρ μ₁ hn₁ hn₁0 h₁₁ c₁ =
      binomialLabel d ρ μ₁ hn₁ hn₁0 h₁₁ c₁ *
        binomialLabel d ρ (μ₁ + μ₂) (add_mem hn₁ hn₂) (d.add_ne_zero hn₁ hn₂ hn₁0)
          (by simp [h₁₁, h₁₂, h₂₁, h₂₂]) (c₁ * c₂) ^ 2 *
        binomialLabel d ρ (μ₁ + 2 • μ₂) (add_mem hn₁ (nsmul_mem hn₂ 2))
          (d.add_ne_zero hn₁ (nsmul_mem hn₂ 2) hn₁0) (by simp [h₁₁, h₁₂, h₂₁, h₂₂])
          (c₁ * c₂ ^ 2) *
        binomialLabel d ρ μ₂ hn₂ hn₂0 h₂₂ c₂ ^ 2 := by
  -- Write `A, B, C` for the labels of `(μ₁, n₁)`, `(μ₂, n₂)` and `(μ₁ + μ₂, n₁ + n₂)`, and `E` for
  -- that of `(μ₁ + 2 μ₂, n₁ + 2 n₂)`. The pentagon identities `B A = A C B` and `B C = C E B` give
  -- `B² A = B A C B = A C (B C) B = A C² E B²`.
  have hA := binomialLabel_pentagon d ρ hn₁ hn₂ hn₁0 hn₂0 h₁₁ h₂₂ h₁₂ h₂₁ c₁ c₂
  have hC := binomialLabel_pentagon (μ₁ := μ₁ + μ₂) d ρ (add_mem hn₁ hn₂) hn₂
    (d.add_ne_zero hn₁ hn₂ hn₁0) hn₂0 (by simp [h₁₁, h₁₂, h₂₁, h₂₂]) h₂₂ (by simp [h₁₂, h₂₂])
    (by simp [h₂₁, h₂₂]) (c₁ * c₂) c₂
  have hE : binomialLabel d ρ (μ₁ + μ₂ + μ₂) (add_mem (add_mem hn₁ hn₂) hn₂)
      (d.add_ne_zero (add_mem hn₁ hn₂) hn₂ (d.add_ne_zero hn₁ hn₂ hn₁0))
      (by simp [h₁₁, h₁₂, h₂₁, h₂₂]) (c₁ * c₂ * c₂) =
      binomialLabel d ρ (μ₁ + 2 • μ₂) (add_mem hn₁ (nsmul_mem hn₂ 2))
        (d.add_ne_zero hn₁ (nsmul_mem hn₂ 2) hn₁0) (by simp [h₁₁, h₁₂, h₂₁, h₂₂])
        (c₁ * c₂ ^ 2) := by
    congr 1 <;> first | abel | ring
  rw [hE] at hC
  set A := binomialLabel d ρ μ₁ hn₁ hn₁0 h₁₁ c₁
  set B := binomialLabel d ρ μ₂ hn₂ hn₂0 h₂₂ c₂
  set C := binomialLabel d ρ (μ₁ + μ₂) (add_mem hn₁ hn₂) (d.add_ne_zero hn₁ hn₂ hn₁0)
    (by simp [h₁₁, h₁₂, h₂₁, h₂₂]) (c₁ * c₂)
  set E := binomialLabel d ρ (μ₁ + 2 • μ₂) (add_mem hn₁ (nsmul_mem hn₂ 2))
    (d.add_ne_zero hn₁ (nsmul_mem hn₂ 2) hn₁0) (by simp [h₁₁, h₁₂, h₂₁, h₂₂]) (c₁ * c₂ ^ 2)
  have hA' (x) : B * (A * x) = A * (C * (B * x)) := by
    rw [← mul_assoc, hA]
    simp only [mul_assoc]
  have hC' (x) : B * (C * x) = C * (E * (B * x)) := by
    rw [← mul_assoc, hC]
    simp only [mul_assoc]
  calc B ^ 2 * A = B * (A * (C * B)) := by rw [sq, mul_assoc, hA, mul_assoc]
    _ = A * (C * (C * (E * (B * B)))) := by rw [hA', hC']
    _ = _ := by simp only [sq, mul_assoc]

end Mei
