/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Instances.Sign
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith

/-!
# Local constancy of signs

Near a point where a continuous function to a linear order does not vanish, its sign is
constant (`ContinuousAt.eventually_sign_eq`).

In a linearly ordered field with the order topology, for `x ≠ 0` and any `y`, small
multiples `σ * y` have absolute value smaller than `|x|` (`eventually_abs_mul_lt`), so that
`x + σ * y` has the sign of `x` (`eventually_pos_add_mul`, `eventually_add_mul_neg`). The bound
on `|σ * y|` holds for small positive `σ`, with `x ≠ 0` as a
hypothesis inside the filter (`eventually_nhdsGT_imp_abs_mul_lt`).

Consequently, along a line `s ↦ θ ± s • w` a linear form keeps a strict sign it has at `θ`
for small `s > 0` (`eventually_neg_line`, `eventually_pos_line`), and changes sign across its
kernel in a direction `w` with `f w > 0` (`eventually_pos_neg_line`). If crossing at `θ` in every
direction `w` with `ℓ w > 0` multiplies a function `T` to a group on the right by `X`, then
crossing in any direction `v` with `ℓ v ≠ 0` changes `T` by `X^{∓1}`
(`eventually_inv_mul_eq_zpow`).
-/

public section

open Filter Topology

namespace ContinuousAt

variable {X α : Type*} [TopologicalSpace X] [Zero α] [LinearOrder α] [TopologicalSpace α]
  [OrderTopology α] {f : X → α} {x : X}

/-- Near a point where a continuous function does not vanish, its sign is constant. -/
theorem eventually_sign_eq (hf : ContinuousAt f x) (h : f x ≠ 0) :
    ∀ᶠ y in 𝓝 x, SignType.sign (f y) = SignType.sign (f x) := by
  have hc := (continuousAt_sign_of_ne_zero h).comp hf
  rw [ContinuousAt, nhds_discrete SignType, tendsto_pure] at hc
  exact hc

end ContinuousAt

namespace Mei

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  [OrderTopology K]

/-- For `x ≠ 0`, small multiples `σ * y` have absolute value smaller than `|x|`. -/
theorem eventually_abs_mul_lt {x : K} (hx : x ≠ 0) (y : K) :
    ∀ᶠ σ in 𝓝 (0 : K), |σ * y| < |x| := by
  have hlim : Tendsto (fun σ : K => |σ * y|) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_id.mul continuous_const).abs.tendsto (0 : K) :
      Tendsto (fun σ : K => |σ * y|) (𝓝 0) (𝓝 |0 * y|))
  exact hlim.eventually_lt_const (abs_pos.mpr hx)

/-- For `x > 0` and any `y`, `x + σ * y` is positive for small `σ`. -/
theorem eventually_pos_add_mul {x : K} (hx : 0 < x) (y : K) :
    ∀ᶠ σ in 𝓝 (0 : K), 0 < x + σ * y := by
  filter_upwards [eventually_abs_mul_lt hx.ne' y] with σ hσ
  rw [abs_of_pos hx] at hσ
  calc 0 < x - |σ * y| := sub_pos.mpr hσ
    _ ≤ x + σ * y := by
      rw [sub_eq_add_neg]
      exact add_le_add_right (neg_abs_le _) x

/-- For `x < 0` and any `y`, `x + σ * y` is negative for small `σ`. -/
theorem eventually_add_mul_neg {x : K} (hx : x < 0) (y : K) :
    ∀ᶠ σ in 𝓝 (0 : K), x + σ * y < 0 := by
  filter_upwards [eventually_abs_mul_lt hx.ne y] with σ hσ
  rw [abs_of_neg hx] at hσ
  calc x + σ * y ≤ x + |σ * y| := add_le_add_right (le_abs_self _) x
    _ < x + -x := add_lt_add_right hσ x
    _ = 0 := add_neg_cancel x

/-- For small positive `σ`, if `x ≠ 0`, then `σ * y` has absolute value smaller than `|x|`. -/
theorem eventually_nhdsGT_imp_abs_mul_lt (x y : K) :
    ∀ᶠ σ in 𝓝[>] (0 : K), x ≠ 0 → |σ * y| < |x| := by
  by_cases hx : x = 0
  · exact Eventually.of_forall fun _ hne => absurd hx hne
  · exact Eventually.mono (nhdsWithin_le_nhds (eventually_abs_mul_lt hx y)) fun _ hσ _ => hσ

section Line

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Along a line through a point where a linear form is negative, it stays negative on both
sides for all small parameters. -/
theorem eventually_neg_line {f : V →ₗ[K] K} {θ : V} (hf : f θ < 0) (w : V) :
    ∀ᶠ s in 𝓝[>] (0 : K), f (θ + s • w) < 0 ∧ f (θ - s • w) < 0 := by
  have hle : 𝓝[>] (0 : K) ≤ 𝓝 0 := nhdsWithin_le_nhds
  filter_upwards [hle (eventually_add_mul_neg hf (f w)), hle (eventually_add_mul_neg hf (-f w))]
    with s h₁ h₂
  rw [mul_neg, ← sub_eq_add_neg] at h₂
  simpa only [map_add, map_sub, map_smul, smul_eq_mul] using ⟨h₁, h₂⟩

/-- Along a line through a point where a linear form is positive, it stays positive on both
sides for all small parameters. -/
theorem eventually_pos_line {f : V →ₗ[K] K} {θ : V} (hf : 0 < f θ) (w : V) :
    ∀ᶠ s in 𝓝[>] (0 : K), 0 < f (θ + s • w) ∧ 0 < f (θ - s • w) := by
  simpa only [LinearMap.neg_apply, neg_lt_zero] using
    eventually_neg_line (f := -f) (by rwa [LinearMap.neg_apply, neg_lt_zero]) w

omit [OrderTopology K] in
/-- Crossing the kernel of a linear form `f` in a direction `w` with `f w > 0`, the form is
positive after and negative before the crossing. -/
theorem eventually_pos_neg_line {f : V →ₗ[K] K} {θ w : V} (hf : f θ = 0)
    (hw : 0 < f w) : ∀ᶠ s in 𝓝[>] (0 : K), 0 < f (θ + s • w) ∧ f (θ - s • w) < 0 := by
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have := mul_pos hs hw
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hf]
  constructor <;> linarith

omit [OrderTopology K] in
/-- Let `T` be a function on `V` such that, near `θ`, crossing in every direction `w` with
`ℓ w > 0` multiplies `T` on the right by `X`. Then crossing in any direction `v` with
`ℓ v ≠ 0` gives `T (θ + s • v)⁻¹ * T (θ - s • v) = X⁻¹` if `ℓ v > 0` and `X` if `ℓ v < 0`,
for all small `s > 0`. -/
theorem eventually_inv_mul_eq_zpow {G : Type*} [Group G] {T : V → G} {θ v : V}
    {ℓ : V →ₗ[K] K} {X : G}
    (hT : ∀ w, 0 < ℓ w → ∀ᶠ s in 𝓝[>] (0 : K), T (θ + s • w) = T (θ - s • w) * X)
    (hv : ℓ v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : K), (T (θ + s • v))⁻¹ * T (θ - s • v) =
      X ^ (if 0 < ℓ v then -1 else 1 : ℤ) := by
  rcases hv.lt_or_gt with hv | hv
  · filter_upwards [hT (-v) (by simpa using hv)] with s hs
    rw [smul_neg, ← sub_eq_add_neg, sub_neg_eq_add] at hs
    rw [hs, ite_eq_right (not_lt.mpr hv.le)]
    group
  · filter_upwards [hT v hv] with s hs
    rw [hs, ite_eq_left hv]
    group

end Line

end Mei
