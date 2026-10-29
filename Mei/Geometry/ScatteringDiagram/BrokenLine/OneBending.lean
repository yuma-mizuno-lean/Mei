/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Affine.FiniteRay.Moment
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# One-bending rank-two rectangles

In the rank-two scattering diagram of Burcroff–Lee–Mou with initial walls on the coordinate
axes of `ℝ²`, the outgoing walls are the rays `ℝ_{≤0} (a', b')` with `a', b' > 0`. A broken
line, modelled as a `FiniteAffineRay` whose direction is its exponent (its velocity is the
negative exponent), bending on the negative coordinate axes or on these rays and not on a
positive coordinate axis, bends only at points `-s • u` with `s > 0`, where the exponent
increases by a lattice vector `u ∈ ℕ²` (`RankTwo.IsNegativeRayBend`).

The rectangle `(d₁, d₂)` is *one-bending* for `(a, b)` and `k` (`RankTwo.OneBending`) if every
such broken line from exponent `(-d₁, -d₂)` to `(k a - d₁, k b - d₂)`, at any endpoint, has
exactly one bend, on `ℝ_{<0} (a, b)`; Burcroff–Lee–Mou use it for coprime `a, b > 0` and
`k ≥ 1`.

The position–velocity determinant of such a broken line is constant
(`FiniteAffineRay.form_eval_directionAt`). Hence consecutive bend positions, and so the exponent
increments `u_i`, rotate strictly in one direction, beginning on the side of the incoming
direction `(d₁, d₂)` facing `(a, b)`. If there are two bends, the first increment is a lattice
point `(a₁, b₁)` with `a₁ ≤ k a` and `b₁ ≤ k b` strictly between the directions `(d₁, d₂)` and
`(a, b)`. Writing `Δ = b d₁ - a d₂`, "strictly between" means that `d₁ b₁ - d₂ a₁` and
`a₁ b - b₁ a` both have the sign of `Δ`; for `b₁ > 0` this says that `a₁ / b₁` lies strictly
between `a / b` and `d₁ / d₂`. The absence of such lattice points therefore implies
one-bending (`RankTwo.oneBending_of_forall_not_between`). Coprimality of `a` and `b` is not
needed for this implication.

If `Δ > 0` and `d₂ ≥ Δ k b`, there is no such lattice point, and dually for `Δ < 0` and
`d₁ ≥ -Δ k a` (Burcroff–Lee–Mou, Corollary 5.14(2)). The rectangle `(6, 4)` with
`(a, b) = (1, 1)` and `k = 3` is one-bending by the lattice test, although `d₂ < Δ k b`.
The rectangle `(5, 3)` is not: the broken line with velocities `(5, 3)`, `(2, 1)`, `(2, 0)`
bends at `(-6, -4)` and on the negative `y`-axis, its first increment being the lattice point
`(3, 2)` between the directions `(5, 3)` and `(1, 1)`.

## Main definitions and statements

* `Mei.RankTwo.IsNegativeRayBend`: a bend at `-s • u` with exponent increment `u ∈ ℕ²`.
* `Mei.RankTwo.OneBending`: the one-bending property of a rectangle.
* `Mei.RankTwo.oneBending_of_forall_not_between`: the lattice test for one-bending.
* `Mei.RankTwo.oneBending_of_lt_of_le_snd`, `Mei.RankTwo.oneBending_of_lt_of_le_fst`:
  Burcroff–Lee–Mou, Corollary 5.14(2).

## References

* Amanda Burcroff, Kyungyong Lee, Lang Mou, *Positivity of generalized cluster scattering
  diagrams*, Definition 5.9, Lemma 5.13 and Corollary 5.14, arXiv:2503.03719v1.
-/

public section

open Finset

namespace Mei.RankTwo

open FiniteAffineRay

/-- A finite ray in `ℝ²` bends at time `t` on the open ray `ℝ_{<0} u` spanned by the negative
of a lattice vector `u ∈ ℕ²`, with exponent increment `u`; that is, its backward direction
increment at `t` is `-u`. These are the bends of broken lines on the negative coordinate axes
and on the outgoing rays `ℝ_{≤0} (a', b')` of a rank-two scattering diagram. -/
def IsNegativeRayBend (β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)) (t : ℝ) : Prop :=
  ∃ u : ℕ × ℕ, β.bends t = (-(u.1 : ℝ), -(u.2 : ℝ)) ∧
    ∃ s : ℝ, 0 < s ∧ β t = (-(s * u.1), -(s * u.2))

/-- The rectangle `(d₁, d₂)` is one-bending for `(a, b)` and `k` if every finite ray in `ℝ²`
with exponent `(-d₁, -d₂)` before its bends and `(k a - d₁, k b - d₂)` after them, all of whose
bends are `IsNegativeRayBend`, has exactly one bend, on the open ray `ℝ_{<0} (a, b)`. The
exponent of a broken line is the direction of its finite ray. -/
def OneBending (d₁ d₂ a b k : ℕ) : Prop :=
  ∀ β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ),
    β.incomingDirection = (-(d₁ : ℝ), -(d₂ : ℝ)) →
    β.direction = ((k : ℝ) * a - d₁, (k : ℝ) * b - d₂) →
    (∀ t ∈ β.bends.support, IsNegativeRayBend β t) →
    ∃ t : ℝ, β.bends = Finsupp.single t (-((k : ℝ) * a), -((k : ℝ) * b)) ∧
      ∃ s : ℝ, 0 < s ∧ β t = (-(s * a), -(s * b))

/-- The determinant form on `ℝ²`. -/
private def det : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.2 - x.2 * y.1) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

private theorem det_apply (x y : ℝ × ℝ) : det x y = x.1 * y.2 - x.2 * y.1 := by
  simp [det]

private theorem det_isAlt : det.IsAlt := fun x => by
  rw [det_apply]
  ring

/-- For vectors in the open half-plane `x₁ + x₂ < 0`, the relation "`det x y` is a positive
multiple of `c`" is transitive. -/
private theorem det_trans {c : ℝ} {x y z : ℝ × ℝ} (hx : x.1 + x.2 < 0) (hy : y.1 + y.2 < 0)
    (hz : z.1 + z.2 < 0) (hxy : ∃ α > 0, det x y = c * α) (hyz : ∃ α > 0, det y z = c * α) :
    ∃ α > 0, det x z = c * α := by
  obtain ⟨α, hα, hxy⟩ := hxy
  obtain ⟨γ, hγ, hyz⟩ := hyz
  refine ⟨(γ * (x.1 + x.2) + α * (z.1 + z.2)) / (y.1 + y.2),
    div_pos_of_neg_of_neg (by nlinarith) hy, ?_⟩
  rw [det_apply] at hxy hyz ⊢
  rw [mul_div_assoc', eq_div_iff hy.ne]
  linear_combination (z.1 + z.2) * hxy + (x.1 + x.2) * hyz

/-- The increment of a bend in the support has negative coordinate sum. -/
private theorem fst_add_snd_neg {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)} {t : ℝ}
    (h : IsNegativeRayBend β t) (ht : t ∈ β.bends.support) :
    (β.bends t).1 + (β.bends t).2 < 0 := by
  obtain ⟨u, hu, -⟩ := h
  have hne := Finsupp.mem_support_iff.mp ht
  rw [hu] at hne ⊢
  by_contra hle
  have h₁ := Nat.cast_nonneg (α := ℝ) u.1
  have h₂ := Nat.cast_nonneg (α := ℝ) u.2
  have h₁ : (u.1 : ℝ) = 0 := by linarith
  have h₂ : (u.2 : ℝ) = 0 := by linarith
  exact hne (by simp [h₁, h₂])

/-- A bend on a ray through the origin has zero moment. -/
private theorem det_eval_bends {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)} {t : ℝ}
    (h : IsNegativeRayBend β t) : det (β t) (β.bends t) = 0 := by
  obtain ⟨u, hu, s, -, hs⟩ := h
  rw [hu, hs, det_apply]
  ring

/-- Consecutive bends rotate in the sense of `-det β.endpoint β.direction`: if no bend lies
strictly between the bend times `s < t`, then `det (Δ_s) (Δ_t)` is a positive multiple of it. -/
private theorem exists_det_bends_eq_mul_of_consecutive {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)}
    (hβ : ∀ t ∈ β.bends.support, IsNegativeRayBend β t) {s t : ℝ} (hs : s ∈ β.bends.support)
    (ht : t ∈ β.bends.support) (hst : s < t) (hb : ∀ c ∈ β.bends.support, c ≤ s ∨ t ≤ c) :
    ∃ α > 0, det (β.bends s) (β.bends t) = -det β.endpoint β.direction * α := by
  obtain ⟨u, hu, σ, hσ, hpos⟩ := hβ s hs
  obtain ⟨u', hu', σ', hσ', hpos'⟩ := hβ t ht
  have h := form_eval_eval det_isAlt β (fun c hc => det_eval_bends (hβ c hc)) hst hb
  rw [hpos, hpos', det_apply] at h
  refine ⟨(t - s) / (σ * σ'), div_pos (by linarith) (by positivity), ?_⟩
  rw [hu, hu', det_apply, mul_div_assoc', eq_div_iff (by positivity)]
  linear_combination h

/-- Bends rotate in one direction: if `t₀` is the first bend and `t` is another bend, then
`det (Δ_{t₀}) (Δ_t)` is a positive multiple of `-det β.endpoint β.direction`. -/
private theorem exists_det_bends_eq_mul {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)}
    (hβ : ∀ t ∈ β.bends.support, IsNegativeRayBend β t) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ β.bends.support) (hmin : ∀ c ∈ β.bends.support, t₀ ≤ c)
    (ht : t ∈ β.bends.support) (hne : t ≠ t₀) :
    ∃ α > 0, det (β.bends t₀) (β.bends t) = -det β.endpoint β.direction * α := by
  classical
  -- induction on the number of bends before `t`, through the last bend `p` before `t`
  induction hn : (β.bends.support.filter (· < t)).card using Nat.strong_induction_on
    generalizing t with
  | _ n ih =>
  have hT : (β.bends.support.filter (· < t)).Nonempty :=
    ⟨t₀, mem_filter.mpr ⟨ht₀, (hmin t ht).lt_of_ne hne.symm⟩⟩
  set p := (β.bends.support.filter (· < t)).max' hT
  have hp : p ∈ β.bends.support.filter (· < t) := max'_mem _ _
  obtain ⟨hpS, hpt⟩ := mem_filter.mp hp
  have hstep := exists_det_bends_eq_mul_of_consecutive hβ hpS ht hpt fun c hc =>
    (lt_or_ge c t).imp (fun hct => le_max' _ c (mem_filter.mpr ⟨hc, hct⟩)) id
  by_cases hp₀ : p = t₀
  · rwa [hp₀] at hstep
  have hsub : β.bends.support.filter (· < p) ⊆ β.bends.support.filter (· < t) := fun c hc => by
    simp only [mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.trans hpt⟩
  have hlt : (β.bends.support.filter (· < p)).card < n :=
    hn ▸ card_lt_card ((ssubset_iff_of_subset hsub).mpr ⟨p, hp, by simp⟩)
  exact det_trans (fst_add_snd_neg (hβ t₀ ht₀) ht₀) (fst_add_snd_neg (hβ p hpS) hpS)
    (fst_add_snd_neg (hβ t ht) ht) (ih _ hlt hpS hp₀ rfl) hstep

/-- Every bend increment lies on the side of the incoming direction given by
`-det β.endpoint β.direction`, provided the incoming direction lies in the half-plane
`x₁ + x₂ < 0` of the increments. -/
private theorem exists_det_incomingDirection_bends_eq_mul
    {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)} (hβ : ∀ t ∈ β.bends.support, IsNegativeRayBend β t)
    (hin : β.incomingDirection.1 + β.incomingDirection.2 < 0) {t : ℝ}
    (ht : t ∈ β.bends.support) :
    ∃ α > 0, det β.incomingDirection (β.bends t) = -det β.endpoint β.direction * α := by
  have hS : β.bends.support.Nonempty := ⟨t, ht⟩
  set t₀ := β.bends.support.min' hS
  have ht₀ : t₀ ∈ β.bends.support := min'_mem _ hS
  have hmin : ∀ c ∈ β.bends.support, t₀ ≤ c := fun c hc => min'_le _ c hc
  -- the moment at the first bend is computed against the incoming direction
  have h₀ : ∃ α > 0, det β.incomingDirection (β.bends t₀) = -det β.endpoint β.direction * α := by
    obtain ⟨u, hu, σ, hσ, hpos⟩ := hβ t₀ ht₀
    have hcons := form_eval_directionAt det_isAlt β (fun c hc => det_eval_bends (hβ c hc)) t₀
    rw [β.directionAt_of_le_bends t₀ hmin, hpos, det_apply] at hcons
    refine ⟨1 / σ, by positivity, ?_⟩
    rw [hu, det_apply, ← hcons]
    field_simp
    ring
  by_cases htt : t = t₀
  · rwa [htt]
  · exact det_trans hin (fst_add_snd_neg (hβ t₀ ht₀) ht₀) (fst_add_snd_neg (hβ t ht) ht) h₀
      (exists_det_bends_eq_mul hβ ht₀ hmin ht htt)

/-- Under the hypotheses of `OneBending`, the bend increments add up to `-k (a, b)`. -/
private theorem sum_bends_eq {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)} {d₁ d₂ a b k : ℕ}
    (hin : β.incomingDirection = (-(d₁ : ℝ), -(d₂ : ℝ)))
    (hout : β.direction = ((k : ℝ) * a - d₁, (k : ℝ) * b - d₂)) :
    ∑ t ∈ β.bends.support, β.bends t = (-((k : ℝ) * a), -((k : ℝ) * b)) := by
  have h := β.incomingDirection_def
  rw [hin, hout, Finsupp.sum] at h
  rw [show ∑ t ∈ β.bends.support, β.bends t =
      (-(d₁ : ℝ), -(d₂ : ℝ)) - ((k : ℝ) * a - d₁, (k : ℝ) * b - d₂) by
    rw [h, add_sub_cancel_left]]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring

/-- Under the hypotheses of `OneBending` with at least one bend, `-det β.endpoint β.direction`
has the sign of `Δ = b d₁ - a d₂`: the increments, which add up to `k (a, b)`, all lie on the
side of the incoming direction given by `-det β.endpoint β.direction`. -/
private theorem neg_det_mul_pos {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)} {d₁ d₂ a b k : ℕ}
    (hk : 0 < k) (hΔ : (b * d₁ - a * d₂ : ℝ) ≠ 0)
    (hin : β.incomingDirection = (-(d₁ : ℝ), -(d₂ : ℝ)))
    (hout : β.direction = ((k : ℝ) * a - d₁, (k : ℝ) * b - d₂))
    (hβ : ∀ t ∈ β.bends.support, IsNegativeRayBend β t) (hS : β.bends.support.Nonempty)
    (hd : β.incomingDirection.1 + β.incomingDirection.2 < 0) :
    0 < -det β.endpoint β.direction * (b * d₁ - a * d₂ : ℝ) := by
  choose! α hα hdet using fun t (ht : t ∈ β.bends.support) =>
    exists_det_incomingDirection_bends_eq_mul hβ hd ht
  have hA : k * (b * d₁ - a * d₂ : ℝ) =
      -det β.endpoint β.direction * ∑ t ∈ β.bends.support, α t := by
    have h := congrArg (det β.incomingDirection) (sum_bends_eq hin hout)
    rw [map_sum, sum_congr rfl hdet, ← mul_sum, hin] at h
    simp only [det_apply] at h ⊢
    linear_combination -h
  have h : 0 < (-det β.endpoint β.direction * ∑ t ∈ β.bends.support, α t) *
      (b * d₁ - a * d₂ : ℝ) := by
    rw [← hA, mul_assoc]
    exact mul_pos (by exact_mod_cast hk) (mul_self_pos.mpr hΔ)
  nlinarith [sum_pos hα hS]

/-- Under the hypotheses of `OneBending`, if `t₀` is the first of at least two bends, then its
increment `u` is a lattice point with `u ≤ k (a, b)` strictly between the directions `(d₁, d₂)`
and `(a, b)`. -/
private theorem le_and_between_of_ne {β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)} {d₁ d₂ a b k : ℕ}
    (hk : 0 < k) (hin : β.incomingDirection = (-(d₁ : ℝ), -(d₂ : ℝ)))
    (hout : β.direction = ((k : ℝ) * a - d₁, (k : ℝ) * b - d₂))
    (hβ : ∀ t ∈ β.bends.support, IsNegativeRayBend β t)
    (hd : β.incomingDirection.1 + β.incomingDirection.2 < 0)
    (hsign : 0 < -det β.endpoint β.direction * (b * d₁ - a * d₂ : ℝ)) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ β.bends.support) (hmin : ∀ c ∈ β.bends.support, t₀ ≤ c)
    (ht : t ∈ β.bends.support) (htt : t ≠ t₀) {u : ℕ × ℕ}
    (hu : β.bends t₀ = (-(u.1 : ℝ), -(u.2 : ℝ))) :
    ((u.1 : ℝ) ≤ k * a ∧ (u.2 : ℝ) ≤ k * b) ∧
      ((0 : ℝ) < (b * d₁ - a * d₂) * (d₁ * u.2 - d₂ * u.1) ∧
        (0 : ℝ) < (b * d₁ - a * d₂) * (u.1 * b - u.2 * a)) := by
  have hsum := sum_bends_eq hin hout
  refine ⟨?_, ?_, ?_⟩
  · -- every increment has nonnegative coordinates and they add up to `k (a, b)`
    have hle : ∀ c ∈ β.bends.support, 0 ≤ -(β.bends c).1 ∧ 0 ≤ -(β.bends c).2 := by
      intro c hc
      obtain ⟨u, hu, -⟩ := hβ c hc
      simp [hu]
    have h₁ := single_le_sum (f := fun c => -(β.bends c).1) (fun c hc => (hle c hc).1) ht₀
    have h₂ := single_le_sum (f := fun c => -(β.bends c).2) (fun c hc => (hle c hc).2) ht₀
    simp only [sum_neg_distrib, ← Prod.fst_sum, ← Prod.snd_sum, hsum, hu, neg_neg] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · obtain ⟨α, hα, h⟩ := exists_det_incomingDirection_bends_eq_mul hβ hd ht₀
    rw [hin, hu, det_apply] at h
    have : (d₁ * u.2 - d₂ * u.1 : ℝ) = -det β.endpoint β.direction * α := by linarith
    rw [this]
    nlinarith
  · -- the later increments lie on the side of `u` given by `-det β.endpoint β.direction`
    choose! γ hγ hdet using fun c (hc : c ∈ β.bends.support.erase t₀) =>
      exists_det_bends_eq_mul hβ ht₀ hmin (mem_of_mem_erase hc) (ne_of_mem_erase hc)
    have hB : k * (u.1 * b - u.2 * a : ℝ) =
        -det β.endpoint β.direction * ∑ c ∈ β.bends.support.erase t₀, γ c := by
      have h := congrArg (det (β.bends t₀)) hsum
      rw [map_sum, ← add_sum_erase _ _ ht₀, det_isAlt.self_eq_zero, zero_add,
        sum_congr rfl hdet, ← mul_sum, hu] at h
      simp only [det_apply] at h ⊢
      linear_combination -h
    have h : 0 < (k : ℝ) * ((b * d₁ - a * d₂) * (u.1 * b - u.2 * a)) := by
      rw [mul_left_comm, hB]
      nlinarith [sum_pos (fun c hc => hγ c hc) ⟨t, mem_erase.mpr ⟨htt, ht⟩⟩]
    exact pos_of_mul_pos_right h (by positivity)

/-- The lattice test for one-bending: let `Δ = b d₁ - a d₂ ≠ 0` and `k > 0`. If no lattice point
`(a₁, b₁)` with `a₁ ≤ k a` and `b₁ ≤ k b` lies strictly between the directions `(d₁, d₂)` and
`(a, b)`, in the sense that `d₁ b₁ - d₂ a₁` and `a₁ b - b₁ a` both have the sign of `Δ`, then the
rectangle `(d₁, d₂)` is one-bending for `(a, b)` and `k`. -/
theorem oneBending_of_forall_not_between {d₁ d₂ a b k : ℕ} (hk : 0 < k) (hΔ : b * d₁ ≠ a * d₂)
    (hgap : ∀ a₁ b₁ : ℕ, a₁ ≤ k * a → b₁ ≤ k * b →
      ¬(0 < ((b * d₁ : ℤ) - a * d₂) * (d₁ * b₁ - d₂ * a₁) ∧
        0 < ((b * d₁ : ℤ) - a * d₂) * (a₁ * b - b₁ * a))) :
    OneBending d₁ d₂ a b k := by
  classical
  intro β hin hout hβ
  have hsum := sum_bends_eq hin hout
  have hΔℝ : (b * d₁ - a * d₂ : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hΔ
  -- `Δ ≠ 0` excludes the unbent ray and a zero incoming direction
  have hS : β.bends.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, sum_empty] at hsum
    have ha : (k : ℝ) * a = 0 := by simpa using (congrArg Prod.fst hsum).symm
    have hb : (k : ℝ) * b = 0 := by simpa using (congrArg Prod.snd hsum).symm
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    apply hΔℝ
    rw [(mul_eq_zero.mp ha).resolve_left hk', (mul_eq_zero.mp hb).resolve_left hk']
    ring
  have hd : β.incomingDirection.1 + β.incomingDirection.2 < 0 := by
    have h₁ := Nat.cast_nonneg (α := ℝ) d₁
    have h₂ := Nat.cast_nonneg (α := ℝ) d₂
    refine hin ▸ lt_of_le_of_ne (by simp only; linarith) fun h0 => hΔℝ ?_
    simp only at h0
    rw [show (d₁ : ℝ) = 0 by linarith, show (d₂ : ℝ) = 0 by linarith]
    ring
  have hsign := neg_det_mul_pos hk hΔℝ hin hout hβ hS hd
  set t₀ := β.bends.support.min' hS
  have ht₀ : t₀ ∈ β.bends.support := min'_mem _ hS
  have hmin : ∀ c ∈ β.bends.support, t₀ ≤ c := fun c hc => min'_le _ c hc
  obtain ⟨u, hu, σ, hσ, hpos⟩ := hβ t₀ ht₀
  -- a second bend would make the first increment a lattice point between the two directions
  have hS₁ : β.bends.support = {t₀} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨ht₀, fun t ht => ?_⟩
    by_contra htt
    obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ :=
      le_and_between_of_ne hk hin hout hβ hd hsign ht₀ hmin ht htt hu
    exact hgap u.1 u.2 (by exact_mod_cast h₁) (by exact_mod_cast h₂)
      ⟨by exact_mod_cast h₃, by exact_mod_cast h₄⟩
  -- the single bend carries the whole increment and lies on `ℝ_{<0} (a, b)`
  have ht₀v : β.bends t₀ = (-((k : ℝ) * a), -((k : ℝ) * b)) := by
    rw [← hsum, hS₁, sum_singleton]
  refine ⟨t₀, by rw [(Finsupp.support_eq_singleton.mp hS₁).2, ht₀v], σ * k, by positivity, ?_⟩
  rw [hu] at ht₀v
  have h₁ : (u.1 : ℝ) = k * a := by simpa using congrArg Prod.fst ht₀v
  have h₂ : (u.2 : ℝ) = k * b := by simpa using congrArg Prod.snd ht₀v
  rw [hpos, h₁, h₂]
  ext <;> simp only <;> ring

/-- Burcroff–Lee–Mou, Corollary 5.14(2), for `Δ = b d₁ - a d₂ > 0`: if `d₂ ≥ Δ k b`, then the
rectangle `(d₁, d₂)` is one-bending for `(a, b)` and `k`. -/
theorem oneBending_of_lt_of_le_snd {d₁ d₂ a b k : ℕ} (hk : 0 < k) (hΔ : a * d₂ < b * d₁)
    (h : (b * d₁ - a * d₂) * k * b ≤ d₂) : OneBending d₁ d₂ a b k := by
  refine oneBending_of_forall_not_between hk hΔ.ne' fun a₁ b₁ _ hb₁ ⟨h₁, h₂⟩ => ?_
  have hΔ' : (0 : ℤ) < b * d₁ - a * d₂ := by
    rw [sub_pos]
    exact_mod_cast hΔ
  have h' : ((b * d₁ : ℤ) - a * d₂) * k * b ≤ d₂ := by
    have := Nat.cast_le (α := ℤ) |>.mpr h
    push_cast [Nat.cast_sub hΔ.le] at this
    exact this
  have hb : (1 : ℤ) ≤ b := by
    have : 0 < b := Nat.pos_of_ne_zero fun hb0 => by simp [hb0] at hΔ
    exact_mod_cast this
  have e₁ : (1 : ℤ) ≤ d₁ * b₁ - d₂ * a₁ := pos_of_mul_pos_right h₁ hΔ'.le
  have e₂ : (1 : ℤ) ≤ a₁ * b - b₁ * a := pos_of_mul_pos_right h₂ hΔ'.le
  have hb₁' : (b₁ : ℤ) ≤ k * b := by exact_mod_cast hb₁
  nlinarith [mul_le_mul_of_nonneg_left hb₁' hΔ'.le, mul_nonneg (Nat.cast_nonneg (α := ℤ) d₂)
    (sub_nonneg.mpr e₂), mul_nonneg (Nat.cast_nonneg (α := ℤ) b) (sub_nonneg.mpr e₁)]

/-- Burcroff–Lee–Mou, Corollary 5.14(2), for `Δ = b d₁ - a d₂ < 0`: if `d₁ ≥ -Δ k a`, then the
rectangle `(d₁, d₂)` is one-bending for `(a, b)` and `k`. -/
theorem oneBending_of_lt_of_le_fst {d₁ d₂ a b k : ℕ} (hk : 0 < k) (hΔ : b * d₁ < a * d₂)
    (h : (a * d₂ - b * d₁) * k * a ≤ d₁) : OneBending d₁ d₂ a b k := by
  refine oneBending_of_forall_not_between hk hΔ.ne fun a₁ b₁ ha₁ _ ⟨h₁, h₂⟩ => ?_
  have hΔ' : (b * d₁ : ℤ) - a * d₂ < 0 := by
    rw [sub_neg]
    exact_mod_cast hΔ
  have h' : ((a * d₂ : ℤ) - b * d₁) * k * a ≤ d₁ := by
    have := Nat.cast_le (α := ℤ) |>.mpr h
    push_cast [Nat.cast_sub hΔ.le] at this
    exact this
  have ha : (1 : ℤ) ≤ a := by
    have : 0 < a := Nat.pos_of_ne_zero fun ha0 => by simp [ha0] at hΔ
    exact_mod_cast this
  have e₁ : (1 : ℤ) ≤ d₂ * a₁ - d₁ * b₁ := by nlinarith
  have e₂ : (1 : ℤ) ≤ b₁ * a - a₁ * b := by nlinarith
  have ha₁' : (a₁ : ℤ) ≤ k * a := by exact_mod_cast ha₁
  nlinarith [mul_le_mul_of_nonneg_left ha₁' (neg_nonneg.mpr hΔ'.le),
    mul_nonneg (Nat.cast_nonneg (α := ℤ) d₁) (sub_nonneg.mpr e₂),
    mul_nonneg (Nat.cast_nonneg (α := ℤ) a) (sub_nonneg.mpr e₁)]

/-! ### The rectangles `(6, 4)` and `(5, 3)` for `(a, b) = (1, 1)` and `k = 3` -/

-- The rectangle `(6, 4)` is one-bending by the lattice test, although `d₂ = 4 < Δ k b = 6`.
example : OneBending 6 4 1 1 3 := by
  refine oneBending_of_forall_not_between (by norm_num) (by norm_num) fun a₁ b₁ ha₁ hb₁ => ?_
  interval_cases a₁ <;> interval_cases b₁ <;> norm_num

-- The rectangle `(5, 3)` is not one-bending: the broken line with velocities `(5, 3)`, `(2, 1)`
-- and `(2, 0)` bends at `(-6, -4)` and at `(0, -1)` on the negative `y`-axis. Its first
-- increment `(3, 2)` lies between the directions `(5, 3)` and `(1, 1)`.
example : ¬OneBending 5 3 1 1 3 := by
  classical
  intro h
  set β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ) :=
    ((FiniteAffineRay.straight (2, -1) (-2, 0)).insert (-1) (0, -1) (by norm_num)).insert (-4)
      (-3, -2) (by norm_num)
  have hbends : β.bends = Finsupp.single (-1) (0, -1) + Finsupp.single (-4) (-3, -2) := by
    simp [β]
  obtain ⟨t, ht, -⟩ := h β (by simp [β]; norm_num) (by simp [β]; norm_num) (by
    intro t ht
    rw [hbends] at ht
    rcases Finset.mem_union.mp (Finsupp.support_add ht) with h | h <;>
      obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset h)
    · exact ⟨(0, 1), by rw [hbends]; simp, 1, by norm_num, by simp [β]⟩
    · exact ⟨(3, 2), by rw [hbends]; simp, 2, by norm_num, by simp [β]; norm_num⟩)
  have h₁ := congrArg (· (-1)) ht
  simp only [hbends, Finsupp.add_apply, Finsupp.single_eq_same] at h₁
  rw [Finsupp.single_eq_of_ne (by norm_num), add_zero] at h₁
  rcases eq_or_ne t (-1) with rfl | htm
  · rw [Finsupp.single_eq_same] at h₁
    norm_num [Prod.ext_iff] at h₁
  · rw [Finsupp.single_eq_of_ne htm.symm] at h₁
    simp [Prod.ext_iff] at h₁

end Mei.RankTwo
