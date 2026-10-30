/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude Code
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Factoring finite sums

The sum of a product over functions with freely varying coordinates factors into a fixed
product and a power of the common local sum. Weighted sums over fibres of a projection
also factor through its fixed points, without requiring commutative multiplication.
-/

public section

namespace Finset

/-- If the local sum on each free coordinate is `Q` and the fixed local factors there are
one, summing over all free choices multiplies the fixed product by `Q ^ #O`. -/
theorem sum_piFinset_factor {ι α R : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring R] (f : ι → α → R) (O : Finset ι) (T : Finset α) (Q : R)
    (hQ : ∀ k ∈ O, ∑ j ∈ T, f k j = Q) (g : ι → α) (h₀ : ∀ k ∈ O, f k (g k) = 1) :
    ∑ γ ∈ Fintype.piFinset (fun k ↦ if k ∈ O then T else {g k}), ∏ k, f k (γ k) =
      (∏ k, f k (g k)) * Q ^ #O := by
  classical
  rw [← prod_univ_sum]
  have h₁ : ∀ k, ∑ j ∈ (if k ∈ O then T else {g k}), f k j =
      (if k ∈ O then Q else 1) * f k (g k) := by
    intro k
    split_ifs with hk
    · simp only [hQ k hk, h₀ k hk, mul_one]
    · simp only [sum_singleton, one_mul]
  rw [prod_congr rfl fun k _ ↦ h₁ k, prod_mul_distrib]
  simp only [prod_ite, prod_const, filter_mem_eq_inter, univ_inter, one_pow, mul_one]
  exact mul_comm _ _

/-- Summing the fibres of a projection that preserves a predicate and an auxiliary total
recovers the weighted sum from its fixed points. -/
theorem sum_gen_of_truncation {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    (G : Finset ι) (trunc : ι → ι) (C A : ι → Prop) [DecidablePred C] [DecidablePred A]
    (m : ι → ℕ) (f : ι → R) (Q : R) (r : ℕ → ℕ)
    (hC : ∀ γ, C (trunc γ) ↔ C γ) (hm : ∀ γ, m (trunc γ) = m γ)
    (hA : ∀ γ, A (trunc γ)) (hfix : ∀ γ, A γ → trunc γ = γ)
    (hG : ∀ γ ∈ G, trunc γ ∈ G)
    (hfiber : ∀ γ ∈ G, trunc γ = γ →
      ∑ δ ∈ G.filter (trunc · = γ), f δ = f γ * Q ^ r (m γ)) (q : ℕ) :
    ∑ γ ∈ G with C γ ∧ m γ = q, f γ =
      (∑ γ ∈ G with C γ ∧ m γ = q ∧ A γ, f γ) * Q ^ r q := by
  rw [← sum_fiberwise_of_maps_to (g := trunc) ?_, sum_mul]
  · refine sum_congr rfl fun γ' hγ' ↦ ?_
    obtain ⟨hγ'G, hc', hq', hs'⟩ := mem_filter.mp hγ'
    rw [← hq', ← hfiber γ' hγ'G (hfix γ' hs'), filter_filter]
    congr 1
    refine filter_congr fun γ _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨⟨?_, ?_⟩, h⟩⟩
    · rw [← hC, h]
      exact hc'
    · rw [← hm, h]
  · intro γ hγ
    obtain ⟨hγG, hc, hq⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hG γ hγG, (hC γ).mpr hc, by rw [hm, hq], hA γ⟩

end Finset
