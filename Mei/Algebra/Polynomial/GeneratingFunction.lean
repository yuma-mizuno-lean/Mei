/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mei.Algebra.BigOperators.Ring.Finset

/-!
# Generating functions of finite projections

Weighted monomial sums over fibres factor into a fixed monomial and the local free-coordinate
contributions.
-/

public section

namespace Polynomial

open Finset

/-- The weighted generating function of a fibre factors into its fixed monomial and free
coordinate contributions. -/
theorem sum_fiber_trunc {S : Type*} [CommSemiring S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset (ι → ℕ)) (trunc : (ι → ℕ) → ι → ℕ) (O : Finset ι) (ℓ : ℕ)
    (Q : S[X]) (f : ι → ℕ → S[X]) (w : (ι → ℕ) → S) (total : (ι → ℕ) → ℕ)
    (hprod : ∀ γ, ∏ k, f k (γ k) = C (w γ) * X ^ total γ) (γ' : ι → ℕ)
    (hfilter : G.filter (trunc · = γ') =
      Fintype.piFinset fun k ↦ if k ∈ O then range (ℓ + 1) else {γ' k})
    (hQ : ∀ k ∈ O, ∑ j ∈ range (ℓ + 1), f k j = Q)
    (h₀ : ∀ k ∈ O, f k (γ' k) = 1) :
    ∑ γ ∈ G.filter (trunc · = γ'), C (w γ) * X ^ total γ =
      C (w γ') * X ^ total γ' * Q ^ #O := by
  simp_rw [← hprod]
  rw [hfilter]
  exact sum_piFinset_factor f O (range (ℓ + 1)) Q hQ γ' h₀


end Polynomial
