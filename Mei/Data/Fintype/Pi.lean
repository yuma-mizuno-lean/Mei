/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Fintype.Pi

/-!
# Fibres of coordinatewise projections

A projection that zeroes a stable set of free coordinates has a Cartesian-product fibre:
free coordinates vary over their common bounds and the remaining coordinates stay fixed.
-/

public section

namespace Finset

/-- A coordinatewise zeroing projection has independent free coordinates in each fibre. -/
theorem filter_trunc_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset (ι → ℕ)) (bound : ι → ℕ) (free : (ι → ℕ) → Finset ι)
    (trunc : (ι → ℕ) → ι → ℕ) (ℓ : ℕ)
    (hG : ∀ γ, γ ∈ G ↔ ∀ k, γ k ≤ bound k)
    (htrunc : ∀ γ k, trunc γ k = if k ∈ free γ then 0 else γ k)
    (hbound : ∀ γ k, k ∈ free γ → bound k = ℓ)
    (hfree : ∀ γ γ', (∀ k ∉ free γ', γ k = γ' k) → free γ = free γ')
    {γ' : ι → ℕ} (hγ' : γ' ∈ G) (hfix : trunc γ' = γ') :
    G.filter (trunc · = γ') =
      Fintype.piFinset fun k ↦ if k ∈ free γ' then range (ℓ + 1) else {γ' k} := by
  have hfree_trunc (γ) : free (trunc γ) = free γ :=
    hfree _ _ fun k hk ↦ by simp only [htrunc, hk, ↓reduceIte]
  ext γ
  rw [hG] at hγ'
  simp only [mem_filter, hG, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hb, rfl⟩ k
    rw [hfree_trunc]
    split_ifs with hk
    · exact mem_range.mpr (Nat.lt_succ_iff.mpr ((hbound γ k hk) ▸ hb k))
    · exact mem_singleton.mpr (by simp only [htrunc, hk, ↓reduceIte])
  · intro hT
    have heq : ∀ k ∉ free γ', γ k = γ' k := fun k hk ↦ by
      have := hT k
      simpa only [hk, ↓reduceIte, mem_singleton] using this
    have hfree' := hfree γ γ' heq
    refine ⟨fun k ↦ ?_, funext fun k ↦ ?_⟩
    · have := hT k
      split_ifs at this with hk
      · rw [hbound γ' k hk]
        exact Nat.lt_succ_iff.mp (mem_range.mp this)
      · rw [mem_singleton.mp this]
        exact hγ' k
    · rw [htrunc, hfree']
      split_ifs with hk
      · rw [← hfix, htrunc]
        simp only [hk, ↓reduceIte]
      · exact heq k hk

end Finset
