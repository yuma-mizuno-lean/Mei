/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Components of a coarser homogeneous element

Let `ℳ` and `𝒜` be two decompositions of one module, and suppose that `ℳ` refines `𝒜` along a
map `w`, that is, `ℳ q ⊆ 𝒜 (w q)` for every index `q`. A homogeneous element of `𝒜` of index
`i` then has nonzero `ℳ`-components only in the indices `q` with `w q = i`, and these components
are again homogeneous of index `i`.

In particular, these results apply to a fine exponent grading and the coarser grading by the
weight of a wall normal: the weight of a component of a weight-homogeneous element is the weight
of the element.
-/

public section

namespace DirectSum

variable {ι κ M σ τ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M]
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M] [AddSubmonoidClass τ M]
  (ℳ : ι → σ) [Decomposition ℳ] (𝒜 : κ → τ) [Decomposition 𝒜] (w : ι → κ)

/-- The `𝒜`-component of an element commutes with taking `ℳ`-components when `ℳ` refines `𝒜`
along `w`: it keeps the `ℳ`-components whose index has image `i`, and discards the rest. -/
theorem decompose_decompose_apply_of_le (hw : ∀ q, ∀ x ∈ ℳ q, x ∈ 𝒜 (w q)) (i : κ) (η : ι) (x : M) :
    (decompose ℳ (decompose 𝒜 x i : M) η : M) =
      if w η = i then (decompose ℳ x η : M) else 0 := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous q y =>
    have hy : (y : M) ∈ 𝒜 (w q) := hw q y y.2
    by_cases hηq : η = q
    · subst hηq
      by_cases hi : w η = i
      · simp [decompose_of_mem_same 𝒜 (hi ▸ hy), hi]
      · simp [decompose_of_mem_ne 𝒜 hy hi, hi]
    · have h0 : (decompose ℳ (y : M) η : M) = 0 := decompose_of_mem_ne ℳ y.2 (Ne.symm hηq)
      by_cases hi : w q = i
      · rw [decompose_of_mem_same 𝒜 (hi ▸ hy), h0]
        split_ifs <;> rfl
      · rw [decompose_of_mem_ne 𝒜 hy hi, h0]
        simp
  | add x y hx hy =>
    by_cases h : w η = i <;> simp_all

/-- If `ℳ` refines `𝒜` along `w`, a homogeneous element of `𝒜` of index `i` has no nonzero
`ℳ`-component in an index `η` with `w η ≠ i`. -/
theorem decompose_eq_zero_of_mem_of_le (hw : ∀ q, ∀ x ∈ ℳ q, x ∈ 𝒜 (w q)) {i : κ} {x : M}
    (hx : x ∈ 𝒜 i) {η : ι} (hη : w η ≠ i) : decompose ℳ x η = 0 := by
  have := decompose_decompose_apply_of_le ℳ 𝒜 w hw i η x
  simp only [decompose_of_mem_same 𝒜 hx, hη, ↓reduceIte] at this
  exact_mod_cast this

end DirectSum
