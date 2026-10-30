/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Homogeneous components under regrading

For an additive map preserving homogeneous pieces along an arbitrary map of degrees,
each target component is the sum of the source images over its degree fiber.
The sum uses only the finite homogeneous support of the input, so the degree map need
not have finite fibers or be injective. This describes how coefficients merge under
regrading an internally decomposed additive monoid.
For finite source gradings, reconstruction and regrading also have sums over all degrees.

The proof uses Mathlib's `DirectSum.sum_support_decompose` and homogeneous projection API.
-/

public section

namespace DirectSum

open Classical in
/-- For a finite grading, summing all homogeneous components recovers the input. -/
theorem sum_univ_decompose {ι M S : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M]
    (ℳ : ι → S) [Decomposition ℳ] (x : M) :
    ∑ i, (decompose ℳ x i : M) = x := by
  calc
    _ = ∑ i ∈ (decompose ℳ x).support, (decompose ℳ x i : M) := by
      simpa only [DFinsupp.sum] using
        (DFinsupp.sum_of_support_subset (f := decompose ℳ x)
          (g := fun i y => (y : M)) (Finset.subset_univ _) (by simp)).symm
    _ = x := sum_support_decompose ℳ x

open Classical in
/-- Under a homogeneous additive map, a target component is the finite sum of the images
of the source components whose degrees map to that target degree. -/
theorem decompose_map_eq_sum {ι κ M N S T : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [AddCommMonoid N]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T N] [AddSubmonoidClass T N]
    (ℳ : ι → S) [Decomposition ℳ] (𝓝 : κ → T) [Decomposition 𝓝]
    (f : M →+ N) (σ : ι → κ)
    (hf : ∀ i x, x ∈ ℳ i → f x ∈ 𝓝 (σ i)) (x : M) (j : κ) :
    (decompose 𝓝 (f x) j : N) =
      ∑ i ∈ (decompose ℳ x).support with σ i = j, f (decompose ℳ x i : M) := by
  have hproj (i : ι) :
      (decompose 𝓝 (f (decompose ℳ x i : M)) j : N) =
        if σ i = j then f (decompose ℳ x i : M) else 0 := by
    split_ifs with h
    · exact decompose_of_mem_same 𝓝 (h ▸ hf i _ (decompose ℳ x i).property)
    · exact decompose_of_mem_ne 𝓝 (hf i _ (decompose ℳ x i).property) h
  calc
    (decompose 𝓝 (f x) j : N) =
        (decompose 𝓝 (f (∑ i ∈ (decompose ℳ x).support,
          (decompose ℳ x i : M))) j : N) := by rw [sum_support_decompose]
    _ = ∑ i ∈ (decompose ℳ x).support,
        (decompose 𝓝 (f (decompose ℳ x i : M)) j : N) := by
      simp only [map_sum, decompose_sum, DirectSum.sum_apply]
      exact map_sum (AddSubmonoidClass.subtype (𝓝 j)) _ _
    _ = _ := by simp_rw [hproj]; rw [Finset.sum_filter]

open Classical in
/-- For a finite source grading, a target component under a homogeneous additive map
is the sum over all source degrees mapping to that target degree. -/
theorem decompose_map_eq_sum_univ {ι κ M N S T : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [AddCommMonoid N]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T N] [AddSubmonoidClass T N]
    (ℳ : ι → S) [Decomposition ℳ] (𝓝 : κ → T) [Decomposition 𝓝]
    (f : M →+ N) (σ : ι → κ)
    (hf : ∀ i x, x ∈ ℳ i → f x ∈ 𝓝 (σ i)) (x : M) (j : κ) :
    (decompose 𝓝 (f x) j : N) =
      ∑ i, if σ i = j then f (decompose ℳ x i : M) else 0 := by
  rw [decompose_map_eq_sum ℳ 𝓝 f σ hf x j, Finset.sum_filter]
  simpa only [DFinsupp.sum] using
    (DFinsupp.sum_of_support_subset (f := decompose ℳ x)
      (g := fun i y => if σ i = j then f (y : M) else 0)
      (Finset.subset_univ _) (by intros; simp))

end DirectSum
