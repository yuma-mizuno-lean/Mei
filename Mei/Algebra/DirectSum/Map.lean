/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.HomogeneousExtend
public import TauCeti.Algebra.DirectSum.Internal
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Homogeneous components under regrading

For an additive map preserving homogeneous pieces along an arbitrary map of degrees,
each target component is the sum of the source images over its degree fiber.
The sum uses only the finite homogeneous support of the input, so the degree map need
not have finite fibers or be injective. This describes how coefficients merge under
regrading an internally decomposed additive monoid.
For finite source gradings, reconstruction and regrading also have sums over all degrees.
Linear maps prescribed on the homogeneous pieces extend uniquely to the whole module,
with homogeneous-input and finite-support computation formulas. Preserving chosen
positive monoids on the pieces gives positivity of the extended map.

The finite regrading formula uses Tau Ceti's `DirectSum.decompose_map_eq_sum`.
-/

public section

namespace DirectSum

section LinearExtension

variable {R U M ι : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (𝒰 : ι → Submodule R U) [Decomposition 𝒰]

/-- A homogeneous extension sends componentwise positive inputs into an additive
submonoid if each prescribed map does so on its homogeneous positive inputs. -/
theorem homogeneousExtend_mem_addSubmonoid (f : ∀ i, 𝒰 i →ₗ[R] M)
    (Pos : ι → AddSubmonoid U) (P : AddSubmonoid M)
    (hf : ∀ i (a : 𝒰 i), (a : U) ∈ Pos i → f i a ∈ P)
    (a : U) (ha : ∀ i, (decompose 𝒰 a i : U) ∈ Pos i) :
    homogeneousExtend 𝒰 f a ∈ P := by
  classical
  rw [homogeneousExtend_eq_sum]
  exact P.sum_mem (fun i _ => hf i _ (ha i))

end LinearExtension

open Classical in
/-- For a finite grading, summing all homogeneous components recovers the input. -/
@[simp]
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
