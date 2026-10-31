/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite recursion for nilpotent endomorphisms

If `U ^ r = 0`, the equation `x = a + U x` has the unique solution
`∑ j ∈ Finset.range r, (U ^ j) a`. The solution is linear in `a`, independent
of the nilpotency bound, and natural under intertwining linear maps.

The proofs work over a semiring on an additive commutative monoid: neither
subtraction nor additive cancellation is needed. In particular, the comparison
of two independently established recursions applies to semimodule coefficients.
The filtration-raising operators on finite module quotients in
`Mei.LinearAlgebra.ModuleFiltration.Recursion` are an application of this over rings.
-/

public section

namespace Module.End

variable {R M N : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (U : Module.End R M)

/-- The finite geometric sum, regarded as a linear solution operator. -/
def finiteRecursion (r : ℕ) : Module.End R M :=
  ∑ j ∈ Finset.range r, U ^ j

/-- Evaluating the solution operator gives the finite sum of iterates. -/
theorem finiteRecursion_apply (r : ℕ) (a : M) :
    U.finiteRecursion r a = ∑ j ∈ Finset.range r, (U ^ j) a := by
  simp only [finiteRecursion, LinearMap.sum_apply]

/-- A nilpotency bound makes the solution operator satisfy `1 + U * S = S`. -/
theorem finiteRecursion_eq_one_add_mul {r : ℕ} (hU : U ^ r = 0) :
    U.finiteRecursion r = 1 + U * U.finiteRecursion r := by
  rw [finiteRecursion, add_comm 1, ← geom_sum_succ, Finset.sum_range_succ, hU, add_zero]

/-- A nilpotency bound makes the finite geometric sum solve the recursion. -/
theorem finiteRecursion_eq_add {r : ℕ} (hU : U ^ r = 0) (a : M) :
    U.finiteRecursion r a = a + U (U.finiteRecursion r a) :=
  LinearMap.congr_fun (U.finiteRecursion_eq_one_add_mul hU) a

/-- Any solution equals the finite geometric sum. -/
theorem eq_finiteRecursion_of_eq_add {r : ℕ} (hU : U ^ r = 0)
    {a x : M} (hx : x = a + U x) : x = U.finiteRecursion r a := by
  -- Unrolling retains the remainder `U ^ n x`, so no cancellation is needed.
  have expand (n : ℕ) :
      x = (∑ j ∈ Finset.range n, (U ^ j) a) + (U ^ n) x := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : (U ^ n) x = (U ^ n) a + (U ^ (n + 1)) x := by
        simpa only [map_add, pow_succ, Module.End.mul_apply] using congrArg (U ^ n) hx
      calc
        x = (∑ j ∈ Finset.range n, (U ^ j) a) + (U ^ n) x := ih
        _ = (∑ j ∈ Finset.range (n + 1), (U ^ j) a) + (U ^ (n + 1)) x := by
          rw [hn, Finset.sum_range_succ, add_assoc]
  simpa [hU, finiteRecursion_apply] using expand r

/-- Two independently constructed solutions of the same nilpotent recursion agree. -/
theorem eq_of_eq_add_of_pow_eq_zero {r : ℕ} (hU : U ^ r = 0)
    {a x y : M} (hx : x = a + U x) (hy : y = a + U y) : x = y :=
  (U.eq_finiteRecursion_of_eq_add hU hx).trans
    (U.eq_finiteRecursion_of_eq_add hU hy).symm

/-- Nilpotent linear recursions have exactly one solution over semimodules. -/
theorem existsUnique_eq_add_of_pow_eq_zero {r : ℕ} (hU : U ^ r = 0) (a : M) :
    ∃! x, x = a + U x :=
  ⟨U.finiteRecursion r a, U.finiteRecursion_eq_add hU a,
    fun _ hx => U.eq_finiteRecursion_of_eq_add hU hx⟩

/-- The solution operator does not depend on the chosen nilpotency bound. -/
theorem finiteRecursion_eq {r s : ℕ} (hr : U ^ r = 0) (hs : U ^ s = 0) :
    U.finiteRecursion r = U.finiteRecursion s := by
  ext a
  exact U.eq_of_eq_add_of_pow_eq_zero hr
    (U.finiteRecursion_eq_add hr a) (U.finiteRecursion_eq_add hs a)

/-- Intertwining maps preserve solutions, even with different nilpotency bounds. -/
theorem comp_finiteRecursion (V : Module.End R N) (f : M →ₗ[R] N)
    (hf : f.comp U = V.comp f) {r s : ℕ} (hU : U ^ r = 0) (hV : V ^ s = 0) :
    f.comp (U.finiteRecursion r) = (V.finiteRecursion s).comp f := by
  ext a
  apply V.eq_finiteRecursion_of_eq_add hV
  have h := congrArg f (U.finiteRecursion_eq_add hU a)
  have hf' (x : M) : f (U x) = V (f x) := LinearMap.congr_fun hf x
  simpa only [map_add, hf', LinearMap.comp_apply] using h

end Module.End
