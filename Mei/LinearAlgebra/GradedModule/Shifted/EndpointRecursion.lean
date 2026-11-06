/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Lower-degree steps on shifted cutoff functions

A *shifted cutoff function* of order `k` assigns to a base point in `V` and a
relative degree `n` in `d.cutoff k` a coefficient in the shifted homogeneous
piece `ℳ (p + n)`. A lower-degree step on these functions is assembled from an
arbitrary index type `ι`, a finite set `events Q n` of indices for each base
point and output degree, a coefficient map `block`, and a read point `point`.
The block between relative degrees `m` and `n` is defined only when `m` strictly
precedes `n`, meaning that `m ≠ n` and `n - m` is an allowed degree.

`shiftedLowerStep` packages these data as a linear endomorphism. Each step reads
at a relative degree strictly below the output degree. Consequently its `j`th
iterate vanishes in every relative degree of degree below `j`
(`shiftedLowerStep_pow_apply_eq_zero`), and its `(k + 1)`st iterate is zero
(`shiftedLowerStep_pow_eq_zero`). The proof tracks degrees along iterates and
needs neither a finite ambient grading nor a positivity order on `R`.

Together with the generic results of `Mei.LinearAlgebra.End.Recursion`, this
nilpotence gives finite solutions and uniqueness for recursions of the form
`x = source + shiftedLowerStep x`. The degree bookkeeping follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M V : Type*} [AddCommGroup Γ] [Semiring R] [AddCommMonoid M]
  [Module R M] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ) (k : ℕ)

/-- Shifted cutoff functions: a coefficient at a base point in every retained
shifted homogeneous piece. -/
abbrev ShiftedEndpointFunction (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
    (p : Γ) (V : Type*) (k : ℕ) : Type _ :=
  V → (n : d.cutoff k) → ℳ (p + n.val)

/-- The linear step that transports coefficients from strictly lower relative
degrees. Each `(Q, n)` selects a finite event set from the arbitrary index type
`ι`; event `b` reads at `point b Q n m` and maps its coefficient through
`block b`. No ordering, commutativity, or geometric hypothesis on the base
points is used. -/
def shiftedLowerStep (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ) (k : ℕ)
    {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) :
      ShiftedEndpointFunction d ℳ p V k →ₗ[R] ShiftedEndpointFunction d ℳ p V k where
  toFun F Q n :=
    ∑ b ∈ events Q n, ∑ m : d.cutoff k,
      if h : d.Precedes m.val n.val then block b n m h (F (point b Q n m) m) else 0
  map_add' F G := by
    classical
    funext Q n
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hmn
    · rw [map_add]
    · rw [add_zero]
  map_smul' a F := by
    classical
    funext Q n
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hmn
    · rw [map_smul]
    · rw [smul_zero]

/-- The defining formula of the lower-degree step. -/
theorem shiftedLowerStep_apply {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) (F : ShiftedEndpointFunction d ℳ p V k)
    (Q : V) (n : d.cutoff k) :
    shiftedLowerStep d ℳ p k events block point F Q n =
      ∑ b ∈ events Q n, ∑ m : d.cutoff k,
        if h : d.Precedes m.val n.val then block b n m h (F (point b Q n m) m) else 0 := (rfl)

/-- Iterates of the lower-degree step vanish on relative degrees below the
iterate count: after `j` steps the value read has lost at least `j` degrees. -/
theorem shiftedLowerStep_pow_apply_eq_zero {ι : Type*}
    (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) :
    ∀ (j : ℕ) (F : ShiftedEndpointFunction d ℳ p V k) (Q : V) (n : d.cutoff k),
      d.degree n.val < j →
        ((shiftedLowerStep d ℳ p k events block point) ^ j) F Q n = 0 := by
  classical
  intro j
  induction j with
  | zero =>
    intro F Q n h
    have h0 := d.degree_nonneg (d.mem_cutoff.mp n.property).1
    omega
  | succ j ih =>
    intro F Q n h
    rw [pow_succ', Module.End.mul_apply, shiftedLowerStep_apply]
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro m _
    split_ifs with hmn
    · rw [ih _ _ _ (by have := degree_lt_of_precedes d hmn; omega), map_zero]
    · rfl

/-- The lower-degree step is nilpotent on shifted cutoff functions of order `k`. -/
theorem shiftedLowerStep_pow_eq_zero {ι : Type*}
    (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) :
    (shiftedLowerStep d ℳ p k events block point) ^ (k + 1) = 0 := by
  refine LinearMap.ext fun F => ?_
  refine funext fun Q => ?_
  refine funext fun n => ?_
  exact shiftedLowerStep_pow_apply_eq_zero d ℳ p k events block point (k + 1) F Q n
    (by have := (d.mem_cutoff.mp n.property).2; omega)

end Mei.PositiveDegrees
