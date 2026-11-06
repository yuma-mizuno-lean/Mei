/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mei.LinearAlgebra.End.Recursion
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Set.Finite.Range

/-!
# The common backward-ray operator on generic endpoint functions

A *generic endpoint function* of relative order `k` assigns to a base point `V`
and an allowed relative degree `n` in the cutoff `d.cutoff k` a coefficient in
the shifted homogeneous piece `ℳ (p + n)`. This is the carrier on which the
broken-line and the probe recursions of a scattering diagram both read their
lower-order inputs: the base point is the endpoint of the backward ray (or the
incoming germ of the last change), and the relative degree is the grading
coordinate that the recursion lowers.

`endpointStep` is the single operator that both recursions use. It is assembled
from three pieces of geometric data: a finite inventory `ι` of simultaneous
wall events, the coefficient of each event between two relative degrees
(`block`), and the base point at which each event reads its input (`point`).
The only degree input is that a block occurs only for a *lower* relative degree
`m` of a higher one `n`, written `Precedes`: `m ≠ n` and `n - m` is an allowed
degree. No commutativity between different events, no ordering, and no
genericity hypothesis on the base points is used.

The module proves the three properties the R7 comparison needs about this
operator.

* *Degree increase.* `endpointStep` raises the degree filtration
  `endpointHigh d ℳ p V k j`, the endpoint functions vanishing in relative
  degrees at most `j`. Equivalently, it lowers the relative degree actually
  read, which is the last-change bookkeeping of the geometric recursions.
* *Nilpotence.* The filtration vanishes at order `k + 1`, so
  `endpointStep ^ (k + 1) = 0`. The proof tracks degrees along iterates; it
  needs neither a finite ambient grading nor a positivity order on `R`.
* *Recursion uniqueness.* Consequently `x = source + endpointStep x` has the
  unique solution `∑ j ≤ k, endpointStep ^ j source`, and two endpoint
  functions satisfying the same recursion with the same source are equal. This
  is the comparison step of `probeWall_eq_brokenLineSum`: the probe field and
  the broken-line sum are compared through one recursion, without defining
  either side by the other.

The uniqueness theorem is the shared semimodule result
`Module.End.existsUnique_eq_add_of_pow_eq_zero` of `Mei.LinearAlgebra.End.Recursion`,
applied to this operator. The last-change bookkeeping follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public section

noncomputable section

namespace Mei

namespace PositiveDegrees

variable {Γ : Type*} [AddCommGroup Γ] (d : PositiveDegrees Γ)

/-- A relative degree `m` is strictly lower than `n` when it differs from it and
`n - m` is an allowed degree. This is the index relation of a last change: the
residual degree `n - m` is the degree carried by the crossed wall events. -/
@[expose] def Precedes (m n : Γ) : Prop := m ≠ n ∧ n - m ∈ d.monoid

/-- The last-change relation is decidable, so the sums over retained degrees can
select it without side conditions. -/
noncomputable instance instDecidablePrecedes (m n : Γ) : Decidable (d.Precedes m n) :=
  Classical.propDecidable _

/-- Strictly lower relative degrees have strictly smaller degree. -/
theorem degree_lt_of_precedes {m n : Γ} (h : d.Precedes m n) :
    d.degree m < d.degree n := by
  obtain ⟨hne, hsub⟩ := h
  have hzero : n - m ≠ 0 := sub_ne_zero.mpr hne.symm
  have hpos := d.degree_pos hsub hzero
  have hsplit : m + (n - m) = n := add_sub_cancel m n
  have := congrArg d.degree hsplit
  simp only [map_add] at this
  omega

end PositiveDegrees

open PositiveDegrees

variable {R M V : Type*} [Ring R] [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup M]
  [Module R M] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ) (k : ℕ)

/-- The relative-degree cutoff is a finite type, so endpoint sums over it are
finite. -/
noncomputable instance cutoffFintype : Fintype (d.cutoff k) := (d.finite_cutoff k).fintype

/-- Generic endpoint functions of relative order `k`: a base point and a
coefficient in every retained shifted homogeneous piece. -/
abbrev Endpoint (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ) (V : Type*)
    (k : ℕ) : Type _ :=
  V → (n : d.cutoff k) → ℳ (p + n.val)

/-- The common backward-ray step of the broken-line and probe recursions.

The inventory `ι` indexes simultaneous wall events. It may depend on the base
point `Q` and output degree `n`. Event `b` reads its input at `point b Q n m`,
where both the output degree `n` and the input degree `m` may vary, and transports
it to the output through `block b`. Only strictly lower relative degrees
contribute, which is what removes the unchanged-degree encounters. -/
def endpointStep (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ) (k : ℕ)
    {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) :
      Endpoint d ℳ p V k →ₗ[R] Endpoint d ℳ p V k where
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

omit [DecidableEq Γ] in
/-- The defining formula of the backward-ray step. -/
theorem endpointStep_apply {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) (F : Endpoint d ℳ p V k) (Q : V)
    (n : d.cutoff k) :
    endpointStep d ℳ p k events block point F Q n =
      ∑ b ∈ events Q n, ∑ m : d.cutoff k,
        if h : d.Precedes m.val n.val then block b n m h (F (point b Q n m) m) else 0 := (rfl)

/-- Endpoint functions vanishing in every relative degree at most `j`. These are
the terms of the degree filtration that a last change leaves behind. -/
def endpointHigh (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ) (V : Type*)
    (k : ℕ) (j : ℕ) : Submodule R (Endpoint d ℳ p V k) where
  carrier := {F | ∀ Q n, d.degree n.val ≤ j → F Q n = 0}
  zero_mem' := by
    intro Q n _
    rfl
  add_mem' := by
    intro F G hF hG Q n hn
    rw [Pi.add_apply, Pi.add_apply, hF Q n hn, hG Q n hn, add_zero]
  smul_mem' := by
    intro a F hF Q n hn
    rw [Pi.smul_apply, Pi.smul_apply, hF Q n hn, smul_zero]

omit [DecidableEq Γ] in
/-- The backward-ray step strictly raises the degree filtration: an endpoint
function vanishing in all relative degrees at most `j` is sent to one vanishing
in all relative degrees at most `j + 1`. -/
theorem endpointStep_mem_endpointHigh {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) {j : ℕ} {F : Endpoint d ℳ p V k}
    (hF : F ∈ endpointHigh d ℳ p V k j) :
    endpointStep d ℳ p k events block point F ∈ endpointHigh d ℳ p V k (j + 1) := by
  classical
  intro Q n hn
  rw [endpointStep_apply]
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro m _
  split_ifs with hmn
  · rw [hF _ _ (by have := degree_lt_of_precedes d hmn; omega), map_zero]
  · rfl

omit [DecidableEq Γ] in
/-- The degree filtration of endpoint functions vanishes at order `k + 1`. -/
theorem endpointHigh_eq_bot : endpointHigh d ℳ p V k (k + 1) = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  funext Q n
  exact hF Q n (by have := (d.mem_cutoff.mp n.property).2; omega)

omit [DecidableEq Γ] in
/-- Iterates of the backward-ray step vanish on relative degrees below the
iterate count: after `j` steps the value read has lost at least `j` degrees. -/
theorem endpointStep_pow_apply_eq_zero {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) :
    ∀ (j : ℕ) (F : Endpoint d ℳ p V k) (Q : V) (n : d.cutoff k),
      d.degree n.val < j →
        ((endpointStep d ℳ p k events block point) ^ j) F Q n = 0 := by
  classical
  intro j
  induction j with
  | zero =>
    intro F Q n h
    have h0 := d.degree_nonneg (d.mem_cutoff.mp n.property).1
    omega
  | succ j ih =>
    intro F Q n h
    rw [pow_succ', Module.End.mul_apply, endpointStep_apply]
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro m _
    split_ifs with hmn
    · rw [ih _ _ _ (by have := degree_lt_of_precedes d hmn; omega), map_zero]
    · rfl

omit [DecidableEq Γ] in
/-- Nilpotence of the common backward-ray operator: its `k + 1`-st iterate is
zero on endpoint functions of relative order `k`. -/
theorem endpointStep_pow_eq_zero {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
    (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
      ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
    (point : ι → V → (n m : d.cutoff k) → V) :
    (endpointStep d ℳ p k events block point) ^ (k + 1) = 0 := by
  refine LinearMap.ext fun F => ?_
  refine funext fun Q => ?_
  refine funext fun n => ?_
  exact endpointStep_pow_apply_eq_zero d ℳ p k events block point (k + 1) F Q n
    (by have := (d.mem_cutoff.mp n.property).2; omega)

section Recursion

variable {ι : Type*} (events : V → (d.cutoff k) → Finset ι)
  (block : ι → (n m : d.cutoff k) → d.Precedes m.val n.val →
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val))
  (point : ι → V → (n m : d.cutoff k) → V)

omit [DecidableEq Γ] in
/-- Two endpoint functions satisfying the same last-change recursion with the
same source are equal. This is the comparison principle for the probe field and
the broken-line sum: it applies to both once each is shown to solve the
recursion of the common backward-ray operator. -/
theorem eq_of_endpointStep_eq_add {source x y : Endpoint d ℳ p V k}
    (hx : x = source + endpointStep d ℳ p k events block point x)
    (hy : y = source + endpointStep d ℳ p k events block point y) : x = y :=
  Module.End.eq_of_eq_add_of_pow_eq_zero _
    (endpointStep_pow_eq_zero d ℳ p k events block point) hx hy

omit [DecidableEq Γ] in
/-- Every solution of the common recursion is the finite sum of the iterates of
the source, below the nilpotency bound. -/
theorem eq_finiteRecursion_endpointStep {source x : Endpoint d ℳ p V k}
    (hx : x = source + endpointStep d ℳ p k events block point x) :
    x = Module.End.finiteRecursion (endpointStep d ℳ p k events block point) (k + 1) source :=
  Module.End.eq_finiteRecursion_of_eq_add _
    (endpointStep_pow_eq_zero d ℳ p k events block point) hx

omit [DecidableEq Γ] in
/-- The common recursion has exactly one solution. -/
theorem existsUnique_endpointStep_eq_add (source : Endpoint d ℳ p V k) :
    ∃! x, x = source + endpointStep d ℳ p k events block point x :=
  Module.End.existsUnique_eq_add_of_pow_eq_zero _
    (endpointStep_pow_eq_zero d ℳ p k events block point) source

end Recursion

end Mei
