/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Component
public import Mathlib.LinearAlgebra.Pi

/-!
# Finite shifted coefficients as a direct sum

The order-`k` shifted coefficient quotient is linearly equivalent to the direct sum
of the ambient pieces indexed by the actual positive degrees retained at order `k`.
The forward map reads the existing `shiftedQuotientComponent` maps, and the inverse
inserts and sums the homogeneous coefficients in the quotient. This keeps the quotient carrier
used by filtered actions, without imposing finiteness on any homogeneous piece.
-/

public noncomputable section

open scoped DirectSum

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

/-- Include a retained ambient homogeneous coefficient in the finite shifted quotient. -/
def shiftedQuotientInclusion (k : ℕ) (n : d.cutoff k) :
    ℳ (p + n.val) →ₗ[R] (d.shiftedFiltration ℳ p).quotient k :=
  ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ.comp
    (shiftedInclusion ℳ d.monoid p ⟨n.val, (d.mem_cutoff.mp n.property).1⟩)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] in
/-- Inclusion is the quotient class of the ambient homogeneous coefficient. -/
@[simp]
theorem shiftedQuotientInclusion_apply (k : ℕ) (n : d.cutoff k) (x : ℳ (p + n.val)) :
    d.shiftedQuotientInclusion ℳ p k n x = Submodule.Quotient.mk
      (shiftedInclusion ℳ d.monoid p ⟨n.val, (d.mem_cutoff.mp n.property).1⟩ x) := (rfl)

/-- Reading the component just included recovers the entire coefficient. -/
@[simp↓]
theorem shiftedQuotientComponent_inclusion (k : ℕ) (n : d.cutoff k)
    (hn : d.degree (p + n.val - p) ≤ k) (x : ℳ (p + n.val)) :
    d.shiftedQuotientComponent ℳ p (p + n.val) k hn
      (d.shiftedQuotientInclusion ℳ p k n x) = x := by
  rw [shiftedQuotientInclusion_apply, shiftedQuotientComponent_mk, coe_shiftedInclusion]
  exact Subtype.ext (DirectSum.decompose_of_mem_same ℳ x.property)

/-- Included coefficients have zero component at any different retained degree. -/
@[simp↓]
theorem shiftedQuotientComponent_inclusion_of_ne (k : ℕ) (n m : d.cutoff k)
    (hm : d.degree (p + m.val - p) ≤ k) (hnm : n ≠ m) (x : ℳ (p + n.val)) :
    d.shiftedQuotientComponent ℳ p (p + m.val) k hm
      (d.shiftedQuotientInclusion ℳ p k n x) = 0 := by
  rw [shiftedQuotientInclusion_apply]
  exact d.shiftedQuotientComponent_mk_shiftedInclusion_of_ne ℳ p (p + m.val) k hm
    ⟨n.val, (d.mem_cutoff.mp n.property).1⟩ (fun he => hnm (Subtype.ext (add_left_cancel he))) x

private def finiteShiftedComponents (k : ℕ) :
    (d.shiftedFiltration ℳ p).quotient k →ₗ[R] (n : d.cutoff k) → ℳ (p + n.val) :=
  LinearMap.pi fun n => d.shiftedQuotientComponent ℳ p (p + n.val) k
    (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)

private def finiteShiftedEquivPi (k : ℕ) :
    (d.shiftedFiltration ℳ p).quotient k ≃ₗ[R] (n : d.cutoff k) → ℳ (p + n.val) :=
  LinearEquiv.ofLinearMap (finiteShiftedComponents d ℳ p k)
    (∑ n : d.cutoff k, (d.shiftedQuotientInclusion ℳ p k n).comp (LinearMap.proj n))
    (by
      apply LinearMap.ext
      intro x
      funext m
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        LinearMap.id_apply, finiteShiftedComponents, LinearMap.pi_apply, map_sum]
      rw [Finset.sum_eq_single m]
      · exact d.shiftedQuotientComponent_inclusion ℳ p k m _ _
      · intro n _ hnm
        exact d.shiftedQuotientComponent_inclusion_of_ne ℳ p k n m _ hnm _
      · simp)
    (by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        LinearMap.id_apply, finiteShiftedComponents, LinearMap.pi_apply,
        shiftedQuotientInclusion_apply]
      symm
      trans Submodule.Quotient.mk
        (∑ n : d.cutoff k, shiftedInclusion ℳ d.monoid p
          ⟨n.val, (d.mem_cutoff.mp n.property).1⟩
          (d.shiftedQuotientComponent ℳ p (p + n.val) k
            (by simpa using (d.mem_cutoff.mp n.property).2) x))
      · convert d.quotient_eq_sum_shiftedQuotientComponent ℳ p k x using 1
        congr 1
        exact Fintype.sum_equiv
          (Equiv.subtypeEquivRight fun n => (d.finite_cutoff k).mem_toFinset.symm)
          _ _ (fun _ => rfl)
      · exact map_sum (((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ) _ _)

/-- The finite shifted quotient is exactly the direct sum of its retained ambient pieces. -/
def shiftedQuotientEquivDirectSum (k : ℕ) :
    (d.shiftedFiltration ℳ p).quotient k ≃ₗ[R] ⨁ n : d.cutoff k, ℳ (p + n.val) :=
  (finiteShiftedEquivPi d ℳ p k).trans (DirectSum.linearEquivFunOnFintype R (d.cutoff k) _).symm

/-- The direct-sum comparison reads the existing ambient quotient components. -/
@[simp]
theorem shiftedQuotientEquivDirectSum_apply (k : ℕ)
    (x : (d.shiftedFiltration ℳ p).quotient k) (n : d.cutoff k) :
    d.shiftedQuotientEquivDirectSum ℳ p k x n =
      d.shiftedQuotientComponent ℳ p (p + n.val) k
        (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2) x := (rfl)

/-- Reassembling a direct sum inserts and sums all retained homogeneous coefficients. -/
theorem shiftedQuotientEquivDirectSum_symm_apply (k : ℕ)
    (x : ⨁ n : d.cutoff k, ℳ (p + n.val)) :
    (d.shiftedQuotientEquivDirectSum ℳ p k).symm x =
      ∑ n : d.cutoff k, d.shiftedQuotientInclusion ℳ p k n (x n) := by
  simp only [shiftedQuotientEquivDirectSum, LinearEquiv.symm_trans_apply,
    finiteShiftedEquivPi, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

/-- A singleton direct sum corresponds to the homogeneous quotient inclusion. -/
@[simp]
theorem shiftedQuotientEquivDirectSum_symm_lof (k : ℕ) (n : d.cutoff k)
    (x : ℳ (p + n.val)) :
    (d.shiftedQuotientEquivDirectSum ℳ p k).symm
      (DirectSum.lof R (d.cutoff k) (fun n => ℳ (p + n.val)) n x) =
        d.shiftedQuotientInclusion ℳ p k n x := by
  apply (d.shiftedQuotientEquivDirectSum ℳ p k).injective
  ext m
  rw [LinearEquiv.apply_symm_apply, shiftedQuotientEquivDirectSum_apply]
  by_cases hnm : n = m
  · subst m
    simp
  · rw [d.shiftedQuotientComponent_inclusion_of_ne ℳ p k n m _ hnm]
    rw [DirectSum.lof_eq_of]
    exact congrArg Subtype.val (DirectSum.of_eq_of_ne
      (β := fun n : d.cutoff k => ℳ (p + n.val)) n m x (Ne.symm hnm))

end Mei.PositiveDegrees
