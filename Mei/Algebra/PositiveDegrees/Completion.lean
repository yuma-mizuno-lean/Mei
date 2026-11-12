/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Completion
public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.LinearAlgebra.ModuleFiltration.QuotientTower

/-!
# Degree completions for module filtrations

Mei's compatible quotient families form a module filtration completion.
We compare these families with TauCeti's limit of the same quotient tower
and use the upstream coefficient maps and product equivalence.
-/

public section

open _root_.DirectSum

namespace TauCeti.PositiveDegrees

open Mei

variable {N R M : Type*} [AddCommMonoid N] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq N] (d : PositiveDegrees N) (ℳ : N → Submodule R M)
  [Decomposition ℳ] (F : ModuleFiltration R M)

local notation "J" => fun k => F.submodule (k + 1)

variable (hF : ∀ k, F.submodule (k + 1) = d.degreeSubmodule ℳ k)

/-- A homogeneous component of a finite filtration quotient. -/
def filtrationQuotientComponent (k : ℕ) (n : N) (hn : d.degree n ≤ k) :
    F.quotient k →ₗ[R] ℳ n :=
  (d.quotientComponent ℳ J F.quotientAntitone hF k n hn).comp
    (F.quotientEquivTower k).toLinearMap

/-- The component of a quotient class is the corresponding homogeneous component. -/
@[simp]
theorem filtrationQuotientComponent_mk (k : ℕ) (n : N) (hn : d.degree n ≤ k) (x : M) :
    d.filtrationQuotientComponent ℳ F hF k n hn (Submodule.Quotient.mk x) = decompose ℳ x n := by
  simp [filtrationQuotientComponent]

/-- Components already retained at the lower cutoff commute with quotient transitions. -/
@[simp]
theorem filtrationQuotientComponent_transition {k l : ℕ} (h : k ≤ l) (n : N)
    (hn : d.degree n ≤ k) (x : F.quotient l) :
    d.filtrationQuotientComponent ℳ F hF k n hn (F.transition h x) =
      d.filtrationQuotientComponent ℳ F hF l n (hn.trans (Int.ofNat_le.mpr h)) x := by
  simp only [filtrationQuotientComponent, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← F.quotientEquivTower_transition h x, quotientComponent_transition]

/-- The degree component of an element of the filtration completion. -/
def filtrationCompletionComponent (n : N) : F.completion →ₗ[R] ℳ n :=
  (d.completionComponent ℳ J F.quotientAntitone hF n).comp
    F.completionEquivTowerLimit.toLinearMap

/-- Any cutoff containing the degree computes the same completed component. -/
theorem filtrationCompletionComponent_eq_quotientComponent (n : N) (k : ℕ)
    (hn : d.degree n ≤ k) (x : F.completion) :
    d.filtrationCompletionComponent ℳ F hF n x =
      d.filtrationQuotientComponent ℳ F hF k n hn (F.projection k x) := by
  simp only [filtrationCompletionComponent, filtrationQuotientComponent, LinearMap.comp_apply,
    LinearEquiv.coe_coe, d.completionComponent_eq_quotientComponent ℳ J
      F.quotientAntitone hF n k hn, ModuleFiltration.limπ_completionEquivTowerLimit]

/-- Completed components of canonical elements are their original homogeneous components. -/
@[simp]
theorem filtrationCompletionComponent_of (n : N) (x : M) :
    d.filtrationCompletionComponent ℳ F hF n (F.of x) = decompose ℳ x n := by
  rw [filtrationCompletionComponent_eq_quotientComponent d ℳ F hF n (d.degree n).toNat
    (Int.self_le_toNat _), F.projection_of, filtrationQuotientComponent_mk]

/-- A completed element has order at least k + 1 exactly when its coefficients
through order k vanish. -/
theorem mem_completedFiltration_iff (x : F.completion) (k : ℕ) :
    x ∈ F.completedFiltration.submodule (k + 1) ↔
      ∀ n, d.degree n ≤ k → d.filtrationCompletionComponent ℳ F hF n x = 0 := by
  rw [ModuleFiltration.completedFiltration_succ, LinearMap.mem_ker]
  constructor
  · intro hx n hn
    rw [filtrationCompletionComponent_eq_quotientComponent d ℳ F hF n k hn, hx, map_zero]
  · intro hx
    apply (F.quotientEquivTower k).injective
    apply d.quotient_ext ℳ J F.quotientAntitone hF
    intro n hn
    rw [map_zero, map_zero]
    exact (d.filtrationCompletionComponent_eq_quotientComponent ℳ F hF n k hn x).symm.trans
      (hx n hn)

variable (hℳ : ∀ n, n ∉ d.monoid → ℳ n = ⊥)

/-- The filtration completion of a positively supported module as homogeneous coefficients. -/
noncomputable def filtrationCompletionEquivPi : F.completion ≃ₗ[R] ∀ n, ℳ n :=
  F.completionEquivTowerLimit.trans (d.completionEquivPi ℳ J F.quotientAntitone hF hℳ)

/-- The product comparison reads the completed homogeneous components. -/
@[simp]
theorem filtrationCompletionEquivPi_apply (x : F.completion) (n : N) :
    d.filtrationCompletionEquivPi ℳ F hF hℳ x n =
      d.filtrationCompletionComponent ℳ F hF n x := by
  exact d.completionEquivPi_apply ℳ J F.quotientAntitone hF hℳ (F.completionEquivTowerLimit x) n

/-- The inverse product comparison has the prescribed homogeneous coefficients. -/
@[simp]
theorem filtrationCompletionComponent_equivPi_symm (x : ∀ n, ℳ n) (n : N) :
    d.filtrationCompletionComponent ℳ F hF n ((d.filtrationCompletionEquivPi ℳ F hF hℳ).symm x) =
      x n := by
  rw [← filtrationCompletionEquivPi_apply d ℳ F hF hℳ, LinearEquiv.apply_symm_apply]

/-- At order k, the inverse product comparison is the class of the finite sum
of coefficients in the degree cutoff. -/
theorem projection_filtrationCompletionEquivPi_symm (x : ∀ n, ℳ n) (k : ℕ) :
    F.projection k ((d.filtrationCompletionEquivPi ℳ F hF hℳ).symm x) =
      Submodule.Quotient.mk (∑ n ∈ (d.finite_cutoff k).toFinset, (x n : M)) := by
  apply (F.quotientEquivTower k).injective
  rw [← ModuleFiltration.limπ_completionEquivTowerLimit, ModuleFiltration.quotientEquivTower_mk]
  simp only [filtrationCompletionEquivPi, LinearEquiv.symm_trans_apply,
    LinearEquiv.apply_symm_apply, projection_completionEquivPi_symm]

include hℳ in
/-- A finite projection is reconstructed from the completed components in its cutoff. -/
theorem projection_eq_sum_filtrationCompletionComponent (k : ℕ) (x : F.completion) :
    F.projection k x = Submodule.Quotient.mk
      (∑ n ∈ (d.finite_cutoff k).toFinset, (d.filtrationCompletionComponent ℳ F hF n x : M)) := by
  have h := d.projection_filtrationCompletionEquivPi_symm ℳ F hF hℳ
    (d.filtrationCompletionEquivPi ℳ F hF hℳ x) k
  simpa only [LinearEquiv.symm_apply_apply, filtrationCompletionEquivPi_apply] using h

end TauCeti.PositiveDegrees
