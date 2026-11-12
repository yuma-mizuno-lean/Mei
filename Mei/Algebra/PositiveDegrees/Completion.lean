/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Completion
public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.LinearAlgebra.ModuleFiltration.Completion

/-!
# Degree completions for module filtrations

Mei's compatible quotient families form a module filtration completion.
We compare these families with TauCeti's limit of the same quotient tower
and use the upstream coefficient maps and product equivalence.
-/

public section

open Opposite
open _root_.DirectSum

namespace TauCeti.PositiveDegrees

open Mei

variable {N R M : Type*} [AddCommMonoid N] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq N] (d : PositiveDegrees N) (ℳ : N → Submodule R M)
  [Decomposition ℳ] (F : ModuleFiltration R M)

private theorem quotientAntitone : Antitone (fun k => F.submodule (k + 1)) :=
  fun _ _ h => F.antitone (Nat.add_le_add_right h 1)

local notation "J" => fun k => F.submodule (k + 1)
local notation "T" => ModuleTower.quotients J (quotientAntitone F)

private def quotientComparison (k : ℕ) : F.quotient k ≃ₗ[R] (T).obj (op k) := by
  let f := (F.submodule (k + 1)).liftQ (ModuleTower.quotientsπ J (quotientAntitone F) k)
    (by rw [ModuleTower.ker_quotientsπ])
  let g := ModuleTower.quotientsLift J (quotientAntitone F) k (F.submodule (k + 1)).mkQ
    (by rw [Submodule.ker_mkQ])
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · apply ModuleTower.quotients_hom_ext J (quotientAntitone F)
    apply LinearMap.ext
    intro x
    simp [f, g, Submodule.liftQ_apply]
  · apply Submodule.linearMap_qext (F.submodule (k + 1))
    apply LinearMap.ext
    intro x
    simp [f, g, Submodule.liftQ_apply]

@[simp]
private theorem quotientComparison_mk (k : ℕ) (x : M) :
    quotientComparison F k (Submodule.Quotient.mk x) =
      ModuleTower.quotientsπ J (quotientAntitone F) k x := by
  exact Submodule.liftQ_apply _ _ x

private theorem quotientComparison_transition {k l : ℕ} (h : k ≤ l) (x : F.quotient l) :
    (T).transitionOfLE h (quotientComparison F l x) =
      quotientComparison F k (F.transition h x) := by
  obtain ⟨x, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  simp

private def completionComparison : F.completion ≃ₗ[R] (T).lim where
  toFun x := ⟨fun k => quotientComparison F k (F.projection k x),
    (T).mem_lim.mpr fun k => by
      rw [← ModuleTower.transitionOfLE_succ, quotientComparison_transition,
        F.transition_projection]⟩
  invFun y := ⟨fun k => (quotientComparison F k.unop).symm ((T).limπ k.unop y),
    (F.mem_completionSubmodule_iff _).mpr fun k l h => by
      apply (quotientComparison F k).injective
      change quotientComparison F k (F.transition h
        ((quotientComparison F l).symm ((T).limπ l y))) =
        quotientComparison F k ((quotientComparison F k).symm ((T).limπ k y))
      rw [← quotientComparison_transition, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      simpa only [ModuleTower.limπ_apply] using (T).transitionOfLE_coe_lim y h⟩
  left_inv x := by
    apply F.completion_ext
    intro k
    simp [ModuleTower.limπ_apply]
  right_inv y := by
    apply (T).lim_ext
    intro k
    simp [ModuleTower.limπ_apply]
  map_add' x y := by
    apply (T).lim_ext
    intro k
    simp [ModuleTower.limπ_apply]
  map_smul' r x := by
    apply (T).lim_ext
    intro k
    simp [ModuleTower.limπ_apply]

private theorem limπ_completionComparison (k : ℕ) (x : F.completion) :
    (T).limπ k (completionComparison F x) = quotientComparison F k (F.projection k x) := by
  rw [ModuleTower.limπ_apply]
  rfl

variable (hF : ∀ k, F.submodule (k + 1) = d.degreeSubmodule ℳ k)

/-- A homogeneous component of a finite filtration quotient. -/
def filtrationQuotientComponent (k : ℕ) (n : N) (hn : d.degree n ≤ k) :
    F.quotient k →ₗ[R] ℳ n :=
  (d.quotientComponent ℳ J (quotientAntitone F) hF k n hn).comp
    (quotientComparison F k).toLinearMap

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
    ← quotientComparison_transition F h x, quotientComponent_transition]

/-- The degree component of an element of the filtration completion. -/
def filtrationCompletionComponent (n : N) : F.completion →ₗ[R] ℳ n :=
  (d.completionComponent ℳ J (quotientAntitone F) hF n).comp (completionComparison F).toLinearMap

/-- Any cutoff containing the degree computes the same completed component. -/
theorem filtrationCompletionComponent_eq_quotientComponent (n : N) (k : ℕ)
    (hn : d.degree n ≤ k) (x : F.completion) :
    d.filtrationCompletionComponent ℳ F hF n x =
      d.filtrationQuotientComponent ℳ F hF k n hn (F.projection k x) := by
  simp only [filtrationCompletionComponent, filtrationQuotientComponent, LinearMap.comp_apply,
    LinearEquiv.coe_coe, d.completionComponent_eq_quotientComponent ℳ J
      (quotientAntitone F) hF n k hn, limπ_completionComparison]

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
    apply (quotientComparison F k).injective
    apply d.quotient_ext ℳ J (quotientAntitone F) hF
    intro n hn
    rw [map_zero, map_zero]
    exact (d.filtrationCompletionComponent_eq_quotientComponent ℳ F hF n k hn x).symm.trans
      (hx n hn)

variable (hℳ : ∀ n, n ∉ d.monoid → ℳ n = ⊥)

/-- The filtration completion of a positively supported module as homogeneous coefficients. -/
noncomputable def filtrationCompletionEquivPi : F.completion ≃ₗ[R] ∀ n, ℳ n :=
  (completionComparison F).trans (d.completionEquivPi ℳ J (quotientAntitone F) hF hℳ)

/-- The product comparison reads the completed homogeneous components. -/
@[simp]
theorem filtrationCompletionEquivPi_apply (x : F.completion) (n : N) :
    d.filtrationCompletionEquivPi ℳ F hF hℳ x n =
      d.filtrationCompletionComponent ℳ F hF n x := by
  exact d.completionEquivPi_apply ℳ J (quotientAntitone F) hF hℳ (completionComparison F x) n

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
  apply (quotientComparison F k).injective
  rw [← limπ_completionComparison, quotientComparison_mk]
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
