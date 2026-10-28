/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.LinearAlgebra.ModuleFiltration.Completion

/-!
# Degree completions as products of homogeneous pieces

The completion of a module supported on a positive degree monoid is linearly
equivalent to the product of its homogeneous pieces. Finite degree cutoffs
reconstruct each quotient from
an arbitrary family of homogeneous coefficients. Conversely, a coefficient of a
compatible quotient family is read at any cutoff containing its degree.

The construction uses Mathlib's internal direct-sum decomposition, quotient linear
maps, and the compatible-family completion `ModuleFiltration.completion`. The
filtration is supplied with its identification with the degree submodules, so the
comparison applies to existing completion carriers without replacing them. No
basis or finiteness assumption on the homogeneous modules is needed.
-/

public section

namespace Mei.PositiveDegrees

open _root_.DirectSum

variable {N R M : Type*} [AddCommMonoid N] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq N] (d : PositiveDegrees N) (ℳ : N → Submodule R M)
  [Decomposition ℳ]
  (F : ModuleFiltration R M)
  (hF : ∀ k, F.submodule (k + 1) = d.degreeSubmodule ℳ k)

private def componentLinear (n : N) : M →ₗ[R] ℳ n :=
  (DirectSum.component R N (fun n => ℳ n) n).comp (decomposeLinearEquiv ℳ).toLinearMap

/-- A homogeneous component descends to any quotient retaining its degree. -/
def quotientComponent (k : ℕ) (n : N) (hn : d.degree n ≤ k) :
    F.quotient k →ₗ[R] ℳ n :=
  (F.submodule (k + 1)).liftQ (componentLinear ℳ n) (by
    intro x hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    have hx' : x ∈ d.degreeSubmodule ℳ k := by simpa only [hF k] using hx
    exact (d.mem_degreeSubmodule_iff ℳ).mp hx' n hn)

/-- The component of a quotient class is the corresponding homogeneous component. -/
@[simp]
theorem quotientComponent_mk (k : ℕ) (n : N) (hn : d.degree n ≤ k) (x : M) :
    d.quotientComponent ℳ F hF k n hn (Submodule.Quotient.mk x) = decompose ℳ x n :=
  (F.submodule (k + 1)).liftQ_apply _ x

/-- Components already retained at the lower cutoff commute with quotient transitions. -/
@[simp]
theorem quotientComponent_transition {k l : ℕ} (h : k ≤ l) (n : N)
    (hn : d.degree n ≤ k) (x : F.quotient l) :
    d.quotientComponent ℳ F hF k n hn (F.transition h x) =
      d.quotientComponent ℳ F hF l n (hn.trans (Int.ofNat_le.mpr h)) x := by
  obtain ⟨x, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  simp

private theorem quotient_ext {k : ℕ} {x y : F.quotient k}
    (h : ∀ n (hn : d.degree n ≤ k),
      d.quotientComponent ℳ F hF k n hn x = d.quotientComponent ℳ F hF k n hn y) : x = y := by
  obtain ⟨x, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective y
  apply (Submodule.Quotient.eq (F.submodule (k + 1))).mpr
  rw [hF k, d.mem_degreeSubmodule_iff ℳ]
  intro n hn
  have he := congrArg Subtype.val (h n hn)
  simpa only [Submodule.mkQ_apply, quotientComponent_mk, decompose_sub, sub_apply,
    Submodule.coe_sub,
    sub_eq_zero] using he

/-- The degree-`n` coefficient of a completed module element. -/
def completionComponent (n : N) : F.completion →ₗ[R] ℳ n :=
  (d.quotientComponent ℳ F hF (d.degree n).toNat n (Int.self_le_toNat _)).comp
    (F.projection (d.degree n).toNat)

/-- Any cutoff containing the degree computes the same completed component. -/
theorem completionComponent_eq_quotientComponent (n : N) (k : ℕ)
    (hn : d.degree n ≤ k) (x : F.completion) :
    d.completionComponent ℳ F hF n x =
      d.quotientComponent ℳ F hF k n hn (F.projection k x) := by
  have hnk : (d.degree n).toNat ≤ k := by omega
  rw [completionComponent, LinearMap.comp_apply, ← F.transition_projection hnk x,
    quotientComponent_transition]

/-- Completed components of canonical elements are their original homogeneous components. -/
@[simp]
theorem completionComponent_of (n : N) (x : M) :
    d.completionComponent ℳ F hF n (F.of x) = decompose ℳ x n := by
  simp [completionComponent]

/-- A completed element has order at least `k + 1` exactly when its coefficients
through order `k` vanish. -/
theorem mem_completedFiltration_iff (x : F.completion) (k : ℕ) :
    x ∈ F.completedFiltration.submodule (k + 1) ↔
      ∀ n, d.degree n ≤ k → d.completionComponent ℳ F hF n x = 0 := by
  rw [ModuleFiltration.completedFiltration_succ, LinearMap.mem_ker]
  constructor
  · intro hx n hn
    rw [completionComponent_eq_quotientComponent d ℳ F hF n k hn, hx, map_zero]
  · intro hx
    apply d.quotient_ext ℳ F hF
    intro n hn
    rw [map_zero, ← completionComponent_eq_quotientComponent]
    exact hx n hn

private noncomputable def finiteApprox (k : ℕ) : (∀ n, ℳ n) →ₗ[R] M :=
  ∑ n ∈ (d.finite_cutoff k).toFinset, (ℳ n).subtype.comp (LinearMap.proj n)

variable (hℳ : ∀ n, n ∉ d.monoid → ℳ n = ⊥)

include hℳ in
private theorem decompose_finiteApprox (k : ℕ) (x : ∀ n, ℳ n) (n : N)
    (hn : d.degree n ≤ k) :
    decompose ℳ (d.finiteApprox ℳ k x) n = x n := by
  classical
  apply Subtype.ext
  by_cases hP : n ∈ d.monoid
  · have hn' : n ∈ (d.finite_cutoff k).toFinset := by simp [hP, hn]
    simp only [finiteApprox, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply, decompose_sum, sum_apply,
      Submodule.coe_sum]
    rw [Finset.sum_eq_single n]
    · exact decompose_of_mem_same ℳ (x n).property
    · intro m hm hmn
      exact decompose_of_mem_ne ℳ (x m).property hmn
    · exact fun h => (h hn').elim
  · have hb : ℳ n = ⊥ := hℳ n hP
    have hz (y : ℳ n) : (y : M) = 0 := by simpa only [hb, Submodule.mem_bot] using y.property
    exact (hz _).trans (hz _).symm

private noncomputable def piToQuotient (k : ℕ) : (∀ n, ℳ n) →ₗ[R] F.quotient k :=
  (F.submodule (k + 1)).mkQ.comp (d.finiteApprox ℳ k)

include hℳ in
private theorem quotientComponent_piToQuotient (k : ℕ) (n : N)
    (hn : d.degree n ≤ k) (x : ∀ n, ℳ n) :
    d.quotientComponent ℳ F hF k n hn (d.piToQuotient ℳ F k x) = x n := by
  rw [piToQuotient, LinearMap.comp_apply, Submodule.mkQ_apply, quotientComponent_mk]
  exact d.decompose_finiteApprox ℳ hℳ k x n hn

include hℳ in
private noncomputable def piToCompletion : (∀ n, ℳ n) →ₗ[R] F.completion :=
  F.lift (d.piToQuotient ℳ F) (by
    intro k l h
    apply LinearMap.ext
    intro x
    apply d.quotient_ext ℳ F hF
    intro n hn
    simp only [LinearMap.comp_apply, quotientComponent_transition,
      d.quotientComponent_piToQuotient ℳ F hF hℳ])

private theorem completionComponent_piToCompletion (n : N) (x : ∀ n, ℳ n) :
    d.completionComponent ℳ F hF n (d.piToCompletion ℳ F hF hℳ x) = x n := by
  rw [completionComponent, LinearMap.comp_apply, piToCompletion, F.projection_lift]
  exact d.quotientComponent_piToQuotient ℳ F hF hℳ _ n _ x

include hℳ in
/-- The degree completion of a module supported on the positive monoid is the product of its
homogeneous pieces. Finite degree cutoffs reconstruct the inverse. -/
noncomputable def completionEquivPi : F.completion ≃ₗ[R] ∀ n, ℳ n :=
  LinearEquiv.ofLinearMap (LinearMap.pi (d.completionComponent ℳ F hF))
    (d.piToCompletion ℳ F hF hℳ)
    (by
      apply LinearMap.ext
      intro x
      funext n
      exact d.completionComponent_piToCompletion ℳ F hF hℳ n x)
    (by
      apply LinearMap.ext
      intro x
      apply F.completion_ext
      intro k
      apply d.quotient_ext ℳ F hF
      intro n hn
      rw [← completionComponent_eq_quotientComponent,
        ← completionComponent_eq_quotientComponent]
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.id_apply,
        d.completionComponent_piToCompletion ℳ F hF hℳ])

/-- The product comparison reads the completed homogeneous components. -/
@[simp]
theorem completionEquivPi_apply (x : F.completion) (n : N) :
    d.completionEquivPi ℳ F hF hℳ x n = d.completionComponent ℳ F hF n x := (rfl)

/-- The inverse product comparison has the prescribed homogeneous coefficients. -/
@[simp]
theorem completionComponent_completionEquivPi_symm (x : ∀ n, ℳ n) (n : N) :
    d.completionComponent ℳ F hF n ((d.completionEquivPi ℳ F hF hℳ).symm x) = x n :=
  d.completionComponent_piToCompletion ℳ F hF hℳ n x

/-- At order `k`, the inverse product comparison is the class of the finite sum
of coefficients in the degree cutoff. -/
theorem projection_completionEquivPi_symm (x : ∀ n, ℳ n) (k : ℕ) :
    F.projection k ((d.completionEquivPi ℳ F hF hℳ).symm x) =
      Submodule.Quotient.mk (∑ n ∈ (d.finite_cutoff k).toFinset, (x n : M)) := by
  classical
  calc
    _ = d.piToQuotient ℳ F k x := F.projection_lift _ _ k x
    _ = _ := by
      simp only [piToQuotient, LinearMap.comp_apply, Submodule.mkQ_apply,
        finiteApprox, LinearMap.sum_apply, LinearMap.proj_apply, Submodule.subtype_apply]

include hℳ in
/-- A finite projection is reconstructed from the completed components in its cutoff. -/
theorem projection_eq_sum_completionComponent (k : ℕ) (x : F.completion) :
    F.projection k x = Submodule.Quotient.mk
      (∑ n ∈ (d.finite_cutoff k).toFinset, (d.completionComponent ℳ F hF n x : M)) := by
  have h := d.projection_completionEquivPi_symm ℳ F hF hℳ
    (d.completionEquivPi ℳ F hF hℳ x) k
  simpa only [LinearEquiv.symm_apply_apply, completionEquivPi_apply] using h

end Mei.PositiveDegrees
