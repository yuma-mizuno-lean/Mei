/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Equiv
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Completing direct sums of filtered modules

The completion of a direct sum consists of families in the coefficient completion
whose projections have finite support at every order. The family itself need not
have finite support. This describes completed expansions in an infinite basis,
where more basis vectors may appear as the cutoff increases.

The construction uses `Finsupp.submodule`, `Finsupp.mapRange.linearMap`, and
`LinearMap.quotKerEquivOfSurjective` for the finite quotients, and reads each completed
coefficient with `ModuleFiltration.completionMap` of `Finsupp.lapply`. The inverse assembles
the finite coefficient vectors with `Finsupp.ofSupportFinite` and the universal
property of `ModuleFiltration.completion`.
-/

public section

noncomputable section

namespace Mei.ModuleFiltration

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (F : ModuleFiltration R M) (ι : Type*)

/-- Filter a direct sum by requiring every coefficient to lie in the given term. -/
def finsupp : ModuleFiltration R (ι →₀ M) where
  submodule k := Finsupp.submodule fun _ => F.submodule k
  antitone _ _ h _ hx i := F.antitone h (hx i)
  zero_eq_top := by simp

/-- Membership in the direct-sum filtration is coefficientwise membership. -/
@[simp]
theorem mem_finsupp_submodule (k : ℕ) (x : ι →₀ M) :
    x ∈ (F.finsupp ι).submodule k ↔ ∀ i, x i ∈ F.submodule k := Iff.rfl

/-- Each direct-sum filtration term is Mathlib's coefficientwise submodule. -/
theorem finsupp_submodule (k : ℕ) :
    (F.finsupp ι).submodule k = Finsupp.submodule fun _ => F.submodule k := by
  ext x
  rw [mem_finsupp_submodule, Finsupp.mem_submodule_iff]

end Semiring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) (ι : Type*)

/-- The finite quotient of a direct sum is the direct sum of finite quotients. -/
def finsuppQuotientEquiv (k : ℕ) :
    (F.finsupp ι).quotient k ≃ₗ[R] (ι →₀ F.quotient k) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Finsupp.ker_mapRange, Submodule.ker_mkQ, finsupp_submodule])).trans
    ((Finsupp.mapRange.linearMap (F.submodule (k + 1)).mkQ).quotKerEquivOfSurjective
      (by exact Finsupp.mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective _)))

/-- On representatives, the quotient dictionary takes each coefficient's class. -/
@[simp]
theorem finsuppQuotientEquiv_mk (k : ℕ) (x : ι →₀ M) (i : ι) :
    F.finsuppQuotientEquiv ι k (Submodule.Quotient.mk x) i =
      Submodule.Quotient.mk (x i) := by
  exact congrArg (fun y : ι →₀ F.quotient k => y i)
    ((Finsupp.mapRange.linearMap (F.submodule (k + 1)).mkQ).quotKerEquivOfSurjective_apply_mk
      (by exact Finsupp.mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective _)) x)

/-- The inverse quotient dictionary assembles coefficientwise classes into one class. -/
@[simp]
theorem finsuppQuotientEquiv_symm_mapRange_mk (k : ℕ) (x : ι →₀ M) :
    (F.finsuppQuotientEquiv ι k).symm
        (x.mapRange Submodule.Quotient.mk (Submodule.Quotient.mk_zero _)) =
      Submodule.Quotient.mk x := by
  rw [LinearEquiv.symm_apply_eq]
  ext i
  simp

/-- The finite coefficient dictionaries commute with quotient transitions. -/
@[simp]
theorem finsuppQuotientEquiv_transition {k l : ℕ} (h : k ≤ l)
    (x : (F.finsupp ι).quotient l) (i : ι) :
    F.finsuppQuotientEquiv ι k ((F.finsupp ι).transition h x) i =
      F.transition h (F.finsuppQuotientEquiv ι l x i) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((F.finsupp ι).submodule (l + 1)) x
  simp

/-- Families of completed coefficients with finite support at every finite order. -/
def restrictedFamilies : Submodule R (ι → F.completion) where
  carrier := {x | ∀ k, (Function.support fun i => F.projection k (x i)).Finite}
  zero_mem' := by simp
  add_mem' {x y} hx hy k := by
    apply Set.Finite.subset (Function.HasFiniteSupport.add
      (f := fun i => F.projection k (x i)) (g := fun i => F.projection k (y i))
      (hx k) (hy k))
    intro i hi
    simpa only [Function.mem_support, Pi.add_apply, map_add] using hi
  smul_mem' r x hx k := by
    apply Set.Finite.subset (Function.HasFiniteSupport.smul_right (fun _ : ι => r) (hx k))
    intro i hi
    simpa only [Function.mem_support, Pi.smul_apply, Pi.smul_apply', map_smul] using hi

/-- The restriction is finiteness of the surviving indices, at each cutoff separately. -/
@[simp]
theorem mem_restrictedFamilies (x : ι → F.completion) :
    x ∈ F.restrictedFamilies ι ↔
      ∀ k, (Function.support fun i => F.projection k (x i)).Finite := Iff.rfl

private theorem finsupp_le_comap_lapply (i : ι) (k : ℕ) :
    (F.finsupp ι).submodule (id k + 1) ≤ (F.submodule (k + 1)).comap (Finsupp.lapply i) :=
  fun _ hx => (F.mem_finsupp_submodule ι _ _).mp hx i

/-- Read one completed coefficient from a completed direct sum. -/
def completedCoefficient (i : ι) : (F.finsupp ι).completion →ₗ[R] F.completion :=
  (F.finsupp ι).completionMap F (Finsupp.lapply i) id monotone_id
    (F.finsupp_le_comap_lapply ι i)

/-- Projecting a completed coefficient reads the corresponding finite coefficient. -/
@[simp]
theorem projection_completedCoefficient (i : ι) (k : ℕ) (x : (F.finsupp ι).completion) :
    F.projection k (F.completedCoefficient ι i x) =
      F.finsuppQuotientEquiv ι k ((F.finsupp ι).projection k x) i := by
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _ ((F.finsupp ι).projection k x)
  rw [completedCoefficient, projection_completionMap]
  simp only [id_eq, ← hy]
  simp

private def toRestrictedFamilies : (F.finsupp ι).completion →ₗ[R] F.restrictedFamilies ι :=
  (LinearMap.pi (F.completedCoefficient ι)).codRestrict _ fun x k => by
    simpa only [LinearMap.pi_apply, projection_completedCoefficient,
      Function.HasFiniteSupport] using
      (F.finsuppQuotientEquiv ι k ((F.finsupp ι).projection k x)).hasFiniteSupport

private def restrictedProjection (k : ℕ) : F.restrictedFamilies ι →ₗ[R] (ι →₀ F.quotient k) where
  toFun x := Finsupp.ofSupportFinite (fun i => F.projection k (x.val i)) (x.property k)
  map_add' _ _ := by ext i; simp [Finsupp.ofSupportFinite_coe]
  map_smul' _ _ := by ext i; simp [Finsupp.ofSupportFinite_coe]

private theorem restrictedProjection_apply (k : ℕ) (x : F.restrictedFamilies ι) (i : ι) :
    F.restrictedProjection ι k x i = F.projection k (x.val i) := (rfl)

private theorem toRestrictedFamilies_apply (x : (F.finsupp ι).completion) (i : ι) :
    (F.toRestrictedFamilies ι x).val i = F.completedCoefficient ι i x := (rfl)

private def fromRestrictedFamilies : F.restrictedFamilies ι →ₗ[R] (F.finsupp ι).completion := by
  let f : ∀ k, F.restrictedFamilies ι →ₗ[R] (F.finsupp ι).quotient k :=
    fun k => (F.finsuppQuotientEquiv ι k).symm.toLinearMap.comp (F.restrictedProjection ι k)
  refine (F.finsupp ι).lift (X := F.restrictedFamilies ι) f ?_
  intro k l h
  apply LinearMap.ext
  intro x
  simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
  apply (F.finsuppQuotientEquiv ι k).injective
  apply Finsupp.ext
  intro i
  simp only [finsuppQuotientEquiv_transition, LinearEquiv.apply_symm_apply,
    restrictedProjection_apply, transition_projection]

/-- Completing a direct sum gives precisely the families of completed coefficients
that have finite support at every cutoff. No bound on the full support is imposed. -/
def finsuppCompletionEquiv : (F.finsupp ι).completion ≃ₗ[R] F.restrictedFamilies ι where
  __ := F.toRestrictedFamilies ι
  invFun := F.fromRestrictedFamilies ι
  left_inv x := by
    apply completion_ext
    intro k
    apply (F.finsuppQuotientEquiv ι k).injective
    ext i
    simp [fromRestrictedFamilies, restrictedProjection_apply, toRestrictedFamilies_apply]
  right_inv x := by
    apply Subtype.ext
    funext i
    apply completion_ext
    intro k
    simp [fromRestrictedFamilies, restrictedProjection_apply, toRestrictedFamilies_apply]

/-- The completed dictionary's coordinates are the completed coefficient maps. -/
@[simp]
theorem finsuppCompletionEquiv_apply (x : (F.finsupp ι).completion) (i : ι) :
    (F.finsuppCompletionEquiv ι x).val i = F.completedCoefficient ι i x := (rfl)

/-- The inverse dictionary recovers a finite coefficient vector at each cutoff. -/
@[simp]
theorem finsuppQuotientEquiv_projection_finsuppCompletionEquiv_symm
    (x : F.restrictedFamilies ι) (k : ℕ) (i : ι) :
    F.finsuppQuotientEquiv ι k
      ((F.finsupp ι).projection k ((F.finsuppCompletionEquiv ι).symm x)) i =
        F.projection k (x.val i) := by
  simp [finsuppCompletionEquiv, fromRestrictedFamilies, restrictedProjection_apply]

/-- A finite expansion retains each of its coefficients under completion. -/
@[simp]
theorem completedCoefficient_of (x : ι →₀ M) (i : ι) :
    F.completedCoefficient ι i ((F.finsupp ι).of x) = F.of (x i) :=
  (F.finsupp ι).completionMap_of F (Finsupp.lapply i) id monotone_id
    (F.finsupp_le_comap_lapply ι i) x

/-- The canonical images of the coefficients of a finite expansion are admissible. -/
theorem of_comp_mem_restrictedFamilies (x : ι →₀ M) :
    F.of ∘ x ∈ F.restrictedFamilies ι := fun k =>
  x.hasFiniteSupport.fun_comp (g := (F.projection k).comp F.of) (map_zero _)

/-- The inverse dictionary sends the canonical images of finitely many coefficients
to the canonical image of their expansion. -/
@[simp]
theorem finsuppCompletionEquiv_symm_of (x : ι →₀ M) :
    (F.finsuppCompletionEquiv ι).symm ⟨F.of ∘ x, F.of_comp_mem_restrictedFamilies ι x⟩ =
      (F.finsupp ι).of x := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext i
  simp

end Mei.ModuleFiltration
