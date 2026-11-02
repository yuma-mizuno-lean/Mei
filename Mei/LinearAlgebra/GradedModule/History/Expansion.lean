/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Uniform
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform finite expansions of homogeneous histories

When all nonzero homogeneous pieces lie in a fixed finite set, a composite of
linear maps is the sum of its whole-component history maps over that set.
Unlike the support of a single input, this finite index set works simultaneously
for every coefficient, without a finite generation assumption on the modules.
Thus the expansion is an identity of linear maps, suitable for coefficient
identities with a variable incoming parameter.

`sum_homogeneousHistory_comp_eq` in `History/Uniform.lean` gives the version
for a uniform support on the range of an input map, which also covers
infinitely supported gradings.

Selecting the histories with a prescribed terminal degree isolates the final
component of the composite
(`sum_homogeneousHistory_terminal_eq_homogeneousComponent_comp_prod`), with the
uniform linear-map version `sum_homogeneousHistory_terminal_comp_eq`.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- A history using a degree outside the finite support of the grading is the
zero linear map, independently of its input. -/
theorem homogeneousHistory_eq_zero_of_notMem_piFinset (S : Finset ι)
    (hS : ∀ i, i ∉ S → ℳ i = ⊥) {n : ℕ} (T : Fin n → Module.End R M)
    (p : Fin n → ι) (hp : p ∉ Fintype.piFinset (fun _ => S)) :
    homogeneousHistory ℳ T p = 0 := by
  apply LinearMap.ext
  intro x
  by_contra hx
  apply hp
  apply Fintype.mem_piFinset.mpr
  intro j
  by_contra hj
  have hstage := homogeneousHistoryStage_mem ℳ T p x j
  rw [hS _ hj, Submodule.mem_bot] at hstage
  exact homogeneousHistoryStage_ne_zero ℳ T p hx j.castSucc hstage

/-- Two history blocks over a grading with finite support have a nested finite
expansion between arbitrary input and output linear maps. The right block acts
first, and both history index sets are independent of the input. -/
theorem sum_sum_comp_homogeneousHistory_comp_eq (S : Finset ι)
    (hS : ∀ i, i ∉ S → ℳ i = ⊥) {n m : ℕ}
    (T : Fin n → Module.End R M) (U : Fin m → Module.End R M)
    {E O : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid O] [Module R O]
    (a : E →ₗ[R] M) (b : M →ₗ[R] O) :
    (∑ r ∈ Fintype.piFinset (fun _ : Fin m => S),
      ∑ s ∈ Fintype.piFinset (fun _ : Fin n => S),
        b.comp ((homogeneousHistory ℳ T s).comp
          ((homogeneousHistory ℳ U r).comp a))) =
      b.comp ((List.ofFn T).prod.comp ((List.ofFn U).prod.comp a)) := by
  classical
  have hz {l : ℕ} (v : Fin l → Module.End R M) (c : E →ₗ[R] M)
      (r : Fin l → ι) (hr : r ∉ Fintype.piFinset (fun _ => S)) :
      (homogeneousHistory ℳ v r).comp c = 0 := by
    rw [homogeneousHistory_eq_zero_of_notMem_piFinset ℳ S hS v r hr,
      LinearMap.zero_comp]
  simp_rw [sum_comp_homogeneousHistory_comp_eq ℳ T _ b _ (hz T _)]
  simpa only [LinearMap.comp_assoc] using
    sum_comp_homogeneousHistory_comp_eq ℳ U a (b.comp (List.ofFn T).prod) _ (hz U a)

/-- If the grading is supported on a finite set, summing all history maps over
that set recovers the composite as a linear map. The same index set works for
every input; zero component maps contribute zero. -/
theorem sum_homogeneousHistory_eq_prod (S : Finset ι)
    (hS : ∀ i, i ∉ S → ℳ i = ⊥) {n : ℕ} (T : Fin n → Module.End R M) :
    ∑ p : Fin n → S, homogeneousHistory ℳ T (fun j => (p j).val) =
      (List.ofFn T).prod := by
  classical
  let embed : (Fin n → S) → (Fin n → ι) := fun p j => (p j).val
  have hinj : Function.Injective embed := by
    intro p q hpq
    funext j
    exact Subtype.ext (congrFun hpq j)
  have hzero (p : Fin n → ι) (hp : p ∉ Finset.univ.image embed) :
      (homogeneousHistory ℳ T p).comp LinearMap.id = 0 := by
    have hp' : p ∉ Fintype.piFinset (fun _ => S) := by
      intro hmem
      exact hp (Finset.mem_image.mpr
        ⟨fun j => ⟨p j, (Fintype.mem_piFinset.mp hmem) j⟩, Finset.mem_univ _, rfl⟩)
    rw [homogeneousHistory_eq_zero_of_notMem_piFinset ℳ S hS T p hp', LinearMap.zero_comp]
  have he := sum_homogeneousHistory_comp_eq ℳ T LinearMap.id
    (Finset.univ.image embed) hzero
  rw [Finset.sum_image (fun p _ q _ hpq => hinj hpq)] at he
  simpa only [LinearMap.comp_id] using he

section Terminal

/-- Within a grading with finite support, selecting the histories with terminal
degree `η` isolates the final `η`-component of the composite. Histories with a
different terminal degree contribute zero. -/
theorem sum_homogeneousHistory_terminal_eq_homogeneousComponent_comp_prod
    (S : Finset ι) (hS : ∀ i, i ∉ S → ℳ i = ⊥) {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (η : ι) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) → S => (p 0 : ι) = η),
        homogeneousHistory ℳ T (fun j => (p j).val) =
      (homogeneousComponent ℳ η).comp (List.ofFn T).prod := by
  classical
  ext a
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_filter]
  calc ∑ p : Fin (n + 1) → S,
        (if (p 0 : ι) = η then homogeneousHistory ℳ T (fun j => (p j).val) a else 0)
      = ∑ p : Fin (n + 1) → S,
          homogeneousComponent ℳ η
            (homogeneousHistory ℳ T (fun j => (p j).val) a) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with hp
        · have h := LinearMap.congr_fun
            (homogeneousComponent_comp_homogeneousHistory ℳ T (fun j => (p j).val)) a
          rw [hp] at h
          exact h.symm
        · have h := LinearMap.congr_fun
            (homogeneousComponent_comp_homogeneousHistory_of_ne ℳ T (fun j => (p j).val) η
              hp) a
          exact h.symm
    _ = homogeneousComponent ℳ η
          (∑ p : Fin (n + 1) → S, homogeneousHistory ℳ T (fun j => (p j).val) a) :=
        (map_sum _ _ _).symm
    _ = homogeneousComponent ℳ η ((List.ofFn T).prod a) := by
        have h := LinearMap.congr_fun (sum_homogeneousHistory_eq_prod ℳ S hS T) a
        rw [LinearMap.sum_apply] at h
        exact congrArg (homogeneousComponent ℳ η) h

/-- With a uniform finite contributing support on the input range, the final
`η`-component along the composite is the sum of the histories with terminal
degree `η`. The ambient grading may be infinite, and the identity is one of
linear maps. -/
theorem sum_homogeneousHistory_terminal_comp_eq
    {E : Type*} [AddCommMonoid E] [Module R E]
    (a : E →ₗ[R] M) {n : ℕ} (T : Fin (n + 1) → Module.End R M)
    (S : Finset (Fin (n + 1) → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0) (η : ι) :
    ((homogeneousComponent ℳ η).comp (List.ofFn T).prod).comp a =
      ∑ p ∈ S.filter (fun p => p 0 = η),
        (homogeneousHistory ℳ T p).comp a := by
  classical
  ext x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_filter]
  calc homogeneousComponent ℳ η ((List.ofFn T).prod (a x))
      = homogeneousComponent ℳ η (∑ p ∈ S, homogeneousHistory ℳ T p (a x)) := by
        have h := LinearMap.congr_fun (sum_homogeneousHistory_comp_eq ℳ T a S hS) x
        simpa only [LinearMap.sum_apply, LinearMap.comp_apply] using
          (congrArg (homogeneousComponent ℳ η) h).symm
    _ = ∑ p ∈ S, homogeneousComponent ℳ η (homogeneousHistory ℳ T p (a x)) :=
        map_sum _ _ _
    _ = ∑ p ∈ S, if p 0 = η then homogeneousHistory ℳ T p (a x) else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with hp
        · have h := LinearMap.congr_fun
            (homogeneousComponent_comp_homogeneousHistory ℳ T p) (a x)
          rwa [hp] at h
        · exact LinearMap.congr_fun
            (homogeneousComponent_comp_homogeneousHistory_of_ne ℳ T p η hp) (a x)

end Terminal

end Mei
