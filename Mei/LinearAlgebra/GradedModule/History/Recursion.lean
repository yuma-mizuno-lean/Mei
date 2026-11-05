/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.End.Recursion
public import Mei.LinearAlgebra.GradedModule.History.Uniform
public import Mei.LinearAlgebra.GradedModule.History.Filtration

/-!
# Homogeneous histories of finite recursion solutions

The finite geometric solution operator of `Module.End.finiteRecursion` expands
as the finite sum of homogeneous histories of every length below its bound.
For a nilpotent endomorphism, every solution of `x = a + U x` equals this sum.
Only the histories of each actual input are needed; the grading may be infinite.

Uniform finite support on an input range gives the corresponding identity of
linear maps, including after any final linear output map. Finite generation of
that range supplies such supports through `exists_uniform_homogeneousHistory_support`.
A finitely generated input range also supplies uniform supports for any linear
family of nilpotent recursion solutions, followed by any linear output map.
If each component transfer raises a finite-length filtration, long histories vanish
individually. Hence arbitrary selected history sums stabilize at the filtration length,
also after a linear output map. Nilpotence of the total operator alone would not
justify this statement for selected histories, because of possible cancellation.
All statements hold over a semiring and semimodule; no additive cancellation is assumed.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  (U : Module.End R M)

/-- The finite recursion operator is the sum of all contributing histories
of every length below its bound, without a finite ambient grading. -/
theorem sum_sum_homogeneousHistory_eq_finiteRecursion (r : ℕ) (a : M) :
    (∑ j ∈ Finset.range r,
      ∑ p ∈ homogeneousHistorySupport ℳ (fun _ : Fin j => U) a,
        homogeneousHistory ℳ (fun _ : Fin j => U) p a) = U.finiteRecursion r a := by
  simp only [sum_homogeneousHistory, List.ofFn_const, List.prod_replicate,
    Module.End.finiteRecursion_apply]

/-- Every solution of a nilpotent recursion equals its finite homogeneous
history expansion. No additive cancellation is assumed. -/
theorem eq_sum_sum_homogeneousHistory_of_eq_add {r : ℕ} (hU : U ^ r = 0)
    {a x : M} (hx : x = a + U x) :
    x = ∑ j ∈ Finset.range r,
      ∑ p ∈ homogeneousHistorySupport ℳ (fun _ : Fin j => U) a,
        homogeneousHistory ℳ (fun _ : Fin j => U) p a := by
  rw [sum_sum_homogeneousHistory_eq_finiteRecursion]
  exact U.eq_finiteRecursion_of_eq_add hU hx

/-- Uniform finite history supports give the finite recursion as a linear-map
identity on the input range, also after any final projection or linear output map. -/
theorem sum_sum_comp_homogeneousHistory_comp_eq_comp_finiteRecursion_comp
    {E N : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid N] [Module R N]
    (a : E →ₗ[R] M) (b : M →ₗ[R] N) (r : ℕ)
    (S : (j : ℕ) → Finset (Fin j → ι))
    (hS : ∀ j < r, ∀ p ∉ S j, (homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a = 0) :
    (∑ j ∈ Finset.range r,
      ∑ p ∈ S j, b.comp ((homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a)) =
      b.comp ((U.finiteRecursion r).comp a) := by
  calc
    _ = ∑ j ∈ Finset.range r, b.comp (((List.ofFn fun _ : Fin j => U).prod).comp a) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_comp_homogeneousHistory_comp_eq ℳ (fun _ : Fin j => U) a b (S j)
        (hS j (Finset.mem_range.mp hj))
    _ = _ := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, List.ofFn_const,
        List.prod_replicate, Module.End.finiteRecursion_apply, map_sum]

/-- A finitely generated input range gives a uniform finite history expansion
of any linear family solving a nilpotent recursion, after any linear output map.
The same history supports work for all inputs, without a finite ambient grading. -/
theorem exists_uniform_homogeneousHistory_expansion_of_eq_add
    {E N : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid N] [Module R N]
    (a : E →ₗ[R] M) (ha : (LinearMap.range a).FG)
    {r : ℕ} (hU : U ^ r = 0) (x : E →ₗ[R] M) (hx : x = a + U.comp x)
    (b : M →ₗ[R] N) :
    ∃ S : (j : ℕ) → Finset (Fin j → ι),
      (∀ j < r, ∀ p ∉ S j, (homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a = 0) ∧
      (∑ j ∈ Finset.range r,
        ∑ p ∈ S j, b.comp ((homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a)) =
        b.comp x := by
  classical
  have hs (j : ℕ) := exists_uniform_homogeneousHistory_support ℳ
    (fun _ : Fin j => U) a ha
  choose S hS using hs
  have hsol : x = (U.finiteRecursion r).comp a := by
    apply LinearMap.ext
    intro z
    exact U.eq_finiteRecursion_of_eq_add hU (LinearMap.congr_fun hx z)
  refine ⟨S, fun j _ => hS j, ?_⟩
  rw [hsol]
  exact sum_sum_comp_homogeneousHistory_comp_eq_comp_finiteRecursion_comp
    ℳ U a b r S (fun j _ => hS j)

/-- When every component transfer raises a filtration vanishing at order `r`,
each history of length at least `r` vanishes individually. Nilpotence of the sum
of the component transfers alone would not suffice for this conclusion. -/
theorem homogeneousHistory_eq_zero_of_filtration
    (F : ModuleFiltration R M)
    (hU : ∀ i k x, x ∈ F.submodule k →
      homogeneousComponent ℳ i (U x) ∈ F.submodule (k + 1))
    {r n : ℕ} (hr : F.submodule r = ⊥) (hn : r ≤ n) (p : Fin n → ι) :
    homogeneousHistory ℳ (fun _ : Fin n => U) p = 0 := by
  have hraise : ComponentTransfersRaise
      (M := fun _ : Quiver.SingleObj Unit => M) (T := fun _ => U) (ℳ := fun _ => ℳ)
      (F := fun _ => F) (w := fun _ _ _ => 1) := by
    rw [componentTransfersRaise_iff]
    intro b c e i j k y _ hy
    exact hU j k y hy
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy, add_zero]
  | @homogeneous i x =>
    by_contra hne
    rw [homogeneousHistory_eq_pathOfFn ℳ (fun _ : Unit => U) (fun _ : Fin n => ())] at hne
    have hlt := Quiver.Path.componentWeight_lt_of_homogeneousHistory_ne_zero
      (Quiver.SingleObj.pathOfFn (fun _ : Fin n => ())) hraise i x.property hr hne
    rw [Quiver.Path.Degrees.addWeight_componentWeight_liftPath,
      Quiver.SingleObj.addWeight_one_pathOfFn] at hlt
    exact (not_lt_of_ge hn) hlt

open Classical in
/-- Incidence-selected history sums stabilize once their cutoff reaches the
filtration length, including after any linear output map. Selection need not
include all histories, and no support assumption on the finite sets is needed. -/
theorem sum_ite_comp_homogeneousHistory_comp_eq_of_filtration
    {E N : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid N] [Module R N]
    (F : ModuleFiltration R M)
    (hU : ∀ i k x, x ∈ F.submodule k →
      homogeneousComponent ℳ i (U x) ∈ F.submodule (k + 1))
    {r s : ℕ} (hr : F.submodule r = ⊥) (hrs : r ≤ s)
    (a : E →ₗ[R] M) (b : M →ₗ[R] N)
    (S : (j : ℕ) → Finset (Fin j → ι)) (P : (j : ℕ) → (Fin j → ι) → Prop) :
    (∑ j ∈ Finset.range s, ∑ p ∈ (S j).filter (P j),
      b.comp ((homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a)) =
    ∑ j ∈ Finset.range r, ∑ p ∈ (S j).filter (P j),
      b.comp ((homogeneousHistory ℳ (fun _ : Fin j => U) p).comp a) := by
  symm
  apply Finset.sum_subset (Finset.range_mono hrs)
  intro j _ hj
  have hrj : r ≤ j := Nat.le_of_not_gt (by simpa using hj)
  apply Finset.sum_eq_zero
  intro p _
  rw [homogeneousHistory_eq_zero_of_filtration ℳ U F hU hr hrj p,
    LinearMap.zero_comp, LinearMap.comp_zero]

end Mei
