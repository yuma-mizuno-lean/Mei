/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Finite
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Uniform history expansions on an input submodule

A finite set containing all contributing histories on the range of an input
linear map gives an identity of linear maps. The ambient grading can have
infinitely many nonzero pieces, and the input module need not be finite.
Finite generation of the input range is a sufficient condition for such a
finite set to exist.

Selected history sums are independent of the chosen uniform support and commute
with coefficient specialization after grouping by the degree map. Cancellations
are allowed; no bijection of surviving histories is asserted.

These are the constant-chain cases of the uniform expansion theorems for
`chainHistory` in `Mei.LinearAlgebra.GradedModule.History.Chain`, and the
linear-map versions of `sum_homogeneousHistory` and `map_sum_ite_homogeneousHistory`.
-/

public noncomputable section

namespace Mei

variable {R M E ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid E] [Module R E] [DecidableEq ι]
  (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  {n : ℕ} (T : Fin n → Module.End R M) (a : E →ₗ[R] M)

/-- A uniform support of history maps contains the pointwise support of every input. -/
theorem homogeneousHistorySupport_subset_of_comp_eq_zero (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0) (x : E) :
    homogeneousHistorySupport ℳ T (a x) ⊆ S := by
  simp only [homogeneousHistory_eq_chainHistory] at hS
  rw [homogeneousHistorySupport_eq_chainHistorySupport]
  exact chainHistorySupport_subset_of_comp_eq_zero (fun _ => ℳ) T a S hS x

/-- Uniform finite contributing support on the input range suffices for a
linear-map expansion. No global finiteness of homogeneous pieces is required. -/
theorem sum_homogeneousHistory_comp_eq (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0) :
    ∑ p ∈ S, (homogeneousHistory ℳ T p).comp a = ((List.ofFn T).prod).comp a := by
  simp only [homogeneousHistory_eq_chainHistory, ← chainComp_const] at hS ⊢
  exact sum_chainHistory_comp_eq (fun _ => ℳ) T a S hS

/-- Final projection (or any linear output map) commutes with the shared
uniform expansion. The support bound is imposed before projection. -/
theorem sum_comp_homogeneousHistory_comp_eq
    {F : Type*} [AddCommMonoid F] [Module R F] (b : M →ₗ[R] F)
    (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0) :
    ∑ p ∈ S, b.comp ((homogeneousHistory ℳ T p).comp a) =
      b.comp (((List.ofFn T).prod).comp a) := by
  rw [← sum_homogeneousHistory_comp_eq ℳ T a S hS]
  ext x
  simp

/-- A finite generating set of inputs gives a uniform finite history support
on its entire span. This includes arbitrary scalar combinations of generators. -/
theorem exists_uniform_homogeneousHistory_support_of_fg (P : Submodule R M) (hP : P.FG) :
    ∃ S : Finset (Fin n → ι), ∀ p ∉ S, ∀ x ∈ P, homogeneousHistory ℳ T p x = 0 := by
  simp only [homogeneousHistory_eq_chainHistory]
  exact exists_uniform_chainHistory_support_of_fg (fun _ => ℳ) T P hP

/-- Finite generation of the input range, not of the ambient graded module,
ensures the uniform support needed for the linear-map expansion. -/
theorem exists_uniform_homogeneousHistory_support (ha : (LinearMap.range a).FG) :
    ∃ S : Finset (Fin n → ι), ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0 := by
  simp only [homogeneousHistory_eq_chainHistory]
  exact exists_uniform_chainHistory_support (fun _ => ℳ) T a ha

open Classical in
/-- Selecting histories in a uniform support gives the same value as selecting
in the pointwise nonzero support. Zero terms are retained in the linear-map sum. -/
theorem sum_ite_homogeneousHistory_comp_apply (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0)
    (P : (Fin n → ι) → Prop) (x : E) :
    (∑ p ∈ S, if P p then (homogeneousHistory ℳ T p).comp a else 0) x =
      ∑ p ∈ homogeneousHistorySupport ℳ T (a x),
        if P p then homogeneousHistory ℳ T p (a x) else 0 := by
  simp only [homogeneousHistory_eq_chainHistory,
    homogeneousHistorySupport_eq_chainHistorySupport] at hS ⊢
  exact sum_ite_chainHistory_comp_apply (fun _ => ℳ) T a S hS P x

open Classical in
/-- Selected linear-map sums agree over any two uniform supports. -/
theorem sum_ite_homogeneousHistory_comp_eq (S S' : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0)
    (hS' : ∀ p ∉ S', (homogeneousHistory ℳ T p).comp a = 0)
    (P : (Fin n → ι) → Prop) :
    (∑ p ∈ S, if P p then (homogeneousHistory ℳ T p).comp a else 0) =
      ∑ p ∈ S', if P p then (homogeneousHistory ℳ T p).comp a else 0 := by
  simp only [homogeneousHistory_eq_chainHistory] at hS hS' ⊢
  exact sum_ite_chainHistory_comp_eq (fun _ => ℳ) T a S S' hS hS' P

section Regrading

variable {N κ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝓝 : κ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : ι → κ)
  (hr : ∀ i x, x ∈ ℳ i → r x ∈ 𝓝 (σ i))
  (U : Fin n → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)

include hr hT in
/-- A source uniform support gives a target uniform support by regrading.
Specialization may kill individual histories or cancel their grouped sum. -/
theorem homogeneousHistory_comp_eq_zero_of_notMem_image
    (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0)
    (q : Fin n → κ) (hq : q ∉ S.image (fun p => σ ∘ p)) :
    (homogeneousHistory 𝓝 U q).comp (r.comp a) = 0 := by
  simp only [homogeneousHistory_eq_chainHistory] at hS ⊢
  exact chainHistory_comp_eq_zero_of_notMem_image (fun _ => ℳ) T a (fun _ => 𝓝)
    (fun _ => r) (fun _ => σ) (fun _ => hr) U hT S hS q hq

open Classical in
include hr hT in
/-- Grouped specialization of selected histories as an identity of linear maps
on the whole input module. Neither the degree map nor the coefficient map must
be injective, and groups whose total coefficient cancels are allowed. -/
theorem map_sum_ite_homogeneousHistory_comp
    (S : Finset (Fin n → ι)) (S' : Finset (Fin n → κ))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0)
    (hS' : ∀ q ∉ S', (homogeneousHistory 𝓝 U q).comp (r.comp a) = 0)
    (P : (Fin n → κ) → Prop) :
    r.comp (∑ p ∈ S, if P (σ ∘ p) then (homogeneousHistory ℳ T p).comp a else 0) =
      ∑ q ∈ S', if P q then (homogeneousHistory 𝓝 U q).comp (r.comp a) else 0 := by
  simp only [homogeneousHistory_eq_chainHistory] at hS hS' ⊢
  exact map_sum_ite_chainHistory_comp (fun _ => ℳ) T a (fun _ => 𝓝) (fun _ => r)
    (fun _ => σ) (fun _ => hr) U hT S S' hS hS' P

open Classical in
include hr hT in
/-- Grouped specialization needs only a source uniform support: its finite
image supplies the target index set, including groups with zero total weight. -/
theorem map_sum_ite_homogeneousHistory_comp_image
    (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0)
    (P : (Fin n → κ) → Prop) :
    r.comp (∑ p ∈ S, if P (σ ∘ p) then (homogeneousHistory ℳ T p).comp a else 0) =
      ∑ q ∈ S.image (fun p => σ ∘ p),
        if P q then (homogeneousHistory 𝓝 U q).comp (r.comp a) else 0 :=
  map_sum_ite_homogeneousHistory_comp ℳ T a 𝓝 r σ hr U hT S _ hS
    (homogeneousHistory_comp_eq_zero_of_notMem_image ℳ T a 𝓝 r σ hr U hT S hS) P

end Regrading

end Mei
