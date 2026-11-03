/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Finite

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

Restricting the expansion to histories with a prescribed terminal degree
isolates the final component of the composite along any linear input
(`sum_homogeneousHistory_terminal_comp_eq`).

The expansion and the existence of uniform supports are transported from the
uniform theorems for path histories in `Mei.LinearAlgebra.GradedModule.History.Path`;
the selection and regrading statements are the linear-map versions of
`sum_homogeneousHistory` and `map_sum_ite_homogeneousHistory` in `History/Finite.lean`.
-/

public noncomputable section

open Quiver

namespace Mei

variable {R M E ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid E] [Module R E] [DecidableEq ι]
  (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  {n : ℕ} (T : Fin n → Module.End R M) (a : E →ₗ[R] M)

/-- A uniform support of history maps contains the pointwise support of every input. -/
theorem homogeneousHistorySupport_subset_of_comp_eq_zero (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0) (x : E) :
    homogeneousHistorySupport ℳ T (a x) ⊆ S := by
  intro p hp
  by_contra h
  exact (mem_homogeneousHistorySupport ℳ T (a x) p).mp hp
    (LinearMap.congr_fun (hS p h) x)

/-- Uniform finite contributing support on the input range suffices for a
linear-map expansion. No global finiteness of homogeneous pieces is required. -/
theorem sum_homogeneousHistory_comp_eq (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0) :
    ∑ p ∈ S, (homogeneousHistory ℳ T p).comp a = ((List.ofFn T).prod).comp a := by
  let e := SingleObj.degreesPathOfFn ι fun j : Fin n => j
  have hS' : ∀ d ∉ S.map e.toEmbedding,
      ((SingleObj.pathOfFn fun j : Fin n => j).homogeneousHistory (M := fun _ => M)
        (fun j => T j) (fun _ => ℳ) d).comp a = 0 := fun d hd => by
    rw [← homogeneousHistory_degreesPathOfFn_symm]
    exact hS _ fun h => hd (Finset.mem_map_equiv.mpr h)
  rw [← composeLinear_pathOfFn T (fun j : Fin n => j), ← Path.sum_homogeneousHistory_comp_eq
    (Q := SingleObj (Fin n)) (M := fun _ => M) (fun j => T j) (fun _ => ℳ)
    (SingleObj.pathOfFn fun j : Fin n => j) a _ hS', Finset.sum_map]
  exact Finset.sum_congr rfl fun p _ => by
    rw [Equiv.coe_toEmbedding, ← homogeneousHistory_degreesPathOfFn_symm,
      Equiv.symm_apply_apply]

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
  let e := SingleObj.degreesPathOfFn ι fun j : Fin n => j
  obtain ⟨S, hS⟩ := Path.exists_uniform_historySupport_of_fg (M := fun _ => M)
    (fun j => T j) (fun _ => ℳ) (SingleObj.pathOfFn fun j : Fin n => j) P hP
  refine ⟨S.map e.symm.toEmbedding, fun p hp x hx => ?_⟩
  rw [← e.symm_apply_apply p, homogeneousHistory_degreesPathOfFn_symm]
  exact hS _ (fun h => hp (Finset.mem_map_equiv.mpr h)) x hx

/-- Finite generation of the input range, not of the ambient graded module,
ensures the uniform support needed for the linear-map expansion. -/
theorem exists_uniform_homogeneousHistory_support (ha : (LinearMap.range a).FG) :
    ∃ S : Finset (Fin n → ι), ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0 := by
  obtain ⟨S, hS⟩ := exists_uniform_homogeneousHistory_support_of_fg ℳ T _ ha
  exact ⟨S, fun p hp => LinearMap.ext fun x => hS p hp (a x) (LinearMap.mem_range_self a x)⟩

open Classical in
/-- Selecting histories in a uniform support gives the same value as selecting
in the pointwise nonzero support. Zero terms are retained in the linear-map sum. -/
theorem sum_ite_homogeneousHistory_comp_apply (S : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0)
    (P : (Fin n → ι) → Prop) (x : E) :
    (∑ p ∈ S, if P p then (homogeneousHistory ℳ T p).comp a else 0) x =
      ∑ p ∈ homogeneousHistorySupport ℳ T (a x),
        if P p then homogeneousHistory ℳ T p (a x) else 0 := by
  trans ∑ p ∈ S, if P p then homogeneousHistory ℳ T p (a x) else 0
  · simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl
  exact (Finset.sum_subset
    (homogeneousHistorySupport_subset_of_comp_eq_zero ℳ T a S hS x)
    (fun p _ hp => by
      have hz : homogeneousHistory ℳ T p (a x) = 0 := by simpa using hp
      simp [hz])).symm

/-- With a uniform finite contributing support on the input range, the final
`η`-component along the composite is the sum of the histories with terminal
degree `η`, written as an identity of linear maps. The ambient grading may be
infinite. -/
theorem sum_homogeneousHistory_terminal_comp_eq
    (T : Fin (n + 1) → Module.End R M) (S : Finset (Fin (n + 1) → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0) (η : ι) :
    ∑ p ∈ S.filter (fun p => p 0 = η), (homogeneousHistory ℳ T p).comp a =
      ((homogeneousComponent ℳ η).comp (List.ofFn T).prod).comp a := by
  classical
  rw [Finset.sum_filter]
  calc ∑ p ∈ S, (if p 0 = η then (homogeneousHistory ℳ T p).comp a else 0)
      = ∑ p ∈ S, (homogeneousComponent ℳ η).comp
          ((homogeneousHistory ℳ T p).comp a) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with hp
        · rw [← LinearMap.comp_assoc, ← hp,
            homogeneousComponent_comp_homogeneousHistory]
        · rw [← LinearMap.comp_assoc,
            homogeneousComponent_comp_homogeneousHistory_of_ne ℳ T p η hp,
            LinearMap.zero_comp]
    _ = ((homogeneousComponent ℳ η).comp (List.ofFn T).prod).comp a := by
        simpa only [LinearMap.comp_assoc] using
          sum_comp_homogeneousHistory_comp_eq ℳ T a (homogeneousComponent ℳ η) S hS

open Classical in
/-- Selected linear-map sums agree over any two uniform supports. -/
theorem sum_ite_homogeneousHistory_comp_eq (S S' : Finset (Fin n → ι))
    (hS : ∀ p ∉ S, (homogeneousHistory ℳ T p).comp a = 0)
    (hS' : ∀ p ∉ S', (homogeneousHistory ℳ T p).comp a = 0)
    (P : (Fin n → ι) → Prop) :
    (∑ p ∈ S, if P p then (homogeneousHistory ℳ T p).comp a else 0) =
      ∑ p ∈ S', if P p then (homogeneousHistory ℳ T p).comp a else 0 := by
  ext x
  rw [sum_ite_homogeneousHistory_comp_apply ℳ T a S hS,
    sum_ite_homogeneousHistory_comp_apply ℳ T a S' hS']

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
  ext x
  by_contra hx
  obtain ⟨p, hp, hne⟩ :=
    exists_homogeneousHistory_ne_zero_of_map_ne_zero ℳ 𝓝 r σ hr T U hT q hx
  refine hq (Finset.mem_image.mpr ⟨p, ?_, funext hp⟩)
  by_contra h
  have hz := LinearMap.congr_fun (hS p h) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  exact hne (by rw [hz, map_zero])

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
  ext x
  rw [LinearMap.comp_apply, sum_ite_homogeneousHistory_comp_apply ℳ T a S hS,
    sum_ite_homogeneousHistory_comp_apply 𝓝 U (r.comp a) S' hS']
  exact map_sum_ite_homogeneousHistory ℳ 𝓝 r σ hr T U hT P (a x)

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
