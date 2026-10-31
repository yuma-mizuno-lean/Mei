/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Basic

/-!
# Terminal resolutions for graph correspondences

An incoming coefficient of negative normal degree approaches a face from the
negative side; positive normal degree approaches from the positive side. At the
face, negative inputs have chamber values `(a, e a)`, positive inputs have values
`(e⁻¹ a, a)`, and tangent inputs have `(a, a)`. If the linear equivalence `e` fixes
tangent coefficients, these finite homogeneous sums have a unique common lift
through the graph correspondence, linear in the incoming coefficient.

The two chamber sums are constructed independently from the homogeneous inputs.
No finiteness of the grading set or basis of its pieces is needed. The input may
include all three normal signs simultaneously. This is the coefficient identity
at a terminal ordinary-wall crossing.

We use `GradedCorrespondence.graph` and Mathlib's internal direct-sum universal
property. The terminal-face convention is that of Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3.2
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.GradedCorrespondence

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  (e : M ≃ₗ[R] M) (w : ι → ℤ)

open Classical in
/-- Negative-side values of all incoming homogeneous coefficients. Inputs from
the positive side cross by the inverse equivalence; the other inputs stay put. -/
def terminalGraphLift : Module.End R M :=
  (DirectSum.toModule R ι M (fun i => if 0 < w i then
    e.symm.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype)).comp
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

open Classical in
/-- Positive-side values of all incoming homogeneous coefficients. Inputs from
the negative side cross by the equivalence; the other inputs stay put. -/
def terminalGraphRight : Module.End R M :=
  (DirectSum.toModule R ι M (fun i => if w i < 0 then
    e.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype)).comp
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

open Classical in
/-- On one homogeneous input the common-lift candidate is the incoming value
or its inverse transport, according to its normal degree. -/
theorem terminalGraphLift_of_mem {i : ι} {a : M} (ha : a ∈ ℳ i) :
    terminalGraphLift ℳ e w a = if 0 < w i then e.symm a else a := by
  simp only [terminalGraphLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem ℳ ha,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  split_ifs <;> rfl

open Classical in
/-- The terminal lift on a homogeneous subtype input is its inverse transport
in positive normal degree and the input itself otherwise. -/
@[simp] theorem terminalGraphLift_coe {i : ι} (a : ℳ i) :
    terminalGraphLift ℳ e w a = if 0 < w i then e.symm a else a :=
  terminalGraphLift_of_mem ℳ e w a.property

open Classical in
/-- On one homogeneous input the positive-side value is the incoming value
or its forward transport, according to its normal degree. -/
theorem terminalGraphRight_of_mem {i : ι} {a : M} (ha : a ∈ ℳ i) :
    terminalGraphRight ℳ e w a = if w i < 0 then e a else a := by
  simp only [terminalGraphRight, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem ℳ ha,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  split_ifs <;> rfl

open Classical in
/-- The positive-side terminal value on a homogeneous subtype input is its
forward transport in negative normal degree and the input itself otherwise. -/
@[simp] theorem terminalGraphRight_coe {i : ι} (a : ℳ i) :
    terminalGraphRight ℳ e w a = if w i < 0 then e a else a :=
  terminalGraphRight_of_mem ℳ e w a.property

open Classical in
/-- The lift candidate is the finite sum of inverse-transferred positive inputs
and unchanged nonpositive inputs, retaining their whole decorations. -/
theorem terminalGraphLift_eq_sum (a : M) :
    terminalGraphLift ℳ e w a =
      ∑ i ∈ (DirectSum.decompose ℳ a).support,
        if 0 < w i then e.symm (DirectSum.decompose ℳ a i) else
          (DirectSum.decompose ℳ a i : M) := by
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact terminalGraphLift_of_mem ℳ e w (DirectSum.decompose ℳ a i).property

open Classical in
/-- The positive-side total is the finite sum of forward-transferred negative
inputs and unchanged nonnegative inputs. -/
theorem terminalGraphRight_eq_sum (a : M) :
    terminalGraphRight ℳ e w a =
      ∑ i ∈ (DirectSum.decompose ℳ a).support,
        if w i < 0 then e (DirectSum.decompose ℳ a i) else
          (DirectSum.decompose ℳ a i : M) := by
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact terminalGraphRight_of_mem ℳ e w (DirectSum.decompose ℳ a i).property

/-- Forward transport identifies the two terminal sums when tangent
coefficients agree. This includes incoming coefficients from either side. -/
theorem comp_terminalGraphLift
    (hzero : ∀ i (a : ℳ i), w i = 0 → e a = a) :
    e.toLinearMap.comp (terminalGraphLift ℳ e w) = terminalGraphRight ℳ e w := by
  ext a
  induction a using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i a =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      terminalGraphLift_of_mem ℳ e w a.property, terminalGraphRight_of_mem ℳ e w a.property]
    split_ifs with hp hn hn
    · omega
    · exact e.apply_symm_apply a
    · rfl
    · exact hzero i a (by omega)
  | add a b ha hb => simp_all

/-- The two independently constructed terminal totals have exactly one common
linear lift through the graph, also after precomposition by any incoming map. -/
theorem existsUnique_terminalGraphLift {E : Type*} [AddCommMonoid E] [Module R E]
    (hzero : ∀ i (a : ℳ i), w i = 0 → e a = a) (α : E →ₗ[R] M) :
    ∃! l : E →ₗ[R] M,
      (graph ℳ ℳ e).left.comp l = (terminalGraphLift ℳ e w).comp α ∧
      (graph ℳ ℳ e).right.comp l = (terminalGraphRight ℳ e w).comp α := by
  refine ⟨(terminalGraphLift ℳ e w).comp α, ⟨by simp, ?_⟩, ?_⟩
  · rw [graph_right, ← LinearMap.comp_assoc, comp_terminalGraphLift ℳ e w hzero]
  · intro l hl
    simpa only [graph_left, LinearMap.id_comp] using hl.1

end Mei.GradedCorrespondence
