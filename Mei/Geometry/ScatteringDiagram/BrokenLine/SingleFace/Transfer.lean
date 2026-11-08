/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Basic
public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Single-face rays for coefficient correspondences

A homogeneous input in one chamber lifts to the face module and propagates to
a possibly different chamber module. Its nonzero whole output components index
actual one-crossing admissible rays. Their incoming source is the full incoming
half-space, and their crossing must avoid the prescribed singular subset of the
face. Equal spatial velocities do not identify different component degrees.

The weighted sum retains precisely the components with admitted crossings.
For any linear incoming family, this sum is a linear map. With uniform finite
output support it has a fixed finite-sum formula, retaining zero terms.
Generic total-lift identities and matching are developed in
`Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Resolution`.

This uses the existing `AdmissibleRayRealization` carrier and its single-face
classification. Whole-component propagation and total terminal lifts follow
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.GradedCorrespondence

variable {R B U M ι κ V : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid M] [Module R M] [DecidableEq κ]
  {𝒰 : ι → Submodule R U} {ℳ : κ → Submodule R M}
  [DirectSum.Decomposition ℳ] {I : Set ι} {J : Set κ}
  (C : GradedCorrespondence (B := B) 𝒰 ℳ I J) (i : I) (a : 𝒰 i)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (u : V) (v : κ → V) (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)

open Classical in
/-- Actual one-crossing rays carrying nonzero whole transfers of an admissible
homogeneous input. The incoming and outgoing normal velocities must agree. -/
abbrev SingleFaceTransferRay (Q : V) :=
  Σ q : ((DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support.filter
      (fun q => ν (v q) = ν u) : Type _),
    AdmissibleRayRealization (fun _ : Fin 1 => ν) (fun _ => b) ![v q.val, u]
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν u} Q

local notation "Rays" Q:max => C.SingleFaceTransferRay i a u v ν b Z Q
local notation "crosses" Q:max q:max =>
  ((ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z)

variable {C i a u v ν b Z} in
/-- The output degree determines an actual one-crossing ray at a fixed endpoint. -/
@[ext]
theorem SingleFaceTransferRay.ext {Q : V} (r s : (Rays Q))
    (h : r.1.val = s.1.val) : r = s := by
  obtain ⟨q, r⟩ := r
  obtain ⟨q', s⟩ := s
  have hq : q = q' := Subtype.ext h
  subst q'
  exact congrArg (Sigma.mk q) (Subsingleton.elim r s)

/-- The ray fiber is indexed exactly by the nonzero transfers whose normal
velocities match and whose computed crossings are negative and nonsingular. -/
def singleFaceTransferRayEquiv (hZ : Z ⊆ {x | ν x = b}) (Q : V) : (Rays Q) ≃
    {q : κ // C.transfer i q a ≠ 0 ∧ ν (v q) = ν u ∧ (crosses Q q)} := by
  classical
  let F : (Rays Q) → {q : κ // C.transfer i q a ≠ 0 ∧
      ν (v q) = ν u ∧ (crosses Q q)} := fun r => by
    obtain ⟨hq, hv⟩ := Finset.mem_filter.mp r.1.property
    exact ⟨r.1.val, by simpa only [transfer_apply] using DFinsupp.mem_support_iff.mp hq, hv,
      (AdmissibleRayRealization.nonempty_singleFace_one_iff hv hZ).mp ⟨r.2⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro r s hrs
    have he := congrArg Subtype.val hrs
    exact SingleFaceTransferRay.ext _ _ he
  · rintro ⟨q, hq, hv, ht, hx⟩
    have hmem : q ∈ (DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support := by
      simpa only [DFinsupp.mem_support_iff, transfer_apply] using hq
    exact ⟨⟨⟨q, Finset.mem_filter.mpr ⟨hmem, hv⟩⟩,
      AdmissibleRayRealization.singleFaceOne hv hZ ht hx⟩, Subtype.ext rfl⟩

/-- The equivalence retains the outgoing degree recorded by the actual ray. -/
@[simp]
theorem singleFaceTransferRayEquiv_apply_val (hZ : Z ⊆ {x | ν x = b})
    (Q : V) (r : (Rays Q)) :
    (C.singleFaceTransferRayEquiv i a u v ν b Z hZ Q r).val = r.1.val := (rfl)

/-- The weighted evaluation sums the whole final decorations over actual rays,
including unchanged spatial directions and excluding zero output components. -/
def singleFaceTransferEvaluation (Q : V) : M :=
  let := Fintype.ofFinite (Rays Q)
  ∑ r : (Rays Q), (C.transfer i r.1.val a : M)

/-- Evaluate the one-crossing fiber by its actual final decorations. -/
theorem singleFaceTransferEvaluation_def (Q : V) :
    C.singleFaceTransferEvaluation i a u v ν b Z Q =
      let := Fintype.ofFinite (Rays Q)
      ∑ r : (Rays Q), (C.transfer i r.1.val a : M) := (rfl)

/-- Zero incoming coefficient has no surviving weighted contribution. -/
@[simp]
theorem singleFaceTransferEvaluation_zero (Q : V) :
    C.singleFaceTransferEvaluation i 0 u v ν b Z Q = 0 := by
  classical
  simp only [singleFaceTransferEvaluation_def, map_zero, ZeroMemClass.coe_zero,
    Finset.sum_const_zero]

open Classical in
/-- The geometric weighted sum selects precisely the admitted components.
This identity holds at all endpoints, including terminal and singular ones. -/
theorem singleFaceTransferEvaluation_eq_sum (hZ : Z ⊆ {x | ν x = b}) (Q : V) :
    C.singleFaceTransferEvaluation i a u v ν b Z Q =
      ∑ q ∈ (DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support,
        if ν (v q) = ν u ∧ (crosses Q q) then (C.transfer i q a : M) else 0 := by
  classical
  let s := (DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support.filter
    (fun q => ν (v q) = ν u ∧ (crosses Q q))
  let e' : {q : κ // C.transfer i q a ≠ 0 ∧ ν (v q) = ν u ∧ (crosses Q q)} ≃
      (s : Type _) := Equiv.subtypeEquivRight (fun q => by simp [s, transfer_apply])
  let e := (C.singleFaceTransferRayEquiv i a u v ν b Z hZ Q).trans e'
  let := Fintype.ofFinite (Rays Q)
  rw [singleFaceTransferEvaluation_def]
  calc
    _ = ∑ q : (s : Type _), (C.transfer i q.val a : M) := by
      apply Fintype.sum_equiv e
      intro r
      rfl
    _ = _ := (Finset.sum_coe_sort s (fun q => (C.transfer i q a : M))).trans
      (by simp only [s, Finset.sum_filter])

/-- When every surviving component has an admitted crossing and the incoming
normal velocity, weighted evaluation is the full opposite image of the lift. -/
theorem singleFaceTransferEvaluation_eq_right (hZ : Z ⊆ {x | ν x = b}) (Q : V)
    (hcross : ∀ q, C.transfer i q a ≠ 0 → ν (v q) = ν u ∧ (crosses Q q)) :
    C.singleFaceTransferEvaluation i a u v ν b Z Q = C.right (C.liftLeft i a) := by
  classical
  rw [C.singleFaceTransferEvaluation_eq_sum i a u v ν b Z hZ Q]
  rw [Finset.sum_congr rfl (fun q hq =>
    ite_eq_left (hcross q (by simpa only [transfer_apply] using DFinsupp.mem_support_iff.mp hq)))]
  exact C.sum_transfer i a

section Linear

variable {E : Type*} [AddCommMonoid E] [Module R E] (α : E →ₗ[R] 𝒰 i)

open Classical in
/-- Select the component maps of a linear incoming family by the actual
single-face incidence conditions. Each input has finite graded output support;
the family need not have a uniform finite support. -/
def singleFaceTransferEvaluationLinear (Q : V) : E →ₗ[R] M :=
  (DirectSum.homogeneousExtend ℳ (fun q =>
    if ν (v q) = ν u ∧ (crosses Q q) then (ℳ q).subtype else 0)).comp
      (C.right.comp ((C.liftLeft i).comp α))

open Classical in
/-- Linear evaluation applies homogeneous extension of the geometrically admitted
component maps to the opposite image of the incoming lift. -/
theorem singleFaceTransferEvaluationLinear_def (Q : V) :
    C.singleFaceTransferEvaluationLinear i u v ν b Z α Q =
      (DirectSum.homogeneousExtend ℳ (fun q =>
        if ν (v q) = ν u ∧ (crosses Q q) then (ℳ q).subtype else 0)).comp
          (C.right.comp ((C.liftLeft i).comp α)) := (rfl)

open Classical in
/-- The linear evaluation retains zero component terms and selects crossings
by geometry alone, independently of the input parameter. -/
@[simp]
theorem singleFaceTransferEvaluationLinear_apply (Q : V) (x : E) :
    C.singleFaceTransferEvaluationLinear i u v ν b Z α Q x =
      ∑ q ∈ (DirectSum.decompose ℳ (C.right (C.liftLeft i (α x)))).support,
        if ν (v q) = ν u ∧ (crosses Q q) then
          (C.transfer i q (α x) : M) else 0 := by
  rw [singleFaceTransferEvaluationLinear, LinearMap.comp_apply,
    DirectSum.homogeneousExtend_eq_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.zero_apply, transfer_apply]

open Classical in
/-- A uniform support bound gives a fixed finite-sum formula for the linear
evaluation, even when specialization kills some branches. -/
theorem singleFaceTransferEvaluationLinear_eq_sum (s : Finset κ)
    (hs : ∀ q ∉ s, (C.transfer i q).comp α = 0)
    (Q : V) (x : E) :
    C.singleFaceTransferEvaluationLinear i u v ν b Z α Q x =
      ∑ q ∈ s, if ν (v q) = ν u ∧ (crosses Q q) then
        (C.transfer i q (α x) : M) else 0 := by
  classical
  rw [singleFaceTransferEvaluationLinear_apply]
  have hsub : (DirectSum.decompose ℳ (C.right (C.liftLeft i (α x)))).support ⊆ s := by
    intro q hq
    by_contra hqs
    have he := LinearMap.congr_fun (hs q hqs) x
    exact (DFinsupp.mem_support_iff.mp hq) (by simpa only [LinearMap.comp_apply,
      LinearMap.zero_apply, transfer_apply] using he)
  simpa only [DFinsupp.sum, transfer_apply] using
    (DFinsupp.sum_of_support_subset
      (f := DirectSum.decompose ℳ (C.right (C.liftLeft i (α x))))
      (g := fun q y => if ν (v q) = ν u ∧ (crosses Q q) then (y : M) else 0)
      hsub (by simp))

/-- Every linear incoming family computes the actual geometric weighted sum
for every input, without a uniform support bound. -/
theorem singleFaceTransferEvaluationLinear_apply_eq_evaluation
    (hZ : Z ⊆ {x | ν x = b}) (Q : V) (x : E) :
    C.singleFaceTransferEvaluationLinear i u v ν b Z α Q x =
      C.singleFaceTransferEvaluation i (α x) u v ν b Z Q := by
  classical
  rw [singleFaceTransferEvaluationLinear_apply,
    C.singleFaceTransferEvaluation_eq_sum i (α x) u v ν b Z hZ Q]

end Linear

end Mei.GradedCorrespondence
