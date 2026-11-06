/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Transfer
public import Mei.Geometry.Convex.Sweep.Degeneration
public import Mei.LinearAlgebra.GradedCorrespondence.Hom

/-!
# Coefficient comparison of single-face rays

A morphism of graded correspondences preserving spatial velocities intertwines
the geometric weighted evaluations at every endpoint. Several source degrees
may merge, and their whole decorations may cancel. The linear evaluation obeys
the same law without a uniform support or finite-generation assumption.

For an injective output degree map and an injective output coefficient map,
the actual one-crossing fibers are equivalent. This comparison retains the
entire admissible ray, including its incoming tail and recorded encounter,
and maps its whole output decoration. The same comparison identifies the full
branch inventory and its continuous closed path extensions, including branches
with empty endpoint domains. Surjectivity of the degree map and injectivity of
either face leg are unnecessary.

We use the existing single-face admissible realizations and correspondence
transfer comparisons. The coefficient interpretation follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.GradedCorrespondence.Hom

variable {R B U M B' U' M' ι κ ι' κ' V : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid B'] [Module R B'] [AddCommMonoid U'] [Module R U']
  [AddCommMonoid M'] [Module R M'] [DecidableEq κ] [DecidableEq κ']
  {𝒰 : ι → Submodule R U} {ℳ : κ → Submodule R M}
  {𝒰' : ι' → Submodule R U'} {𝓝 : κ' → Submodule R M'}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  {I : Set ι} {J : Set κ} {I' : Set ι'} {J' : Set κ'}
  {C : GradedCorrespondence (B := B) 𝒰 ℳ I J}
  {D : GradedCorrespondence (B := B') 𝒰' 𝓝 I' J'}
  {σ : ι → ι'} {τ : κ → κ'}
  (f : Hom C D σ τ) (i : I)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (u : V) (v : κ → V) (w : κ' → V) (hv : ∀ q, w (τ q) = v q)
  (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)

local notation "i'" => (Subtype.mk (σ i) (f.admissible_left i.property) : I')
local notation "a'(" a ")" =>
  (Subtype.mk (f.left a) (f.left_mem i a (Subtype.property a)) : 𝒰' i')

variable {E : Type*} [AddCommMonoid E] [Module R E] (α : E →ₗ[R] 𝒰 i)

include hv

/-- Geometric component selection commutes with coefficient comparison, including
degree merging and cancellation. The incoming parameter module may be arbitrary. -/
theorem singleFaceTransferEvaluationLinear_comp (Q : V) :
    f.right.comp (C.singleFaceTransferEvaluationLinear i u v ν b Z α Q) =
      D.singleFaceTransferEvaluationLinear i' u w ν b Z
        (((f.left.comp (𝒰 i).subtype).codRestrict (𝒰' i')
          (fun a => f.left_mem i a a.property)).comp α) Q := by
  classical
  let P := fun z : V => ν z = ν u ∧
    (ν Q - b) / ν z < 0 ∧ Q - ((ν Q - b) / ν z) • z ∉ Z
  have hselect :
      f.right.comp (DirectSum.homogeneousExtend ℳ (fun q =>
        if P (v q) then (ℳ q).subtype else 0)) =
      (DirectSum.homogeneousExtend 𝓝 (fun q =>
        if P (w q) then (𝓝 q).subtype else 0)).comp f.right := by
    apply DirectSum.decompose_lhom_ext ℳ
    intro q
    ext a
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      DirectSum.homogeneousExtend_coe,
      DirectSum.homogeneousExtend_of_mem 𝓝 _ (f.right_mem q a a.property), hv]
    split_ifs <;> simp
  ext x
  have he := LinearMap.congr_fun hselect (C.right (C.liftLeft i (α x)))
  have hα (a : 𝒰 i) :
      ((f.left.comp (𝒰 i).subtype).codRestrict (𝒰' i')
        (fun a => f.left_mem i a a.property)) a = a'(a) := by
    exact Subtype.ext (LinearMap.codRestrict_apply _ _ a)
  simpa only [P, singleFaceTransferEvaluationLinear_def, LinearMap.comp_apply,
    hα, right_comm_apply, middle_liftLeft] using he

/-- Weighted sums over actual rays commute with every velocity-preserving
correspondence morphism. No bijection of surviving rays is asserted when
degrees merge or coefficient maps kill decorations. -/
theorem map_singleFaceTransferEvaluation (a : 𝒰 i)
    (hZ : Z ⊆ {x | ν x = b}) (Q : V) :
    f.right (C.singleFaceTransferEvaluation i a u v ν b Z Q) =
      D.singleFaceTransferEvaluation i' a'(a) u w ν b Z Q := by
  have he := LinearMap.congr_fun
    (f.singleFaceTransferEvaluationLinear_comp i u v w hv ν b Z
      (LinearMap.id : 𝒰 i →ₗ[R] 𝒰 i) Q) a
  have ha :
      ((f.left.comp (𝒰 i).subtype).codRestrict (𝒰' i')
        (fun a => f.left_mem i a a.property)) a = a'(a) := by
    exact Subtype.ext (LinearMap.codRestrict_apply _ _ a)
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply,
    singleFaceTransferEvaluationLinear_apply_eq_evaluation _ _ _ _ _ _ _ _ hZ,
    ha] using he

variable (a : 𝒰 i) (hτ : Function.Injective τ) (hinj : Function.Injective f.right)

open Classical in
/-- Coefficient embeddings identify the entire finite inventory of nonzero
single-face transfers, including labels with empty endpoint domains. Neither
surjectivity of the degree map nor injectivity of a face leg is required. -/
def singleFaceTransferLabelEquivOfInjective :
    ((DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support.filter
      (fun q => ν (v q) = ν u) : Type _) ≃
    ((DirectSum.decompose 𝓝 (D.right (D.liftLeft i' a'(a)))).support.filter
      (fun q => ν (w q) = ν u) : Type _) := by
  let F (q : ((DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support.filter
      (fun q => ν (v q) = ν u) : Type _)) :
      ((DirectSum.decompose 𝓝 (D.right (D.liftLeft i' a'(a)))).support.filter
        (fun q => ν (w q) = ν u) : Type _) := by
    obtain ⟨hq, hn⟩ := Finset.mem_filter.mp q.property
    refine ⟨τ q.val, Finset.mem_filter.mpr ⟨?_, by simpa only [hv] using hn⟩⟩
    apply DFinsupp.mem_support_iff.mpr
    intro hz
    have he := f.transfer_map_of_injective hτ i a q.val
    rw [transfer_apply, hz, ZeroMemClass.coe_zero] at he
    apply DFinsupp.mem_support_iff.mp hq
    apply Subtype.val_injective
    exact hinj (by simpa only [map_zero, transfer_apply, ZeroMemClass.coe_zero] using he.symm)
  apply Equiv.ofBijective F
  constructor
  · intro q r he
    exact Subtype.ext (hτ (congrArg Subtype.val he))
  · intro r
    have hne : (D.transfer i' r.val a'(a) : M') ≠ 0 := by
      intro hz
      apply DFinsupp.mem_support_iff.mp (Finset.mem_filter.mp r.property).1
      apply Subtype.val_injective
      simpa only [transfer_apply, ZeroMemClass.coe_zero] using hz
    rw [f.transfer_map_eq_sum] at hne
    obtain ⟨q, hq, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨hsupport, heq⟩ := Finset.mem_filter.mp hq
    refine ⟨⟨q, Finset.mem_filter.mpr ⟨hsupport, ?_⟩⟩, Subtype.ext heq⟩
    rw [← hv q, heq]
    exact (Finset.mem_filter.mp r.property).2

open Classical in
/-- Inventory transport applies the given map to the output degree. -/
@[simp]
theorem singleFaceTransferLabelEquivOfInjective_degree
    (q : ((DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support.filter
      (fun q => ν (v q) = ν u) : Type _)) :
    (f.singleFaceTransferLabelEquivOfInjective i u v w hv ν a hτ hinj q).val =
      τ q.val := (rfl)

open Classical in
/-- The closed single-face paths agree at every endpoint, including outside
the admissible domains and along the full incoming half-line. -/
@[simp↓]
theorem singleFaceTransferLabelEquivOfInjective_path
    (q : ((DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support.filter
      (fun q => ν (v q) = ν u) : Type _)) :
    backwardPath (fun _ : Fin 1 => ν) (fun _ => b)
        ![w (f.singleFaceTransferLabelEquivOfInjective i u v w hv ν a hτ hinj q).val, u] =
      backwardPath (fun _ : Fin 1 => ν) (fun _ => b) ![v q.val, u] := by
  rw [singleFaceTransferLabelEquivOfInjective_degree, hv]

open Classical in
/-- Inventory transport maps each whole decoration by the chamber map. -/
@[simp↓]
theorem singleFaceTransferLabelEquivOfInjective_weight
    (q : ((DirectSum.decompose ℳ (C.right (C.liftLeft i a))).support.filter
      (fun q => ν (v q) = ν u) : Type _)) :
    (D.transfer i'
      (f.singleFaceTransferLabelEquivOfInjective i u v w hv ν a hτ hinj q).val a'(a) : M') =
        f.right (C.transfer i q.val a : M) := by
  rw [singleFaceTransferLabelEquivOfInjective_degree, f.transfer_map_of_injective hτ]

private def transferRayMap (Q : V) (r : C.SingleFaceTransferRay i a u v ν b Z Q) :
    D.SingleFaceTransferRay i' a'(a) u w ν b Z Q :=
  ⟨f.singleFaceTransferLabelEquivOfInjective i u v w hv ν a hτ hinj r.1,
    r.2.congrVelocity (by simp only [singleFaceTransferLabelEquivOfInjective_degree, hv])⟩

/-- Injective output coefficients and degrees give a bijection of the full
single-face ray fibers. Every target degree with nonzero decoration comes from
a source degree, even when the output degree map is not surjective. -/
def singleFaceTransferRayEquivOfInjective (Q : V) :
    C.SingleFaceTransferRay i a u v ν b Z Q ≃
      D.SingleFaceTransferRay i' a'(a) u w ν b Z Q := by
  let e := f.singleFaceTransferLabelEquivOfInjective i u v w hv ν a hτ hinj
  apply Equiv.ofBijective (f.transferRayMap i u v w hv ν b Z a hτ hinj Q)
  constructor
  · intro r s hrs
    exact SingleFaceTransferRay.ext _ _ (hτ (congrArg (fun z => z.1.val) hrs))
  · intro r
    let q := e.symm r.1
    have hq : τ q.val = r.1.val := by
      rw [← f.singleFaceTransferLabelEquivOfInjective_degree i u v w hv ν a hτ hinj q]
      exact congrArg Subtype.val (e.apply_symm_apply r.1)
    refine ⟨⟨q, r.2.congrVelocity (by simp only [← hq, hv])⟩, ?_⟩
    exact SingleFaceTransferRay.ext _ _ hq

/-- The comparison regrades the recorded outgoing degree. -/
@[simp]
theorem singleFaceTransferRayEquivOfInjective_degree (Q : V)
    (r : C.SingleFaceTransferRay i a u v ν b Z Q) :
    (f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q r).1.val =
      τ r.1.val := (rfl)

/-- The comparison retains the entire affine ray and its incoming tail. -/
@[simp]
theorem singleFaceTransferRayEquivOfInjective_ray (Q : V)
    (r : C.SingleFaceTransferRay i a u v ν b Z Q) :
    (f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q r).2.ray =
      r.2.ray := by
  exact AdmissibleRayRealization.ray_congrVelocity _ _

/-- Every recorded encounter parameter is preserved, including an encounter
whose incoming and outgoing spatial directions agree. -/
@[simp]
theorem singleFaceTransferRayEquivOfInjective_parameter (Q : V)
    (r : C.SingleFaceTransferRay i a u v ν b Z Q) :
    (f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q r).2.parameter =
      r.2.parameter := by
  exact AdmissibleRayRealization.parameter_congrVelocity _ _

/-- Whole decorations transform by the output coefficient map. -/
@[simp↓]
theorem singleFaceTransferRayEquivOfInjective_decoration (Q : V)
    (r : C.SingleFaceTransferRay i a u v ν b Z Q) :
    (D.transfer i'
      (f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q r).1.val
      a'(a) : M') = f.right (C.transfer i r.1.val a : M) := by
  rw [singleFaceTransferRayEquivOfInjective_degree, f.transfer_map_of_injective hτ]

/-- Lifting a target ray recovers its degree after regrading. -/
theorem singleFaceTransferRayEquivOfInjective_symm_degree (Q : V)
    (r : D.SingleFaceTransferRay i' a'(a) u w ν b Z Q) :
    τ ((f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q).symm r).1.val =
      r.1.val := by
  let e := f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q
  exact (f.singleFaceTransferRayEquivOfInjective_degree i u v w hv ν b Z a hτ hinj Q
    (e.symm r)).symm.trans (congrArg (fun z => z.1.val) (e.apply_symm_apply r))

/-- The inverse comparison retains the full incoming and outgoing path. -/
@[simp]
theorem singleFaceTransferRayEquivOfInjective_symm_ray (Q : V)
    (r : D.SingleFaceTransferRay i' a'(a) u w ν b Z Q) :
    ((f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q).symm r).2.ray =
      r.2.ray := by
  let e := f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q
  exact (f.singleFaceTransferRayEquivOfInjective_ray i u v w hv ν b Z a hτ hinj Q
    (e.symm r)).symm.trans (congrArg (fun z => z.2.ray) (e.apply_symm_apply r))

/-- The inverse comparison also retains the recorded encounter parameters. -/
@[simp]
theorem singleFaceTransferRayEquivOfInjective_symm_parameter (Q : V)
    (r : D.SingleFaceTransferRay i' a'(a) u w ν b Z Q) :
    ((f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q).symm r).2.parameter =
      r.2.parameter := by
  let e := f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q
  exact (f.singleFaceTransferRayEquivOfInjective_parameter i u v w hv ν b Z a hτ hinj Q
    (e.symm r)).symm.trans (congrArg (fun z => z.2.parameter) (e.apply_symm_apply r))

/-- The coefficient image of a lifted whole decoration is the original target
decoration. This characterizes inverse weights without unfolding the bijection. -/
@[simp↓]
theorem singleFaceTransferRayEquivOfInjective_symm_decoration (Q : V)
    (r : D.SingleFaceTransferRay i' a'(a) u w ν b Z Q) :
    f.right (C.transfer i
      ((f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q).symm r).1.val
      a : M) = (D.transfer i' r.1.val a'(a) : M') := by
  let e := f.singleFaceTransferRayEquivOfInjective i u v w hv ν b Z a hτ hinj Q
  exact (f.singleFaceTransferRayEquivOfInjective_decoration i u v w hv ν b Z a hτ hinj Q
    (e.symm r)).symm.trans
      (congrArg (fun z => (D.transfer i' z.1.val a'(a) : M')) (e.apply_symm_apply r))

end Mei.GradedCorrespondence.Hom
