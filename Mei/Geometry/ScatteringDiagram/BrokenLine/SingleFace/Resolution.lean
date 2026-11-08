/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Transfer
public import Mei.LinearAlgebra.GradedModule.History.Uniform
import Mei.LinearAlgebra.CommonLift
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Total lifts of single-face ray evaluations

For a graded correspondence between independently graded chamber semimodules,
one exceptional arrangement makes the opposite-side ray sum of a linear incoming
family equal to the opposite image of its chosen face lift, for every input
simultaneously. Uniform finite output support suffices; finite generation of the
incoming range supplies it by the shared homogeneous-history expansion.

Joint injectivity makes the total lift unique. No individual outgoing branch
needs a lift through the face. Graph and slab correspondences use this same
construction, also when coefficients cancel or propagation is not invertible.
These are terminal matching identities; singular-degeneration certificates and
descent on the base require additional geometry.

The terminal-face interpretation follows Gross–Hacking–Siebert, *Theta functions
on varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.GradedCorrespondence

variable {R B U M ι κ V E : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B] [AddCommMonoid U] [Module R U]
  [AddCommMonoid M] [Module R M] [DecidableEq κ]
  {𝒰 : ι → Submodule R U} {ℳ : κ → Submodule R M}
  [DirectSum.Decomposition ℳ] {I : Set ι} {J : Set κ}
  (C : GradedCorrespondence (B := B) 𝒰 ℳ I J) (i : I)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (u : V) (v : κ → V) (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)
  [AddCommMonoid E] [Module R E] (α : E →ₗ[R] 𝒰 i)

/-- A single exceptional arrangement computes every opposite-side ray sum as
an identity of linear maps. Only the output components of the incoming family
must preserve normal velocity, and no injectivity assumption is needed. -/
theorem exists_singleFaceTransferEvaluationLinear_eq_right
    (s : Finset κ) (hs : ∀ q ∉ s, (C.transfer i q).comp α = 0)
    (hnormal : ∀ q x, C.transfer i q (α x) ≠ 0 → ν (v q) = ν u)
    (hZ : Z ⊆ {x | ν x = b})
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      (ν Q - b) / ν u < 0 →
        C.singleFaceTransferEvaluationLinear i u v ν b Z α Q =
          C.right.comp ((C.liftLeft i).comp α) := by
  classical
  -- Exclude all singular shadows for the uniform output support at once.
  obtain ⟨F, hF⟩ := exists_forall_notMem_sweepProjection
    (fun _ : (s : Type _) => ν) (fun _ => b)
    (fun q => (ν (v q.val))⁻¹ • v q.val) A (fun _ j => hA j)
  refine ⟨F, fun Q hQ ht => ?_⟩
  ext x
  rw [C.singleFaceTransferEvaluationLinear_apply_eq_evaluation i u v ν b Z α hZ Q x]
  apply C.singleFaceTransferEvaluation_eq_right i (α x) u v ν b Z hZ Q
  intro q hq
  refine ⟨hnormal q x hq, by rwa [hnormal q x hq], ?_⟩
  have hqs : q ∈ s := by
    by_contra hnot
    exact hq (by simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun (hs q hnot) x)
  intro hmem
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hmem)
  have hp : sweepProjection ν b ((ν (v q))⁻¹ • v q) Q =
      Q - ((ν Q - b) / ν (v q)) • v q := by
    simp only [sweepProjection_apply, smul_smul, div_eq_mul_inv]
    module
  exact hF Q hQ ⟨q, hqs⟩ j (hp ▸ hj)

/-- A finitely generated incoming range has a uniform finite support for its
outgoing transfer components, without finiteness assumptions on the chambers. -/
theorem exists_singleFaceTransfer_support_of_fg
    (hα : (LinearMap.range α).FG) :
    ∃ s : Finset κ, ∀ q ∉ s, (C.transfer i q).comp α = 0 := by
  classical
  let β := C.right.comp ((C.liftLeft i).comp α)
  have hβ : (LinearMap.range β).FG := by
    have he : β = (C.right.comp (C.liftLeft i)).comp α := LinearMap.comp_assoc ..
    rw [he, LinearMap.range_comp]
    exact hα.map (C.right.comp (C.liftLeft i))
  obtain ⟨S, hS⟩ := exists_uniform_homogeneousHistory_support ℳ
    (fun _ : Fin 1 => LinearMap.id) β hβ
  refine ⟨S.image fun d => d 0, fun q hq => ?_⟩
  have hnot : (fun _ : Fin 1 => q) ∉ S := fun h =>
    hq (Finset.mem_image.mpr ⟨_, h, rfl⟩)
  apply LinearMap.ext
  intro x
  apply Subtype.val_injective
  simpa only [homogeneousHistory_succ_apply, homogeneousHistory_zero,
    LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply,
    transfer_apply, ZeroMemClass.coe_zero, β] using LinearMap.congr_fun (hS _ hnot) x

/-- A finitely generated incoming range gives the uniform finite-input test
without finite generation of either chamber or any homogeneous piece. -/
theorem exists_singleFaceTransferEvaluationLinear_eq_right_of_fg
    (hα : (LinearMap.range α).FG)
    (hnormal : ∀ q x, C.transfer i q (α x) ≠ 0 → ν (v q) = ν u)
    (hZ : Z ⊆ {x | ν x = b})
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      (ν Q - b) / ν u < 0 →
        C.singleFaceTransferEvaluationLinear i u v ν b Z α Q =
          C.right.comp ((C.liftLeft i).comp α) := by
  obtain ⟨s, hs⟩ := C.exists_singleFaceTransfer_support_of_fg i α hα
  exact C.exists_singleFaceTransferEvaluationLinear_eq_right
    i u v ν b Z α s hs hnormal hZ A hcover hA

/-- Uniformly supported one-face ray sums have their total common face lift
at generic opposite-side endpoints. The arrangement is chosen for the whole
linear family, before its input. Only joint injectivity is needed for uniqueness;
neither chamber leg nor any individual component is required to be injective. -/
theorem exists_singleFaceTransferEvaluationLinear_commonLift
    (s : Finset κ) (hs : ∀ q ∉ s, (C.transfer i q).comp α = 0)
    (hnormal : ∀ q x, C.transfer i q (α x) ≠ 0 → ν (v q) = ν u)
    (hZ : Z ⊆ {x | ν x = b})
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j)
    (hinj : Function.Injective (C.left.prod C.right)) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      (ν Q - b) / ν u < 0 →
        ∃! l : E →ₗ[R] B,
          C.left.comp l = (𝒰 i).subtype.comp α ∧
          C.right.comp l = C.singleFaceTransferEvaluationLinear i u v ν b Z α Q := by
  obtain ⟨F, hF⟩ := C.exists_singleFaceTransferEvaluationLinear_eq_right
    i u v ν b Z α s hs hnormal hZ A hcover hA
  refine ⟨F, fun Q hQ ht => ?_⟩
  apply (LinearMap.existsUnique_comp_eq_and_comp_eq_iff hinj).mpr
  intro x
  refine ⟨C.liftLeft i (α x), ?_⟩
  simp only [hF Q hQ ht, LinearMap.prod_apply, Function.prod_apply,
    LinearMap.comp_apply, C.left_liftLeft_apply, Submodule.subtype_apply]

/-- A finitely generated incoming range gives the unique total common face
lift at generic opposite-side endpoints, with one arrangement for every input. -/
theorem exists_singleFaceTransferEvaluationLinear_commonLift_of_fg
    (hα : (LinearMap.range α).FG)
    (hnormal : ∀ q x, C.transfer i q (α x) ≠ 0 → ν (v q) = ν u)
    (hZ : Z ⊆ {x | ν x = b})
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j)
    (hinj : Function.Injective (C.left.prod C.right)) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      (ν Q - b) / ν u < 0 →
        ∃! l : E →ₗ[R] B,
          C.left.comp l = (𝒰 i).subtype.comp α ∧
          C.right.comp l = C.singleFaceTransferEvaluationLinear i u v ν b Z α Q := by
  obtain ⟨s, hs⟩ := C.exists_singleFaceTransfer_support_of_fg i α hα
  exact C.exists_singleFaceTransferEvaluationLinear_commonLift
    i u v ν b Z α s hs hnormal hZ A hcover hA hinj

end Mei.GradedCorrespondence
