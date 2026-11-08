/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Resolution
public import Mei.Algebra.Category.SemimoduleCat.Multispan.Span
import Mei.LinearAlgebra.CommonLift

/-!
# Matching families of single-face ray evaluations

The two chamber modules of a graded correspondence may have different degree
sets and different underlying semimodules. A linear family of admissible inputs
and its actual opposite-side ray sums determine a unique linear family of
matching sections of the face incidence diagram when the span is jointly
injective. Only the total sum needs a face lift; individual branches need none.

The arrangement is independent of the incoming coefficient. Finite generation
of the incoming range supplies the finite-input test, without finite generation
of either chamber or its homogeneous pieces. This uses the total transfer
construction shared by graph and slab correspondences. It does not supply
certificates across singular degenerations or descent along the base.

The face matching follows Gross–Hacking–Siebert, *Theta functions on varieties
with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open CategoryTheory Limits Set

universe u

namespace Mei.GradedCorrespondence

variable {R V H ι κ : Type*} {U M B : Type u} [Semiring R]
  [AddCommMonoid U] [Module R U] [AddCommMonoid M] [Module R M]
  [DecidableEq κ] {𝒰 : ι → Submodule R U} {ℳ : κ → Submodule R M}
  [DirectSum.Decomposition ℳ] [AddCommMonoid B] [Module R B]
  {I : Set ι} {J : Set κ} (C : GradedCorrespondence (B := B) 𝒰 ℳ I J)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommMonoid H] [Module R H]
  (p : I) (α : H →ₗ[R] 𝒰 p) (u : V) (v : κ → V)
  (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)

local notation "Sections" => SemimoduleCat.sectionsSubmodule
  (MultispanIndex.multispan (MultispanIndex.ofLinearMaps C.left C.right))

/-- The incoming coefficients and the actual opposite-side ray sums are the
chamber values of a unique linear family of matching sections. One arrangement
works for all incoming parameters, including zero and cancelling inputs. -/
theorem existsUnique_singleFace_matchingFamily
    (hinj : Function.Injective (C.left.prod C.right))
    (s : Finset κ) (hs : ∀ q ∉ s, (C.transfer p q).comp α = 0)
    (hnormal : ∀ q x, C.transfer p q (α x) ≠ 0 → ν (v q) = ν u)
    (hZ : Z ⊆ {x | ν x = b})
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q → (ν Q - b) / ν u < 0 →
      ∃! ℓ : H →ₗ[R] Sections, ∀ x,
        (ℓ x).val (.right false) = (α x : U) ∧
        (ℓ x).val (.right true) = C.singleFaceTransferEvaluation p (α x) u v ν b Z Q := by
  obtain ⟨F, hF⟩ := C.exists_singleFaceTransferEvaluationLinear_commonLift
    p u v ν b Z α s hs hnormal hZ A hcover hA hinj
  refine ⟨F, fun Q hQ ht => ?_⟩
  apply (MultispanIndex.existsUnique_sections_ofLinearMaps_iff C.left C.right _ _).mpr
  simpa only [LinearMap.ext_iff, LinearMap.comp_apply, Submodule.subtype_apply,
    ← forall_and,
    C.singleFaceTransferEvaluationLinear_apply_eq_evaluation p u v ν b Z α hZ Q] using
    hF Q hQ ht

/-- Every linear family with finitely generated incoming range gives matching
sections with these actual ray sums as chamber values. No finiteness of the
ambient grading or chamber modules is required. -/
theorem existsUnique_singleFace_matchingFamily_of_fg
    (hinj : Function.Injective (C.left.prod C.right))
    (hα : (LinearMap.range α).FG)
    (hnormal : ∀ q x, C.transfer p q (α x) ≠ 0 → ν (v q) = ν u)
    (hZ : Z ⊆ {x | ν x = b})
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q → (ν Q - b) / ν u < 0 →
      ∃! ℓ : H →ₗ[R] Sections, ∀ x,
        (ℓ x).val (.right false) = (α x : U) ∧
        (ℓ x).val (.right true) = C.singleFaceTransferEvaluation p (α x) u v ν b Z Q := by
  obtain ⟨F, hF⟩ := C.exists_singleFaceTransferEvaluationLinear_eq_right_of_fg
    p u v ν b Z α hα hnormal hZ A hcover hA
  refine ⟨F, fun Q hQ ht => ?_⟩
  apply (MultispanIndex.existsUnique_sections_ofLinearMaps_iff C.left C.right _ _).mpr
  have hlift : ∃! l : H →ₗ[R] B,
      C.left.comp l = (𝒰 p).subtype.comp α ∧
      C.right.comp l = C.singleFaceTransferEvaluationLinear p u v ν b Z α Q := by
    apply (LinearMap.existsUnique_comp_eq_and_comp_eq_iff hinj).mpr
    intro x
    refine ⟨C.liftLeft p (α x), ?_⟩
    simp only [hF Q hQ ht, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.comp_apply, C.left_liftLeft_apply, Submodule.subtype_apply]
  simpa only [LinearMap.ext_iff, LinearMap.comp_apply, Submodule.subtype_apply,
    ← forall_and,
    C.singleFaceTransferEvaluationLinear_apply_eq_evaluation p u v ν b Z α hZ Q] using hlift

end Mei.GradedCorrespondence
