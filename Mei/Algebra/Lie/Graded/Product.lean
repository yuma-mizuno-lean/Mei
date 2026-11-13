/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Completion
public import TauCeti.Algebra.Lie.Graded.Completion
public import Mei.Algebra.PositiveDegrees.Completion

/-!
# Homogeneous Lie components of filtration completions

The quotient-tower equivalence identifies the filtration completion with
TauCeti's convolution Lie algebra on the product of the homogeneous pieces.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

namespace TauCeti.PositiveDegrees

open Mei

open _root_.DirectSum

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)

variable [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "F" =>
  Mei.LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- The filtration completion is the convolution Lie algebra in homogeneous coordinates. -/
noncomputable def filtrationCompletionLieEquivPi :
    letI := d.lieRingPi ℒ
    letI := d.lieAlgebraPi ℒ
    d.filtrationCompletedLie ℒ ≃ₗ⁅R⁆ ∀ n, ℒ n := by
  letI := d.lieRingPi ℒ
  letI := d.lieAlgebraPi ℒ
  let upstream := (Mei.LieIdeal.completionLieEquivLimit (d.degreeIdeal ℒ)
    (d.degreeIdeal_antitone ℒ)).trans (d.completionLieEquivPi ℒ)
  let linear := (F).completionEquivTowerLimit.trans
    (d.completionEquivPi ℒ (fun k => (F).submodule (k + 1)) (F).quotientAntitone
      (fun k => d.degreeIdeal_toSubmodule ℒ k)
      (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn)))
  have hlinear : upstream.toLinearEquiv = linear := by
    -- Expose the two linear factors of the composed Lie equivalence.
    change (Mei.LieIdeal.completionLieEquivLimit (d.degreeIdeal ℒ)
      (d.degreeIdeal_antitone ℒ)).toLinearEquiv.trans (d.completionLieEquivPi ℒ).toLinearEquiv = _
    rw [Mei.LieIdeal.completionLieEquivLimit_toLinearEquiv,
      d.completionLieEquivPi_toLinearEquiv ℒ]
  refine { linear with map_lie' := ?_ }
  intro x y
  -- The structure field is evaluated through the linear equivalence's `toFun`.
  change linear ⁅x, y⁆ = ⁅linear x, linear y⁆
  rw [← hlinear]
  exact upstream.map_lie x y

/-- The underlying linear map is the homogeneous-coordinate comparison. -/
@[simp]
theorem filtrationCompletionLieEquivPi_toLinearEquiv :
    letI := d.lieRingPi ℒ
    letI := d.lieAlgebraPi ℒ
    (d.filtrationCompletionLieEquivPi ℒ).toLinearEquiv =
      d.filtrationCompletionEquivPi ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k)
        (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn)) := by
  unfold filtrationCompletionLieEquivPi
  exact (d.filtrationCompletionEquivPi_def ℒ F _ _).symm

/-- The Lie comparison reads the same coefficients as the module comparison. -/
@[simp]
theorem filtrationCompletionLieEquivPi_apply (x : (F).completion) (n : N) :
    letI := d.lieRingPi ℒ
    letI := d.lieAlgebraPi ℒ
    d.filtrationCompletionLieEquivPi ℒ x n =
      d.filtrationCompletionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n x := by
  let := d.lieRingPi ℒ
  let := d.lieAlgebraPi ℒ
  -- The comparison theorem rewrites the linear equivalence underlying the evaluation.
  change (d.filtrationCompletionLieEquivPi ℒ).toLinearEquiv x n = _
  rw [d.filtrationCompletionLieEquivPi_toLinearEquiv ℒ]
  exact d.filtrationCompletionEquivPi_apply ℒ F _ _ x n

/-- The inverse Lie comparison reconstructs the prescribed coefficients. -/
@[simp]
theorem filtrationCompletionComponent_lieEquivPi_symm (x : ∀ n, ℒ n) (n : N) :
    letI := d.lieRingPi ℒ
    letI := d.lieAlgebraPi ℒ
    d.filtrationCompletionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n
      ((d.filtrationCompletionLieEquivPi ℒ).symm x) = x n := by
  let := d.lieRingPi ℒ
  let := d.lieAlgebraPi ℒ
  rw [← d.filtrationCompletionLieEquivPi_apply ℒ, LieEquiv.apply_symm_apply]

/-- The completed Lie bracket has the finite convolution formula on homogeneous
coefficients, expressed directly on the compatible-family completion. -/
theorem filtrationCompletionComponent_lie (x y : (F).completion) (n : N) :
    (d.filtrationCompletionComponent ℒ F
      (fun k => d.degreeIdeal_toSubmodule ℒ k) n ⁅x, y⁆ : L) =
      ∑ p ∈ (d.finite_decompositions n).toFinset,
        ⁅(d.filtrationCompletionComponent ℒ F
            (fun k => d.degreeIdeal_toSubmodule ℒ k) p.1 x : L),
         (d.filtrationCompletionComponent ℒ F
            (fun k => d.degreeIdeal_toSubmodule ℒ k) p.2 y : L)⁆ := by
  let := d.lieRingPi ℒ
  let := d.lieAlgebraPi ℒ
  have he := (d.filtrationCompletionLieEquivPi ℒ).map_lie x y
  have h := congrArg (fun z : ∀ n, ℒ n => (z n : L)) he
  simpa only [lieRingPi_bracket, piLieBracket_apply, filtrationCompletionLieEquivPi_apply] using h

end TauCeti.PositiveDegrees
