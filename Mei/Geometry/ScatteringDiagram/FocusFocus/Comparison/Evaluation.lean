/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison.Basic
public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Coefficient

/-!
# Laurent comparison of actual focus-focus ray sums

The chamber-to-Laurent morphism of coefficient correspondences intertwines
the actual single-face weighted evaluations, in both crossing directions.
It retains spatial velocities while the smoothing exponent becomes part
of the coefficient in the truncated scalar ring. Degrees that differ only
in their smoothing exponent are grouped.

These are applications of the common geometric coefficient comparison.
They hold at every endpoint, including endpoints at which a singular crossing
removes a branch, with arbitrary incoming homogeneous decorations. No
nonvanishing assumption on the smoothing parameter or on a binomial coefficient
is imposed. The slab geometry follows Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local instance isScalarTower_slabNode_evaluation : IsScalarTower K S (SlabNode τ) :=
  IsScalarTower.to₁₂₄ K S S[ℤ] _

local notation "D" =>
  (GradedCorrespondence.restrictScalars (exponentCorrespondence (C τ * (1 + T 1))) K)

variable (u : ℝ × ℝ) (ν : (ℝ × ℝ) →L[ℝ] ℝ) (b : ℝ)
  (Z : Set (ℝ × ℝ)) (hZ : Z ⊆ {x | ν x = b}) (Q : ℝ × ℝ)

include hZ

/-- The right Laurent realization sends the actual left-to-right ray sum to
the common slab evaluation, grouping the forgotten smoothing exponents. -/
theorem rightChamberExponentMap_singleFaceTransferEvaluation
    (p : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (a : truncatedExponentChamberGrade K k 1 p) :
    rightChamberExponentMap K k
        ((chamberCorrespondence K k).singleFaceTransferEvaluation p a u
          (fun q => ((q.1 : ℝ), (q.2.1 : ℝ))) ν b Z Q) =
      (D).singleFaceTransferEvaluation
        ⟨(-p.val.1, p.val.2.1), (chamberLaurentComparison K k).admissible_left p.property⟩
        ⟨(chamberLaurentComparison K k).left a,
          (chamberLaurentComparison K k).left_mem p a a.property⟩
        u (fun q => ((q.1 : ℝ), (q.2 : ℝ))) ν b Z Q := by
  simpa only [chamberLaurentComparison_right, chamberLaurentComparison_left,
    AlgHom.toLinearMap_apply] using
    (chamberLaurentComparison K k).map_singleFaceTransferEvaluation p u
      (fun q => ((q.1 : ℝ), (q.2.1 : ℝ)))
      (fun q => ((q.1 : ℝ), (q.2 : ℝ))) (fun _ => rfl) ν b Z a hZ Q

/-- In the reverse direction the left Laurent normal coordinate has the
opposite sign. The whole ray sum still obeys the same coefficient comparison. -/
theorem leftChamberExponentMap_singleFaceTransferEvaluation
    (p : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (a : truncatedExponentChamberGrade K k 0 p) :
    leftChamberExponentMap K k
        ((chamberCorrespondence K k).symm.singleFaceTransferEvaluation p a u
          (fun q => ((q.1 : ℝ), (q.2.1 : ℝ))) ν b Z Q) =
      (D).symm.singleFaceTransferEvaluation
        ⟨(p.val.1, p.val.2.1), (chamberLaurentComparison K k).admissible_right p.property⟩
        ⟨(chamberLaurentComparison K k).right a,
          (chamberLaurentComparison K k).right_mem p a a.property⟩
        u (fun q => (-(q.1 : ℝ), (q.2 : ℝ))) ν b Z Q := by
  simpa only [GradedCorrespondence.Hom.symm_right, GradedCorrespondence.Hom.symm_left,
    chamberLaurentComparison_right, chamberLaurentComparison_left,
    AlgHom.toLinearMap_apply] using
    (chamberLaurentComparison K k).symm.map_singleFaceTransferEvaluation p u
      (fun q => ((q.1 : ℝ), (q.2.1 : ℝ)))
      (fun q => (-(q.1 : ℝ), (q.2 : ℝ)))
      (fun q => by simp) ν b Z a hZ Q

end Mei.FocusFocus
