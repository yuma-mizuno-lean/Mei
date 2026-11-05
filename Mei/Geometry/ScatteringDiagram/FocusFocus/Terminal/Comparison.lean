/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison.Basic
public import Mei.LinearAlgebra.CommonLift

/-!
# Reflecting terminal slab lifts to the truncated coefficient diagram

The face component of the faithful chamber Laurent comparison is the inverse
slab algebra dictionary. Every total nodal terminal lift therefore has an
explicit preimage in the original truncated slab. If its two chamber values
are the images of specified chamber maps, their common lift reflects uniquely.
This includes the actual finite weighted terminal evaluations.

Only the total chamber maps require a common face lift. No preimages of separate
binomial branches are needed. All maps retain the original coefficient scalar action.
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "A" => slabAlgebra (C τ) (1 + T 1) k

attribute [local instance] instScalarTowerSlabNode

/-- Every target face coefficient has its specified preimage under the inverse
slab dictionary. This is the terminal-lift preimage condition for reflection. -/
theorem chamberLaurentComparison_middle_preimage (z : SlabNode τ) :
    (chamberLaurentComparison K k).middle
      (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1)) z) = z := by
  simp only [chamberLaurentComparison_middle, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

variable {H : Type*} [AddCommMonoid H] [Module K H]

private theorem comparison_middle_injective :
    Function.Injective (chamberLaurentComparison K k).middle := by
  intro x y h
  apply (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))).symm.injective
  simpa only [chamberLaurentComparison_middle, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply] using h

private theorem comparison_left_injective :
    Function.Injective (chamberLaurentComparison K k).left := by
  intro x y h
  apply leftChamberExponentMap_injective K k
  simpa only [chamberLaurentComparison_left, AlgHom.toLinearMap_apply] using h

private theorem comparison_right_injective :
    Function.Injective (chamberLaurentComparison K k).right := by
  intro x y h
  apply rightChamberExponentMap_injective K k
  simpa only [chamberLaurentComparison_right, AlgHom.toLinearMap_apply] using h

private theorem comparison_reflect (l : H →ₗ[K] SlabNode τ)
    (βL : H →ₗ[K] TruncatedExponentChamber K k 1)
    (βR : H →ₗ[K] TruncatedExponentChamber K k 0)
    (hL : (((exponentCorrespondence (C τ * (1 + T 1))).restrictScalars K).left).comp l =
      (chamberLaurentComparison K k).left.comp βL)
    (hR : (((exponentCorrespondence (C τ * (1 + T 1))).restrictScalars K).right).comp l =
      (chamberLaurentComparison K k).right.comp βR)
    (hpre : ∀ a, l a ∈ LinearMap.range (chamberLaurentComparison K k).middle) :
    ∃ L : H →ₗ[K] A,
      (chamberCorrespondence K k).left.comp L = βL ∧
      (chamberCorrespondence K k).right.comp L = βR ∧
      (chamberLaurentComparison K k).middle.comp L = l :=
  LinearMap.exists_comp_eq_and_comp_eq_and_comp_eq_of_forall_mem_range
    (chamberLaurentComparison K k).middle (chamberLaurentComparison K k).left
    (chamberLaurentComparison K k).right (chamberLaurentComparison K k).left_comm.symm
    (chamberLaurentComparison K k).right_comm.symm
    (comparison_left_injective K k) (comparison_right_injective K k)
    (comparison_middle_injective K k) l hL hR hpre

private theorem comparison_left_lift (l : H →ₗ[K] SlabNode τ)
    (βL : H →ₗ[K] TruncatedExponentChamber K k 1)
    (hL : ((exponentLeftMap (C τ * (1 + T 1))).toLinearMap.restrictScalars K).comp l =
      (leftChamberExponentMap K k).toLinearMap.comp βL) :
    (((exponentCorrespondence (C τ * (1 + T 1))).restrictScalars K).left).comp l =
      (chamberLaurentComparison K k).left.comp βL := by
  simpa only [GradedCorrespondence.restrictScalars_left, exponentCorrespondence_left,
    chamberLaurentComparison_left] using hL

private theorem comparison_right_lift (l : H →ₗ[K] SlabNode τ)
    (βR : H →ₗ[K] TruncatedExponentChamber K k 0)
    (hR : ((exponentRightMap (C τ * (1 + T 1))).toLinearMap.restrictScalars K).comp l =
      (rightChamberExponentMap K k).toLinearMap.comp βR) :
    (((exponentCorrespondence (C τ * (1 + T 1))).restrictScalars K).right).comp l =
      (chamberLaurentComparison K k).right.comp βR := by
  simpa only [GradedCorrespondence.restrictScalars_right, exponentCorrespondence_right,
    chamberLaurentComparison_right] using hR

private theorem comparison_middle_range (l : H →ₗ[K] SlabNode τ) (a : H) :
    l a ∈ LinearMap.range (chamberLaurentComparison K k).middle :=
  ⟨algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1)) (l a),
    chamberLaurentComparison_middle_preimage K k (l a)⟩

private theorem comparison_unique (L L' : H →ₗ[K] A)
    (h : (chamberLaurentComparison K k).middle.comp L =
      (chamberLaurentComparison K k).middle.comp L') : L = L' :=
  (LinearMap.cancel_left (comparison_middle_injective K k)).mp h

/-- A nodal common lift determines a unique truncated slab map with the two
specified chamber components and with middle component equal to the nodal lift. -/
theorem existsUnique_chamberCommonLift_of_laurent
    (l : H →ₗ[K] SlabNode τ)
    (βL : H →ₗ[K] TruncatedExponentChamber K k 1)
    (βR : H →ₗ[K] TruncatedExponentChamber K k 0)
    (hL : ((exponentLeftMap (C τ * (1 + T 1))).toLinearMap.restrictScalars K).comp l =
      (leftChamberExponentMap K k).toLinearMap.comp βL)
    (hR : ((exponentRightMap (C τ * (1 + T 1))).toLinearMap.restrictScalars K).comp l =
      (rightChamberExponentMap K k).toLinearMap.comp βR) :
    ∃! L : H →ₗ[K] A,
      (chamberCorrespondence K k).left.comp L = βL ∧
      (chamberCorrespondence K k).right.comp L = βR ∧
      (chamberLaurentComparison K k).middle.comp L = l :=
  (comparison_reflect K k l βL βR (comparison_left_lift K k l βL hL)
    (comparison_right_lift K k l βR hR) (comparison_middle_range K k l)).elim fun L h =>
      ⟨L, h, fun L' h' => comparison_unique K k L' L (h'.2.2.trans h.2.2.symm)⟩

section FiniteInput

variable {ι : Type*}
  [Module (AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)) H]
  [IsScalarTower K (AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)) H]
  (s : Finset ι) (n b : ι → ℤ)
  (α : ι → H →ₗ[AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)]
    AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K))

/-- Finite terminal evaluations determine a unique truncated slab map with the
specified chamber components and middle component equal to the total theta lift. -/
theorem existsUnique_slabTerminalFinite_chamberLift
    {v : ℝ} {L U : ℝ × ℝ}
    (hL : L ∈ slabTerminalFiniteDomain s n b v)
    (hU : U ∈ slabTerminalFiniteDomain s n b v) (hLs : L.1 < 0) (hUs : 0 < U.1)
    (βL : H →ₗ[K] TruncatedExponentChamber K k 1)
    (βR : H →ₗ[K] TruncatedExponentChamber K k 0)
    (hβL : ∀ a, leftChamberExponentMap K k (βL a) =
      ∑ i ∈ s, slabThetaEvaluation τ (α i a) (n i) (b i) L)
    (hβR : ∀ a, rightChamberExponentMap K k (βR a) =
      ∑ i ∈ s, slabThetaEvaluation τ (α i a) (n i) (b i) U) :
    ∃! l : H →ₗ[K] A,
      (chamberCorrespondence K k).left.comp l = βL ∧
      (chamberCorrespondence K k).right.comp l = βR ∧
      (chamberLaurentComparison K k).middle.comp l =
        (slabTerminalFiniteLift s n b τ α).restrictScalars K := by
  apply existsUnique_chamberCommonLift_of_laurent K k
  · apply LinearMap.ext
    intro a
    exact (exponentLeftMap_slabTerminalFiniteLift s n b τ α hL hLs a).trans (hβL a).symm
  · apply LinearMap.ext
    intro a
    exact (exponentRightMap_slabTerminalFiniteLift s n b τ α hU hUs a).trans (hβR a).symm

end FiniteInput

end Mei.FocusFocus
