/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Lifts
public import Mei.Geometry.ScatteringDiagram.FocusFocus.GradedMap

/-!
# Reductions of the focus-focus slab correspondence

Coefficient changes and lower cutoffs commute with the incoming lifts from both
truncated chambers into the fiber-product slab. Consequently they commute with
each homogeneous transfer across the slab, including when the target cutoff or
coefficient map kills the input. These equations compare the actual chamber
correspondences used for propagation of decorated lines.

We use `NodeAlgebra.slabAlgebraMap`, `FocusFocus.leftChamberLift` and
`FocusFocus.rightChamberLift`, `NodeAlgebra.mapOfEq_incomingLift`, the graded
chamber reductions, and Mathlib's `GradedRingHom.map_directSumDecompose`.
The slab coordinates follow
Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open Mei.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable {K K' : Type*} [CommRing K] [CommRing K']
  {k l : ℕ} (φ : K →+* K') (hl : l ≤ k)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "S'" => AdjoinRoot (Polynomial.X ^ (l + 1) : Polynomial K')
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ'" => AdjoinRoot.root (Polynomial.X ^ (l + 1) : Polynomial K')

/-- Every whole admissible left piece has the same lift before or after
coefficient change and cutoff reduction. No survival assumption is needed. -/
@[simp]
theorem truncatedSlabMap_leftChamberLift (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    truncatedSlabMap φ hl (leftChamberLift K k q u) =
      leftChamberLift K' l q
        ((truncatedExponentChamberGradedMap φ hl 1).gradedAddHom q.val u) := by
  let : Algebra S[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
  have htf : algebraMap S[ℤ] S'[ℤ] (C τ * (1 + T 1)) = C τ' * (1 + T 1) := by
    simp only [map_mul, map_add, map_one, RingHom.algebraMap_toAlgebra,
      truncatedScalarMap_C_root, truncatedScalarMap_T]
  have he := leftChamberLaurentMap_leftChamberMap (t := C τ)
    (truncatedScalarMap_C_root φ hl) hl (C_root_X_pow_pow K (k + 1))
    (C_root_X_pow_pow K' (l + 1)) u.val
  simp only [leftChamberLift_apply K k (C_root_X_pow_pow K (k + 1)) q u,
    leftChamberLift_apply K' l (C_root_X_pow_pow K' (l + 1)) q
      ((truncatedExponentChamberGradedMap φ hl 1).gradedAddHom q.val u)]
  rw [truncatedSlabMap_toSlabAlgebra]
  simp only [GradedRingHom.gradedAddHom_apply_coe,
    ← GradedRingHom.coe_toRingHom, truncatedExponentChamberGradedMap_toRingHom,
    truncatedExponentChamberMap_one,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  simp only [he]
  apply congrArg (toSlabAlgebra (C τ') (1 + T 1) l)
  simpa only [incomingLift_apply] using
    mapOfEq_incomingLift (C τ * (1 + T 1)) htf 0
      ⟨-q.val.1, by simpa only [Set.mem_ofPred_eq] using
        (neg_nonneg.mpr (q.property : q.val.1 ≤ 0))⟩
      ⟨leftChamberLaurentMap (C_root_X_pow_pow K (k + 1)) u.val,
        leftLaurent_mem_grade K k q.val u⟩

/-- Every whole admissible right piece has the same lift before or after
coefficient change and cutoff reduction, including discarded pieces. -/
@[simp]
theorem truncatedSlabMap_rightChamberLift (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val) :
    truncatedSlabMap φ hl (rightChamberLift K k q u) =
      rightChamberLift K' l q
        ((truncatedExponentChamberGradedMap φ hl 0).gradedAddHom q.val u) := by
  let : Algebra S[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
  have htf : algebraMap S[ℤ] S'[ℤ] (C τ * (1 + T 1)) = C τ' * (1 + T 1) := by
    simp only [map_mul, map_add, map_one, RingHom.algebraMap_toAlgebra,
      truncatedScalarMap_C_root, truncatedScalarMap_T]
  have he := rightChamberLaurentMap_rightChamberMap (t := C τ)
    (truncatedScalarMap_C_root φ hl) hl (C_root_X_pow_pow K (k + 1))
    (C_root_X_pow_pow K' (l + 1)) u.val
  simp only [rightChamberLift_apply K k (C_root_X_pow_pow K (k + 1)) q u,
    rightChamberLift_apply K' l (C_root_X_pow_pow K' (l + 1)) q
      ((truncatedExponentChamberGradedMap φ hl 0).gradedAddHom q.val u)]
  rw [truncatedSlabMap_toSlabAlgebra]
  simp only [GradedRingHom.gradedAddHom_apply_coe,
    ← GradedRingHom.coe_toRingHom, truncatedExponentChamberGradedMap_toRingHom,
    truncatedExponentChamberMap_zero,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  simp only [he]
  apply congrArg (toSlabAlgebra (C τ') (1 + T 1) l)
  simpa only [incomingLift_apply] using
    mapOfEq_incomingLift (C τ * (1 + T 1)) htf 1
      ⟨q.val.1, q.property⟩
      ⟨rightChamberLaurentMap (C_root_X_pow_pow K (k + 1)) u.val,
        rightLaurent_mem_grade K k q.val u⟩

/-- Left-to-right propagation commutes with coefficient change and cutoff
reduction on each whole homogeneous output, without an injectivity assumption. -/
theorem truncatedExponentChamberMap_transfer
    (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0}) (r : ℤ × ℤ × ℤ)
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    truncatedExponentChamberMap φ hl 0
        ((chamberCorrespondence K k).transfer q r u : TruncatedExponentChamber K k 0) =
      ((chamberCorrespondence K' l).transfer q r
        ((truncatedExponentChamberGradedMap φ hl 1).gradedAddHom q.val u) :
          TruncatedExponentChamber K' l 0) := by
  simp only [GradedCorrespondence.transfer_apply, chamberCorrespondence_right_apply,
    chamberCorrespondence_liftLeft]
  have he := congrArg (fun z : slabAlgebra (C τ') (1 + T 1) l => z.val.2)
    (truncatedSlabMap_leftChamberLift φ hl q u)
  rw [truncatedSlabMap_snd] at he
  have hp := (truncatedExponentChamberGradedMap φ hl 0).map_directSumDecompose
    (x := (leftChamberLift K k q u).val.2) (i := r)
  simp only [← GradedRingHom.coe_toRingHom, truncatedExponentChamberGradedMap_toRingHom] at hp
  exact hp.trans (congrArg
    (fun z => (DirectSum.decompose (truncatedExponentChamberGrade K' l 0) z r :
      TruncatedExponentChamber K' l 0)) he)

/-- Right-to-left propagation obeys the same reduction equation, including
inputs or outputs annihilated by the specialization or the target cutoff. -/
theorem truncatedExponentChamberMap_symm_transfer
    (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1}) (r : ℤ × ℤ × ℤ)
    (u : truncatedExponentChamberGrade K k 0 q.val) :
    truncatedExponentChamberMap φ hl 1
        ((chamberCorrespondence K k).symm.transfer q r u : TruncatedExponentChamber K k 1) =
      ((chamberCorrespondence K' l).symm.transfer q r
        ((truncatedExponentChamberGradedMap φ hl 0).gradedAddHom q.val u) :
          TruncatedExponentChamber K' l 1) := by
  simp only [GradedCorrespondence.transfer_apply, GradedCorrespondence.symm_right,
    GradedCorrespondence.symm_liftLeft, chamberCorrespondence_left_apply,
    chamberCorrespondence_liftRight]
  have he := congrArg (fun z : slabAlgebra (C τ') (1 + T 1) l => z.val.1)
    (truncatedSlabMap_rightChamberLift φ hl q u)
  rw [truncatedSlabMap_fst] at he
  have hp := (truncatedExponentChamberGradedMap φ hl 1).map_directSumDecompose
    (x := (rightChamberLift K k q u).val.1) (i := r)
  simp only [← GradedRingHom.coe_toRingHom, truncatedExponentChamberGradedMap_toRingHom] at hp
  exact hp.trans (congrArg
    (fun z => (DirectSum.decompose (truncatedExponentChamberGrade K' l 1) z r :
      TruncatedExponentChamber K' l 1)) he)

end Mei.FocusFocus
