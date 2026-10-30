/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Lifts
public import Mei.Geometry.ScatteringDiagram.FocusFocus.GradedMap

/-!
# Reduction of the focus-focus chamber correspondence

Changing coefficients and lowering the cutoff preserves the incoming lifts from
the full exponent pieces of both chambers into the fiber-product slab algebra.
In particular, the chamber correspondences form a compatible system under
truncation, and their homogeneous transfers commute with reduction. Pieces
killed by specialization or truncation are included in these identities.

We use `NodeAlgebra.slabAlgebraMap`, the faithful chamber Laurent maps, and the
graded chamber reductions. The lift comparison uses the coefficient formula for
`NodeAlgebra.incomingLift`; the slab model follows Gross–Siebert, *An Invitation
to Toric Degenerations*, §2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open AddMonoidAlgebra TauCeti Mei.NodeAlgebra _root_.LaurentPolynomial
open _root_.Mei.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable {K K' K'' : Type*} [CommRing K] [CommRing K'] [CommRing K'']
  {k l m : ℕ} (φ : K →+* K') (hl : l ≤ k)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "S'" => AdjoinRoot (Polynomial.X ^ (l + 1) : Polynomial K')
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ'" => AdjoinRoot.root (Polynomial.X ^ (l + 1) : Polynomial K')

/-- Coefficient change and cutoff reduction on the actual fiber-product slab. -/
def truncatedSlabMap : slabAlgebra (C τ) (1 + T 1) k →+*
    slabAlgebra (C τ') (1 + T 1) l :=
  letI : Algebra S[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
  (slabAlgebraMap (C τ) (1 + T 1) (truncatedScalarMap_C_root φ hl)
    (by simp only [RingHom.algebraMap_toAlgebra, map_add, map_one, truncatedScalarMap_T])
    hl).toRingHom

/-- The left projection of slab reduction is the existing chamber reduction. -/
@[simp]
theorem truncatedSlabMap_fst (z : slabAlgebra (C τ) (1 + T 1) k) :
    (truncatedSlabMap φ hl z).val.1 = truncatedExponentChamberMap φ hl 1 z.val.1 := by
  simp only [truncatedSlabMap, coe_slabAlgebraMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    truncatedExponentChamberMap_def]

/-- The right projection of slab reduction is the existing chamber reduction. -/
@[simp]
theorem truncatedSlabMap_snd (z : slabAlgebra (C τ) (1 + T 1) k) :
    (truncatedSlabMap φ hl z).val.2 = truncatedExponentChamberMap φ hl 0 z.val.2 := by
  simp only [truncatedSlabMap, coe_slabAlgebraMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    truncatedExponentChamberMap_def]

/-- With unchanged coefficients and cutoff, slab reduction is the identity. -/
@[simp]
theorem truncatedSlabMap_id :
    truncatedSlabMap (RingHom.id K) (k := k) le_rfl = RingHom.id _ := by
  ext z : 1
  apply Subtype.ext
  apply Prod.ext <;> simp

/-- Successive slab reductions compose in the same order as the coefficient maps. -/
theorem truncatedSlabMap_comp (ψ : K' →+* K'') (hm : m ≤ l) :
    (truncatedSlabMap ψ hm).comp (truncatedSlabMap φ hl) =
      truncatedSlabMap (ψ.comp φ) (hm.trans hl) := by
  ext z : 1
  apply Subtype.ext
  apply Prod.ext
  · simp only [RingHom.comp_apply, truncatedSlabMap_fst]
    exact RingHom.congr_fun (truncatedExponentChamberMap_comp φ hl 1 ψ hm) z.val.1
  · simp only [RingHom.comp_apply, truncatedSlabMap_snd]
    exact RingHom.congr_fun (truncatedExponentChamberMap_comp φ hl 0 ψ hm) z.val.2

/-- Reduction preserves the entire incoming left lift, including zero target pieces. -/
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
  simp only [truncatedSlabMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [slabAlgebraMap_toSlabAlgebra]
  simp only [GradedRingHom.gradedAddHom_apply_coe,
    ← GradedRingHom.coe_toRingHom, truncatedExponentChamberGradedMap_toRingHom,
    truncatedExponentChamberMap_def,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  simp only [he]
  apply congrArg (toSlabAlgebra (C τ') (1 + T 1) l)
  simpa only [incomingLift_apply] using
    mapOfEq_incomingLift (C τ * (1 + T 1)) htf 0
      ⟨-q.val.1, by simpa only [Set.mem_ofPred_eq] using
        (neg_nonneg.mpr (q.property : q.val.1 ≤ 0))⟩
      ⟨leftChamberLaurentMap (C_root_X_pow_pow K (k + 1)) u.val,
        leftLaurent_mem_grade K k q.val u⟩

/-- Reduction preserves the entire incoming right lift, including zero target pieces. -/
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
  simp only [truncatedSlabMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [slabAlgebraMap_toSlabAlgebra]
  simp only [GradedRingHom.gradedAddHom_apply_coe,
    ← GradedRingHom.coe_toRingHom, truncatedExponentChamberGradedMap_toRingHom,
    truncatedExponentChamberMap_def,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  simp only [he]
  apply congrArg (toSlabAlgebra (C τ') (1 + T 1) l)
  simpa only [incomingLift_apply] using
    mapOfEq_incomingLift (C τ * (1 + T 1)) htf 1
      ⟨q.val.1, q.property⟩
      ⟨rightChamberLaurentMap (C_root_X_pow_pow K (k + 1)) u.val,
        rightLaurent_mem_grade K k q.val u⟩

/-- Every left-to-right homogeneous transfer commutes with coefficient change
and cutoff reduction. No survival or nonzero hypothesis is needed. -/
theorem truncatedExponentChamberMap_transfer (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (η : ℤ × ℤ × ℤ) (u : truncatedExponentChamberGrade K k 1 q.val) :
    truncatedExponentChamberMap φ hl 0
        ((chamberCorrespondence K k).transfer q η u) =
      ((chamberCorrespondence K' l).transfer q η
        ((truncatedExponentChamberGradedMap φ hl 1).gradedAddHom q.val u) :
          TruncatedExponentChamber K' l 0) := by
  have h := congrArg (fun z => z.val.2) (truncatedSlabMap_leftChamberLift φ hl q u)
  simp only [truncatedSlabMap_snd] at h
  simp only [GradedCorrespondence.transfer_apply, chamberCorrespondence_liftLeft,
    chamberCorrespondence_right_apply]
  simpa only [← GradedRingHom.coe_toRingHom,
    truncatedExponentChamberGradedMap_toRingHom, h] using
    (truncatedExponentChamberGradedMap φ hl 0).map_directSumDecompose
      (x := (leftChamberLift K k q u).val.2) (i := η)

/-- Right-to-left homogeneous transfer also commutes with coefficient change
and cutoff reduction. -/
theorem truncatedExponentChamberMap_symm_transfer (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (η : ℤ × ℤ × ℤ) (u : truncatedExponentChamberGrade K k 0 q.val) :
    truncatedExponentChamberMap φ hl 1
        ((chamberCorrespondence K k).symm.transfer q η u) =
      ((chamberCorrespondence K' l).symm.transfer q η
        ((truncatedExponentChamberGradedMap φ hl 0).gradedAddHom q.val u) :
          TruncatedExponentChamber K' l 1) := by
  have h := congrArg (fun z => z.val.1) (truncatedSlabMap_rightChamberLift φ hl q u)
  simp only [truncatedSlabMap_fst] at h
  simp only [GradedCorrespondence.transfer_apply, GradedCorrespondence.symm_liftLeft,
    GradedCorrespondence.symm_right, chamberCorrespondence_liftRight,
    chamberCorrespondence_left_apply]
  simpa only [← GradedRingHom.coe_toRingHom,
    truncatedExponentChamberGradedMap_toRingHom, h] using
    (truncatedExponentChamberGradedMap φ hl 1).map_directSumDecompose
      (x := (rightChamberLift K k q u).val.1) (i := η)

end Mei.FocusFocus
