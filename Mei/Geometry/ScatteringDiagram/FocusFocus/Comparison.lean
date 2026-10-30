/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.ChamberTransfer
public import Mei.LinearAlgebra.GradedCorrespondence.Hom
public import Mei.LinearAlgebra.GradedCorrespondence.RestrictScalars

/-!
# Comparing focus-focus chamber and Laurent slab correspondences

The faithful Laurent realizations of the truncated chambers, together with the
inverse slab algebra isomorphism, form a morphism of graded correspondences.
Normal and tangential exponents are retained; the smoothing exponent becomes
part of the coefficient in `K[t]/(t^(k+1))`. Both admissible incoming lifts are
preserved, including when their whole homogeneous source piece is zero. Full
chamber transfer components realize as Laurent monomials with the same binomial
coefficient and smoothing powers, so their survival is detected by that coefficient.

We use `FocusFocus.algebraEquiv`, the chamber Laurent realization squares,
`NodeAlgebra.exponentCorrespondence`, and Mathlib's `curryAlgEquiv`. This is the
slab comparison of Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties
with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "ι" => AdjoinRoot.of (Polynomial.X ^ (k + 1) : Polynomial K)

-- Compose the existing coefficient actions through the tangential Laurent algebra.
local instance : IsScalarTower K S (SlabNode τ) :=
  IsScalarTower.to₁₂₄ K S S[ℤ] _

/-- The left Laurent embedding with normal and tangential exponents uncurried. -/
def leftChamberExponentMap : TruncatedExponentChamber K k 1 →ₐ[K] S[ℤ × ℤ] :=
  ((curryAlgEquiv S).symm.toAlgHom.restrictScalars K).comp
    ((leftChamberLaurentMap (C_root_X_pow_pow K (k + 1))).restrictScalars K)

/-- The left embedding is the original realization followed by uncurrying. -/
@[simp]
theorem leftChamberExponentMap_apply (x : TruncatedExponentChamber K k 1) :
    leftChamberExponentMap K k x =
      (curryAlgEquiv S).symm (leftChamberLaurentMap (C_root_X_pow_pow K (k + 1)) x) := (rfl)

/-- The right Laurent embedding with both exponents retained. -/
def rightChamberExponentMap : TruncatedExponentChamber K k 0 →ₐ[K] S[ℤ × ℤ] :=
  ((curryAlgEquiv S).symm.toAlgHom.restrictScalars K).comp
    ((rightChamberLaurentMap (C_root_X_pow_pow K (k + 1))).restrictScalars K)

/-- The right embedding is the original realization followed by uncurrying. -/
@[simp]
theorem rightChamberExponentMap_apply (x : TruncatedExponentChamber K k 0) :
    rightChamberExponentMap K k x =
      (curryAlgEquiv S).symm (rightChamberLaurentMap (C_root_X_pow_pow K (k + 1)) x) := (rfl)

/-- Laurent realization of each full left-to-right component preserves its whole
coefficient, absorbing precisely the incoming and crossing smoothing powers. -/
theorem rightChamberExponentMap_transfer_single (q : exponentMonoid)
    (hq : q.val.1 ≤ 0) (c : K) (j : ℕ) :
    rightChamberExponentMap K k
      ((chamberCorrespondence K k).transfer ⟨q.val, hq⟩
        (q + tangentDegree j).val
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩) =
      single (q.val.1, q.val.2.1 + j)
        ((ι c * τ ^ leftOrder q) * τ ^ q.val.1.natAbs *
          (q.val.1.natAbs.choose j : S)) := by
  rw [chamberCorrespondence_transfer_single, rightChamberExponentMap_apply,
    rightChamberLaurentMap_single]
  have habs : (-q.val.1).toNat = q.val.1.natAbs := by omega
  simp only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.fst_add, Prod.snd_add,
    add_zero, map_add, rightOrder_apply, sub_zero, Int.toNat_zero, habs]
  rw [← rightOrder_apply, rightOrder_eq_leftOrder_add_natAbs q hq]
  simp only [map_mul, map_natCast, ← single_eq_C, single_pow, nsmul_zero,
    single_mul_single, add_zero]
  rw [← curryAlgEquiv_single (R := S), AlgEquiv.symm_apply_apply, pow_add τ]
  congr 1
  ring

/-- The reverse crossing has the same scalar coefficient and opposite normal
Laurent exponent. Its smoothing exponent remains in the full chamber degree. -/
theorem leftChamberExponentMap_symm_transfer_single (q : exponentMonoid)
    (hq : 0 ≤ q.val.1) (c : K) (j : ℕ) :
    leftChamberExponentMap K k
      ((chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩
        (q + tangentDegree j).val
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩) =
      single (-q.val.1, q.val.2.1 + j)
        ((ι c * τ ^ rightOrder q) * τ ^ q.val.1.natAbs *
          (q.val.1.natAbs.choose j : S)) := by
  rw [chamberCorrespondence_symm_transfer_single, leftChamberExponentMap_apply,
    leftChamberLaurentMap_single]
  have habs : q.val.1.toNat = q.val.1.natAbs := by omega
  simp only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.fst_add, Prod.snd_add,
    add_zero, map_add, leftOrder_apply, Int.toNat_zero, habs]
  rw [← leftOrder_apply, leftOrder_eq_rightOrder_add_natAbs q hq]
  simp only [map_mul, map_natCast, ← single_eq_C, single_pow, nsmul_zero,
    single_mul_single, add_zero]
  rw [← curryAlgEquiv_single (R := S), AlgEquiv.symm_apply_apply, pow_add τ]
  congr 1
  ring

/-- A full left-to-right component survives exactly when its Laurent coefficient
is nonzero, including all smoothing powers and the binomial factor. -/
theorem chamberCorrespondence_transfer_single_ne_zero_iff_laurent (q : exponentMonoid)
    (hq : q.val.1 ≤ 0) (c : K) (j : ℕ) :
    (chamberCorrespondence K k).transfer ⟨q.val, hq⟩
      (q + tangentDegree j).val
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ↔
        (ι c * τ ^ leftOrder q) * τ ^ q.val.1.natAbs *
          (q.val.1.natAbs.choose j : S) ≠ 0 := by
  have hinj : Function.Injective (rightChamberExponentMap K k) := by
    intro x y hxy
    apply rightChamberLaurentMap_injective_truncatedPolynomial K k
    apply (curryAlgEquiv S).symm.injective
    simpa only [rightChamberExponentMap_apply] using hxy
  simp only [ne_eq, ← Submodule.coe_eq_zero]
  rw [← map_eq_zero_iff (rightChamberExponentMap K k) hinj,
    rightChamberExponentMap_transfer_single, AddMonoidAlgebra.single_eq_zero]

/-- A full right-to-left component survives exactly when its Laurent coefficient
is nonzero, including all smoothing powers and the binomial factor. -/
theorem chamberCorrespondence_symm_transfer_single_ne_zero_iff_laurent (q : exponentMonoid)
    (hq : 0 ≤ q.val.1) (c : K) (j : ℕ) :
    (chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩
      (q + tangentDegree j).val
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ↔
        (ι c * τ ^ rightOrder q) * τ ^ q.val.1.natAbs *
          (q.val.1.natAbs.choose j : S) ≠ 0 := by
  have hinj : Function.Injective (leftChamberExponentMap K k) := by
    intro x y hxy
    apply leftChamberLaurentMap_injective_truncatedPolynomial K k
    apply (curryAlgEquiv S).symm.injective
    simpa only [leftChamberExponentMap_apply] using hxy
  simp only [ne_eq, ← Submodule.coe_eq_zero]
  rw [← map_eq_zero_iff (leftChamberExponentMap K k) hinj,
    leftChamberExponentMap_symm_transfer_single, AddMonoidAlgebra.single_eq_zero]

/-- The inverse slab dictionary preserves every admissible left lift, with
the whole smoothing coefficient retained in the Laurent input. -/
theorem algebraEquiv_symm_leftChamberLift (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))).symm
        (leftChamberLift K k q u) =
      exponentIncomingLift (C τ * (1 + T 1)) 0
        ⟨(-q.val.1, q.val.2.1), by
          simpa only [Set.mem_ofPred_eq] using neg_nonneg.mpr (q.property : q.val.1 ≤ 0)⟩
        ⟨leftChamberExponentMap K k u.val,
          by simpa only [leftChamberExponentMap_apply] using
            leftChamberLaurentMap_mem_exponentGrade K k q.val u.val u.property⟩ := by
  rw [leftChamberLift_apply K k (C_root_X_pow_pow K (k + 1)),
    ← algebraEquiv_apply τ k (AdjoinRoot.root_X_pow_pow (k + 1)),
    AlgEquiv.symm_apply_apply,
    exponentIncomingLift_apply (C τ * (1 + T 1)) 0
      ⟨(-q.val.1, q.val.2.1), by
        simpa only [Set.mem_ofPred_eq] using neg_nonneg.mpr (q.property : q.val.1 ≤ 0)⟩,
    incomingLift_apply]
  simp only [leftChamberExponentMap_apply, AlgEquiv.apply_symm_apply]

/-- The inverse dictionary likewise preserves every admissible right lift. -/
theorem algebraEquiv_symm_rightChamberLift (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val) :
    (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))).symm
        (rightChamberLift K k q u) =
      exponentIncomingLift (C τ * (1 + T 1)) 1
        ⟨(q.val.1, q.val.2.1), q.property⟩
        ⟨rightChamberExponentMap K k u.val,
          by simpa only [rightChamberExponentMap_apply] using
            rightChamberLaurentMap_mem_exponentGrade K k q.val u.val u.property⟩ := by
  rw [rightChamberLift_apply K k (C_root_X_pow_pow K (k + 1)),
    ← algebraEquiv_apply τ k (AdjoinRoot.root_X_pow_pow (k + 1)),
    AlgEquiv.symm_apply_apply,
    exponentIncomingLift_apply (C τ * (1 + T 1)) 1 ⟨(q.val.1, q.val.2.1), q.property⟩,
    incomingLift_apply]
  simp only [rightChamberExponentMap_apply, AlgEquiv.apply_symm_apply]

/-- The chamber-to-Laurent comparison preserves the span and the chosen lifts.
The left normal exponent is `-a`, the right normal exponent is `a`. -/
def chamberLaurentComparison :
    GradedCorrespondence.Hom (chamberCorrespondence K k)
      ((exponentCorrespondence (C τ * (1 + T 1))).restrictScalars K)
      (fun q => (-q.1, q.2.1)) (fun q => (q.1, q.2.1)) where
  middle :=
    (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))).symm.toLinearMap.restrictScalars K
  left := (leftChamberExponentMap K k).toLinearMap
  right := (rightChamberExponentMap K k).toLinearMap
  left_comm := by
    apply LinearMap.ext
    intro z
    apply (curryAlgEquiv S).injective
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply, chamberCorrespondence_left_apply,
      GradedCorrespondence.restrictScalars_left, exponentCorrespondence_left,
      leftChamberExponentMap_apply, AlgEquiv.apply_symm_apply, curry_exponentLeftMap]
    rw [← leftChamberLaurentMap_toSlabAlgebra (1 + T 1)
      (C_root_X_pow_pow K (k + 1)),
      ← algebraEquiv_apply τ k (AdjoinRoot.root_X_pow_pow (k + 1)),
      AlgEquiv.apply_symm_apply]
  right_comm := by
    apply LinearMap.ext
    intro z
    apply (curryAlgEquiv S).injective
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply, chamberCorrespondence_right_apply,
      GradedCorrespondence.restrictScalars_right, exponentCorrespondence_right,
      rightChamberExponentMap_apply, AlgEquiv.apply_symm_apply, curry_exponentRightMap]
    rw [← rightChamberLaurentMap_toSlabAlgebra (1 + T 1)
      (C_root_X_pow_pow K (k + 1)),
      ← algebraEquiv_apply τ k (AdjoinRoot.root_X_pow_pow (k + 1)),
      AlgEquiv.apply_symm_apply]
  left_mem q x hx := by simpa only [AlgHom.toLinearMap_apply,
    Submodule.restrictScalars_mem, leftChamberExponentMap_apply] using
    leftChamberLaurentMap_mem_exponentGrade K k q x hx
  right_mem q x hx := by simpa only [AlgHom.toLinearMap_apply,
    Submodule.restrictScalars_mem, rightChamberExponentMap_apply] using
    rightChamberLaurentMap_mem_exponentGrade K k q x hx
  admissible_left q h := by
    simpa only [Set.mem_ofPred_eq] using neg_nonneg.mpr (h : q.1 ≤ 0)
  admissible_right _ h := h
  middle_liftLeft q u := by
    simp only [chamberCorrespondence_liftLeft,
      GradedCorrespondence.restrictScalars_liftLeft_apply, exponentCorrespondence_liftLeft,
      LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply]
    -- Identify the admissible and homogeneous subtypes after regrading.
    convert algebraEquiv_symm_leftChamberLift K k q u using 1
    congr 2
  middle_liftRight q u := by
    simp only [chamberCorrespondence_liftRight,
      GradedCorrespondence.restrictScalars_liftRight_apply, exponentCorrespondence_liftRight,
      LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply]
    -- Identify the admissible and homogeneous subtypes after regrading.
    convert algebraEquiv_symm_rightChamberLift K k q u using 1
    congr 2

/-- The middle comparison is the inverse slab algebra dictionary. -/
@[simp]
theorem chamberLaurentComparison_middle :
    (chamberLaurentComparison K k).middle =
      (algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))).symm.toLinearMap.restrictScalars K :=
  (rfl)

/-- The left leg of the comparison is the faithful left Laurent realization. -/
@[simp]
theorem chamberLaurentComparison_left :
    (chamberLaurentComparison K k).left = (leftChamberExponentMap K k).toLinearMap := (rfl)

/-- The right leg is the faithful right Laurent realization. -/
@[simp]
theorem chamberLaurentComparison_right :
    (chamberLaurentComparison K k).right = (rightChamberExponentMap K k).toLinearMap := (rfl)

end Mei.FocusFocus
