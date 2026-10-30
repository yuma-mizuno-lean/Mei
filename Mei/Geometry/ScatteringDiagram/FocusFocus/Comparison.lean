/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Lifts
public import Mei.RingTheory.Node.Tangential
public import Mei.LinearAlgebra.GradedCorrespondence.Hom
public import Mei.LinearAlgebra.GradedCorrespondence.RestrictScalars

/-!
# Comparing focus-focus chamber and Laurent slab correspondences

The faithful Laurent realizations of the truncated chambers, together with the
inverse slab algebra isomorphism, form a morphism of graded correspondences.
Normal and tangential exponents are retained; the smoothing exponent becomes
part of the coefficient in `K[t]/(t^(k+1))`. Both admissible incoming lifts are
preserved, including when their whole homogeneous source piece is zero.

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

/-- The uncurried left realization is faithful over the original coefficient ring. -/
theorem leftChamberExponentMap_injective : Function.Injective (leftChamberExponentMap K k) :=
  (curryAlgEquiv S).symm.injective.comp
    (leftChamberLaurentMap_injective_truncatedPolynomial K k)

/-- The uncurried right realization is faithful over the original coefficient ring. -/
theorem rightChamberExponentMap_injective : Function.Injective (rightChamberExponentMap K k) :=
  (curryAlgEquiv S).symm.injective.comp
    (rightChamberLaurentMap_injective_truncatedPolynomial K k)

/-- The left realization puts the entire smoothing power into the Laurent coefficient. -/
@[simp↓]
theorem leftChamberExponentMap_single (q : exponentMonoid) (c : K) :
    leftChamberExponentMap K k
        (truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c))) =
      single (-q.val.1, q.val.2.1) (AdjoinRoot.of _ c * τ ^ leftOrder q) := by
  rw [leftChamberExponentMap_apply, leftChamberLaurentMap_single]
  apply (curryAlgEquiv S).injective
  rw [AlgEquiv.apply_symm_apply, curryAlgEquiv_single]
  simp [← single_eq_C, -single_eq_C_mul_T]

/-- The right realization puts the entire smoothing power into the Laurent coefficient. -/
@[simp↓]
theorem rightChamberExponentMap_single (q : exponentMonoid) (c : K) :
    rightChamberExponentMap K k
        (truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c))) =
      single (q.val.1, q.val.2.1) (AdjoinRoot.of _ c * τ ^ rightOrder q) := by
  rw [rightChamberExponentMap_apply, rightChamberLaurentMap_single]
  apply (curryAlgEquiv S).injective
  rw [AlgEquiv.apply_symm_apply, curryAlgEquiv_single]
  simp [← single_eq_C, -single_eq_C_mul_T]

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
