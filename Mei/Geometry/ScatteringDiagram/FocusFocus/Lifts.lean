/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Grading
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Algebra
public import Mei.RingTheory.Node.Chamber

/-!
# Admissible lifts from the focus-focus chambers

The full exponent pieces of the truncated nodal chambers have canonical incoming
lifts into the slab algebra. Left degrees with horizontal exponent at most zero
lift through powers of `X`; right degrees with horizontal exponent at least zero
lift through powers of `Y`. These are linear maps on whole homogeneous pieces,
including the zero pieces. Their source projections are the identity, and their
opposite projections define a graded correspondence on the actual truncated
chambers, rather than only on their Laurent realizations.

The construction uses `NodeAlgebra.incomingLift`, the faithful chamber Laurent
maps, `truncatedExponentChamberGrade`, and the fiber-product comparison
`algebraEquiv`. The slab coordinates follow Gross–Siebert, *An Invitation to
Toric Degenerations*, §2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)

private theorem parameter_pow : τ ^ (k + 1) = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

private theorem laurent_parameter_pow : (C τ : S[T;T⁻¹]) ^ (k + 1) = 0 := by
  rw [← map_pow, parameter_pow, map_zero]

private theorem leftLaurent_single (q : exponentMonoid) (c : K) :
    leftChamberLaurentMap (laurent_parameter_pow K k)
        (truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c))) =
      single (-q.val.1) (single q.val.2.1 (AdjoinRoot.of _ c) * C τ ^ leftOrder q) := by
  rw [truncatedExponentChamberEquiv_single, leftChamberLaurentMap_mk]
  have he : (rightOrder q : ℤ) - leftOrder q = -q.val.1 := by
    rw [natCast_rightOrder, natCast_leftOrder]
    omega
  simp only [map_mul, map_pow, AlgHom.commutes, leftLaurentMap_coord_zero,
    leftLaurentMap_coord_one, mul_pow, ← C_eq_algebraMap]
  simp only [← single_eq_C, T, single_pow, single_mul_single, one_pow,
    mul_one, zero_add, nsmul_eq_mul, mul_neg_one]
  congr 1
  omega

private theorem rightLaurent_single (q : exponentMonoid) (c : K) :
    rightChamberLaurentMap (laurent_parameter_pow K k)
        (truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c))) =
      single q.val.1 (single q.val.2.1 (AdjoinRoot.of _ c) * C τ ^ rightOrder q) := by
  rw [truncatedExponentChamberEquiv_single, rightChamberLaurentMap_mk]
  have he : (leftOrder q : ℤ) - rightOrder q = q.val.1 := by
    rw [natCast_rightOrder, natCast_leftOrder]
    omega
  simp only [map_mul, map_pow, AlgHom.commutes, rightLaurentMap_coord_zero,
    rightLaurentMap_coord_one, mul_pow, ← C_eq_algebraMap]
  simp only [← single_eq_C, T, single_pow, single_mul_single, one_pow,
    mul_one, zero_add, nsmul_eq_mul, mul_neg_one]
  congr 1
  omega

private theorem leftLaurent_mem_grade (q : ℤ × ℤ × ℤ)
    (u : truncatedExponentChamberGrade K k 1 q) :
    leftChamberLaurentMap (laurent_parameter_pow K k) u.val ∈ grade S[T;T⁻¹] (-q.1) := by
  by_cases hq : q ∈ exponentMonoid
  · obtain ⟨c, hc⟩ := (mem_truncatedExponentChamberGrade_iff_exists K k 1 ⟨q, hq⟩ u.val).mp
      u.property
    rw [← hc, leftLaurent_single]
    exact single_mem_grade _ _
  · have hu : u.val = 0 := by
      simpa only [truncatedExponentChamberGrade_eq_bot_of_notMem K k 1 q hq,
        Submodule.mem_bot] using u.property
    rw [hu, map_zero]
    exact zero_mem _

private theorem rightLaurent_mem_grade (q : ℤ × ℤ × ℤ)
    (u : truncatedExponentChamberGrade K k 0 q) :
    rightChamberLaurentMap (laurent_parameter_pow K k) u.val ∈ grade S[T;T⁻¹] q.1 := by
  by_cases hq : q ∈ exponentMonoid
  · obtain ⟨c, hc⟩ := (mem_truncatedExponentChamberGrade_iff_exists K k 0 ⟨q, hq⟩ u.val).mp
      u.property
    rw [← hc, rightLaurent_single]
    exact single_mem_grade _ _
  · have hu : u.val = 0 := by
      simpa only [truncatedExponentChamberGrade_eq_bot_of_notMem K k 0 q hq,
        Submodule.mem_bot] using u.property
    rw [hu, map_zero]
    exact zero_mem _

private def leftGradeToLaurent (q : ℤ × ℤ × ℤ) :
    truncatedExponentChamberGrade K k 1 q →ₗ[K]
      (grade S[T;T⁻¹] (-q.1)).restrictScalars K :=
  (((leftChamberLaurentMap (laurent_parameter_pow K k)).toLinearMap.restrictScalars K).comp
    (truncatedExponentChamberGrade K k 1 q).subtype).codRestrict _
    (fun u => by
      simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        AlgHom.toLinearMap_apply, Submodule.subtype_apply, Submodule.restrictScalars_mem]
        using leftLaurent_mem_grade K k q u)

private def rightGradeToLaurent (q : ℤ × ℤ × ℤ) :
    truncatedExponentChamberGrade K k 0 q →ₗ[K]
      (grade S[T;T⁻¹] q.1).restrictScalars K :=
  (((rightChamberLaurentMap (laurent_parameter_pow K k)).toLinearMap.restrictScalars K).comp
    (truncatedExponentChamberGrade K k 0 q).subtype).codRestrict _
    (fun u => by
      simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        AlgHom.toLinearMap_apply, Submodule.subtype_apply, Submodule.restrictScalars_mem]
        using rightLaurent_mem_grade K k q u)

/-- Incoming left pieces lift to the slab algebra through the `X` coordinate.
The domain contains every degree with horizontal exponent at most zero. -/
def leftChamberLift (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0}) :
    truncatedExponentChamberGrade K k 1 q.val →ₗ[K]
      slabAlgebra (C τ) (1 + T 1) k :=
  ((algebraEquiv τ k (parameter_pow K k)).toLinearMap.restrictScalars K).comp
    ((((incomingLift (C τ * (1 + T 1)) 0
      ⟨-q.val.1, by simpa only [Set.mem_ofPred_eq] using
        (neg_nonneg.mpr (q.property : q.val.1 ≤ 0))⟩).comp
          (Submodule.restrictScalarsEquiv K S[T;T⁻¹] _
            (grade S[T;T⁻¹] (-q.val.1))).toLinearMap).restrictScalars K).comp
              (leftGradeToLaurent K k q.val))

/-- Incoming right pieces lift through `Y`, retaining the entire coefficient. -/
def rightChamberLift (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1}) :
    truncatedExponentChamberGrade K k 0 q.val →ₗ[K]
      slabAlgebra (C τ) (1 + T 1) k :=
  ((algebraEquiv τ k (parameter_pow K k)).toLinearMap.restrictScalars K).comp
    ((((incomingLift (C τ * (1 + T 1)) 1 ⟨q.val.1, q.property⟩).comp
      (Submodule.restrictScalarsEquiv K S[T;T⁻¹] _
        (grade S[T;T⁻¹] q.val.1)).toLinearMap).restrictScalars K).comp
          (rightGradeToLaurent K k q.val))

/-- Evaluate a left lift by reading the normal Laurent coefficient and
replacing the normal monomial by the corresponding power of `X`. -/
theorem leftChamberLift_apply (h : (C τ : S[T;T⁻¹]) ^ (k + 1) = 0)
    (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    leftChamberLift K k q u = toSlabAlgebra (C τ) (1 + T 1) k
      ((leftChamberLaurentMap h u.val).coeff (-q.val.1) •
        NodeAlgebra.coord (C τ * (1 + T 1)) 0 ^ (-q.val.1).toNat) := by
  dsimp only [leftChamberLift, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply]
  rw [algebraEquiv_apply, incomingLift_apply]
  rfl

/-- Evaluate a right lift by replacing its normal Laurent monomial by a power of `Y`. -/
theorem rightChamberLift_apply (h : (C τ : S[T;T⁻¹]) ^ (k + 1) = 0)
    (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val) :
    rightChamberLift K k q u = toSlabAlgebra (C τ) (1 + T 1) k
      ((rightChamberLaurentMap h u.val).coeff q.val.1 •
        NodeAlgebra.coord (C τ * (1 + T 1)) 1 ^ q.val.1.toNat) := by
  dsimp only [rightChamberLift, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply]
  rw [algebraEquiv_apply, incomingLift_apply]
  rfl

/-- A left monomial `c t^h x^d w^b` lifts to `c t^h X^d W^b`.
This also applies when the cutoff kills the whole piece. -/
@[simp↓]
theorem leftChamberLift_single (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K)
    (hu : truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)) ∈
      truncatedExponentChamberGrade K k 1 q.val) :
    leftChamberLift K k ⟨q.val, hq⟩
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)), hu⟩ =
      toSlabAlgebra (C τ) (1 + T 1) k
        ((single q.val.2.1 (AdjoinRoot.of _ c) * C τ ^ leftOrder q) •
          NodeAlgebra.coord (C τ * (1 + T 1)) 0 ^ (-q.val.1).toNat) := by
  rw [leftChamberLift_apply K k (laurent_parameter_pow K k), leftLaurent_single]
  simp only [coeff_single, Finsupp.single_eq_same]

/-- A right monomial `c t^r y^d w^b` lifts to `c t^r Y^d W^b`, where `r=h-a`. -/
@[simp↓]
theorem rightChamberLift_single (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K)
    (hu : truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)) ∈
      truncatedExponentChamberGrade K k 0 q.val) :
    rightChamberLift K k ⟨q.val, hq⟩
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)), hu⟩ =
      toSlabAlgebra (C τ) (1 + T 1) k
        ((single q.val.2.1 (AdjoinRoot.of _ c) * C τ ^ rightOrder q) •
          NodeAlgebra.coord (C τ * (1 + T 1)) 1 ^ q.val.1.toNat) := by
  rw [rightChamberLift_apply K k (laurent_parameter_pow K k), rightLaurent_single]
  simp only [coeff_single, Finsupp.single_eq_same]

/-- At horizontal degree zero, the two incoming lifts give the same common
tangential lift. The smoothing and Laurent exponents are arbitrary. -/
theorem leftChamberLift_eq_rightChamberLift (q : exponentMonoid) (hq : q.val.1 = 0)
    (c : K)
    (hL : truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)) ∈
      truncatedExponentChamberGrade K k 1 q.val)
    (hR : truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)) ∈
      truncatedExponentChamberGrade K k 0 q.val) :
    leftChamberLift K k ⟨q.val, hq.le⟩
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)), hL⟩ =
      rightChamberLift K k ⟨q.val, hq.ge⟩
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)), hR⟩ := by
  rw [leftChamberLift_single, rightChamberLift_single]
  simp only [hq, neg_zero, Int.toNat_zero, pow_zero, leftOrder_apply, rightOrder_apply, sub_zero]

/-- Projection of the left lift recovers its homogeneous input. -/
@[simp]
theorem leftChamberLift_fst (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    (leftChamberLift K k q u).val.1 = u.val := by
  apply leftChamberLaurentMap_injective_truncatedPolynomial K k
  dsimp only [leftChamberLift, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply]
  rw [algebraEquiv_apply, leftChamberLaurentMap_toSlabAlgebra]
  rw [leftLaurentMap_incomingLift]
  rfl

/-- Projection of the right lift recovers its homogeneous input. -/
@[simp]
theorem rightChamberLift_snd (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val) :
    (rightChamberLift K k q u).val.2 = u.val := by
  apply rightChamberLaurentMap_injective_truncatedPolynomial K k
  dsimp only [rightChamberLift, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply]
  rw [algebraEquiv_apply, rightChamberLaurentMap_toSlabAlgebra]
  rw [rightLaurentMap_incomingLift]
  rfl

/-- The actual truncated chambers and their fiber-product slab form a graded
correspondence, with the geometric incoming half-spaces as admissible degrees. -/
def chamberCorrespondence :
    GradedCorrespondence (B := slabAlgebra (C τ) (1 + T 1) k)
      (truncatedExponentChamberGrade K k 1) (truncatedExponentChamberGrade K k 0)
      {q | q.1 ≤ 0} {q | 0 ≤ q.1} where
  left := ((AlgHom.fst S[T;T⁻¹] _ _).comp
    (slabAlgebra (C τ) (1 + T 1) k).val).toLinearMap.restrictScalars K
  right := ((AlgHom.snd S[T;T⁻¹] _ _).comp
    (slabAlgebra (C τ) (1 + T 1) k).val).toLinearMap.restrictScalars K
  liftLeft := leftChamberLift K k
  liftRight := rightChamberLift K k
  left_liftLeft q := by ext u; exact leftChamberLift_fst K k q u
  right_liftRight q := by ext u; exact rightChamberLift_snd K k q u

/-- The left leg is the actual fiber-product projection. -/
@[simp]
theorem chamberCorrespondence_left_apply (z : slabAlgebra (C τ) (1 + T 1) k) :
    (chamberCorrespondence K k).left z = z.val.1 := (rfl)

/-- The right leg is the actual fiber-product projection. -/
@[simp]
theorem chamberCorrespondence_right_apply (z : slabAlgebra (C τ) (1 + T 1) k) :
    (chamberCorrespondence K k).right z = z.val.2 := (rfl)

/-- The chosen left lift is the homogeneous incoming lift. -/
@[simp]
theorem chamberCorrespondence_liftLeft (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0}) :
    (chamberCorrespondence K k).liftLeft q = leftChamberLift K k q := (rfl)

/-- The chosen right lift is the homogeneous incoming lift. -/
@[simp]
theorem chamberCorrespondence_liftRight (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1}) :
    (chamberCorrespondence K k).liftRight q = rightChamberLift K k q := (rfl)

/-- The two legs of the chamber correspondence are jointly injective. -/
theorem chamberCorrespondence_injective :
    Function.Injective ((chamberCorrespondence K k).left.prod
      (chamberCorrespondence K k).right) := by
  intro x y h
  exact Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

end Mei.FocusFocus
