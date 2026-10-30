/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Lifts
public import Mei.RingTheory.Node.Tangential

/-!
# Binomial transfers between the truncated focus-focus chambers

An incoming monomial with horizontal exponent `a` propagates across the slab by
multiplication by `(1+w)^|a|`. We compute the opposite projection of each lift
and its individual full exponent components in the actual truncated chambers.
The smoothing exponent is retained. Thus a component can vanish either because
its coefficient vanishes or because the opposite chamber cutoff kills it.

We use the faithful Laurent realizations, `leftChamberLift`, `rightChamberLift`,
the chamber exponent decomposition, and the binomial Laurent expansions
`NodeAlgebra.exponentRightMap_exponentIncomingLift_binomial` and
`NodeAlgebra.exponentLeftMap_exponentIncomingLift_binomial`. The decorations are those of
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)

/-- The opposite projection of a left lift is the full binomial expansion,
with the original smoothing exponent and the right chamber cutoff. -/
theorem leftChamberLift_snd_single (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K) :
    (leftChamberLift K k ⟨q.val, hq⟩
      ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩).val.2 =
      ∑ j ∈ Finset.range ((-q.val.1).toNat + 1),
        truncatedExponentChamberEquiv K k 0
          (Ideal.Quotient.mk _ (single (q + tangentDegree j)
            (c * ((-q.val.1).toNat.choose j : K)))) := by
  apply rightChamberLaurentMap_injective_truncatedPolynomial K k
  rw [leftChamberLift_single, rightChamberLaurentMap_toSlabAlgebra]
  have hf : C τ * (1 + T 1) = single 0 τ + single 1 τ := by
    simp [mul_add, ← single_eq_C, T, single_mul_single, -single_eq_C_mul_T]
  rw [hf]
  have hb := congrArg (curryAlgEquiv S)
    (exponentRightMap_exponentIncomingLift_binomial τ
      (AdjoinRoot.of _ c * τ ^ leftOrder q) (-q.val.1).toNat q.val.2.1 1)
  simp only [curry_exponentRightMap, exponentIncomingLift_single, map_sum,
    curryAlgEquiv_single] at hb
  have hc : single q.val.2.1 (AdjoinRoot.of _ c) * C τ ^ leftOrder q =
      single q.val.2.1 (AdjoinRoot.of _ c * τ ^ leftOrder q) := by
    rw [← map_pow]
    simp only [← single_eq_C, single_mul_single, add_zero]
  rw [hc, hb]
  simp only [map_sum, rightChamberLaurentMap_single]
  have he : rightOrder q = leftOrder q + (-q.val.1).toNat := by
    have := natCast_leftOrder q
    have := natCast_rightOrder q
    omega
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_add, rightOrder_apply, AddSubmonoid.coe_add, coe_tangentDegree,
    Prod.fst_add, Prod.snd_add, add_zero, sub_zero, Int.toNat_zero]
  simp [← rightOrder_apply, he, pow_add, ← single_eq_C, single_mul_single,
    Int.toNat_of_nonneg (neg_nonneg.mpr hq), mul_assoc, -single_eq_C_mul_T]
  ring

/-- The opposite projection of a right lift is the full binomial expansion,
with the original smoothing exponent and the left chamber cutoff. -/
theorem rightChamberLift_fst_single (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K) :
    (rightChamberLift K k ⟨q.val, hq⟩
      ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩).val.1 =
      ∑ j ∈ Finset.range (q.val.1.toNat + 1),
        truncatedExponentChamberEquiv K k 1
          (Ideal.Quotient.mk _ (single (q + tangentDegree j)
            (c * (q.val.1.toNat.choose j : K)))) := by
  apply leftChamberLaurentMap_injective_truncatedPolynomial K k
  rw [rightChamberLift_single, leftChamberLaurentMap_toSlabAlgebra]
  have hf : C τ * (1 + T 1) = single 0 τ + single 1 τ := by
    simp [mul_add, ← single_eq_C, T, single_mul_single, -single_eq_C_mul_T]
  rw [hf]
  have hb := congrArg (curryAlgEquiv S)
    (exponentLeftMap_exponentIncomingLift_binomial τ
      (AdjoinRoot.of _ c * τ ^ rightOrder q) q.val.1.toNat q.val.2.1 1)
  simp only [curry_exponentLeftMap, exponentIncomingLift_single, map_sum,
    curryAlgEquiv_single] at hb
  have hc : single q.val.2.1 (AdjoinRoot.of _ c) * C τ ^ rightOrder q =
      single q.val.2.1 (AdjoinRoot.of _ c * τ ^ rightOrder q) := by
    rw [← map_pow]
    simp only [← single_eq_C, single_mul_single, add_zero]
  rw [hc, hb]
  simp only [map_sum, leftChamberLaurentMap_single]
  have he : leftOrder q = rightOrder q + q.val.1.toNat := by
    have := natCast_rightOrder q
    have := natCast_leftOrder q
    omega
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_add, leftOrder_apply, AddSubmonoid.coe_add, coe_tangentDegree,
    Prod.fst_add, Prod.snd_add, add_zero, Int.toNat_zero]
  simp [← leftOrder_apply, he, pow_add, ← single_eq_C, single_mul_single,
    Int.toNat_of_nonneg hq, mul_assoc, -single_eq_C_mul_T]
  ring

/-- The entire component of a left-to-right crossing at its `j`-th binomial
exponent. Indices above the horizontal multiplicity give zero automatically. -/
@[simp↓]
theorem chamberCorrespondence_transfer_single (q : exponentMonoid)
    (hq : q.val.1 ≤ 0) (c : K) (j : ℕ) :
    ((chamberCorrespondence K k).transfer ⟨q.val, hq⟩ (q + tangentDegree j).val
      ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩ :
          TruncatedExponentChamber K k 0) =
      truncatedExponentChamberEquiv K k 0
        (Ideal.Quotient.mk _ (single (q + tangentDegree j)
          (c * ((-q.val.1).toNat.choose j : K)))) := by
  simp only [GradedCorrespondence.transfer_apply, chamberCorrespondence_right_apply,
    chamberCorrespondence_liftLeft]
  rw [leftChamberLift_snd_single K k q hq c]
  simp only [← map_sum]
  rw [coe_decompose_truncatedExponentChamberGrade, AlgEquiv.symm_apply_apply,
    coe_decompose_exponentOrderGrade_mk]
  congr 2
  simp only [coeff_sum, Finset.sum_apply', coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro a _ haj
    have hne : q + tangentDegree a ≠ q + tangentDegree j := by
      intro h
      have := congrArg (fun r : exponentMonoid => r.val.2.1) h
      simp only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add] at this
      exact haj (by omega)
    simp [hne]
  · intro hj
    have hlt : (-q.val.1).toNat < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hlt]

/-- The entire component of a right-to-left crossing at its `j`-th binomial
exponent. Indices above the horizontal multiplicity give zero automatically. -/
@[simp↓]
theorem chamberCorrespondence_symm_transfer_single (q : exponentMonoid)
    (hq : 0 ≤ q.val.1) (c : K) (j : ℕ) :
    ((chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩ (q + tangentDegree j).val
      ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩ :
          TruncatedExponentChamber K k 1) =
      truncatedExponentChamberEquiv K k 1
        (Ideal.Quotient.mk _ (single (q + tangentDegree j)
          (c * (q.val.1.toNat.choose j : K)))) := by
  simp only [GradedCorrespondence.transfer_apply, GradedCorrespondence.symm_right,
    GradedCorrespondence.symm_liftLeft,
    chamberCorrespondence_left_apply, chamberCorrespondence_liftRight]
  rw [rightChamberLift_fst_single K k q hq c]
  simp only [← map_sum]
  rw [coe_decompose_truncatedExponentChamberGrade, AlgEquiv.symm_apply_apply,
    coe_decompose_exponentOrderGrade_mk]
  congr 2
  simp only [coeff_sum, Finset.sum_apply', coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro a _ haj
    have hne : q + tangentDegree a ≠ q + tangentDegree j := by
      intro h
      have := congrArg (fun r : exponentMonoid => r.val.2.1) h
      simp only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add] at this
      exact haj (by omega)
    simp [hne]
  · intro hj
    have hlt : q.val.1.toNat < j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hlt]

/-- A specified left-to-right binomial branch survives exactly when its whole
coefficient and its exponent survive in the target chamber. -/
@[simp↓]
theorem chamberCorrespondence_transfer_single_ne_zero_iff (q : exponentMonoid)
    (hq : q.val.1 ≤ 0) (c : K) (j : ℕ) :
    (chamberCorrespondence K k).transfer ⟨q.val, hq⟩ (q + tangentDegree j).val
      ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ↔
      c * ((-q.val.1).toNat.choose j : K) ≠ 0 ∧ rightOrder q ≤ k := by
  simp only [ne_eq, ← Submodule.coe_eq_zero]
  rw [chamberCorrespondence_transfer_single]
  rw [map_eq_zero_iff _ (truncatedExponentChamberEquiv K k 0).injective,
    exponentOrderQuotient_single_eq_zero_iff]
  simp [rightOrder_apply]

/-- A specified right-to-left binomial branch survives exactly when its whole
coefficient and its exponent survive in the target chamber. -/
@[simp↓]
theorem chamberCorrespondence_symm_transfer_single_ne_zero_iff (q : exponentMonoid)
    (hq : 0 ≤ q.val.1) (c : K) (j : ℕ) :
    (chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩ (q + tangentDegree j).val
      ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ↔
      c * (q.val.1.toNat.choose j : K) ≠ 0 ∧ leftOrder q ≤ k := by
  simp only [ne_eq, ← Submodule.coe_eq_zero]
  rw [chamberCorrespondence_symm_transfer_single]
  rw [map_eq_zero_iff _ (truncatedExponentChamberEquiv K k 1).injective,
    exponentOrderQuotient_single_eq_zero_iff]
  simp [leftOrder_apply]

/-- These binomial branches exhaust all nonzero left-to-right transfers in the
full exponent grading, including the smoothing degree. -/
theorem chamberCorrespondence_transfer_ne_zero_iff (q : exponentMonoid)
    (hq : q.val.1 ≤ 0) (c : K) (η : ℤ × ℤ × ℤ) :
    (chamberCorrespondence K k).transfer ⟨q.val, hq⟩ η
      ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ↔
      ∃ j : ℕ, j ≤ (-q.val.1).toNat ∧ η = (q + tangentDegree j).val ∧
        c * ((-q.val.1).toNat.choose j : K) ≠ 0 ∧ rightOrder q ≤ k := by
  constructor
  · intro h
    have hs : (∑ j ∈ Finset.range ((-q.val.1).toNat + 1),
        (DirectSum.decompose (truncatedExponentChamberGrade K k 0)
          (truncatedExponentChamberEquiv K k 0
            (Ideal.Quotient.mk _ (single (q + tangentDegree j)
              (c * ((-q.val.1).toNat.choose j : K))))) η :
                TruncatedExponentChamber K k 0)) ≠ 0 := by
      simpa only [ne_eq, ← Submodule.coe_eq_zero, GradedCorrespondence.transfer_apply,
        chamberCorrespondence_right_apply, chamberCorrespondence_liftLeft,
        leftChamberLift_snd_single K k q hq c, DirectSum.decompose_sum,
        DirectSum.sum_apply, Submodule.coe_sum] using h
    obtain ⟨j, hj, hjn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    have he : η = (q + tangentDegree j).val := by
      by_contra he
      exact hjn (DirectSum.decompose_of_mem_ne _
        ((mem_truncatedExponentChamberGrade_iff_exists K k 0 (q + tangentDegree j) _).mpr
          ⟨_, rfl⟩) (Ne.symm he))
    refine ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), he, ?_⟩
    subst η
    exact (chamberCorrespondence_transfer_single_ne_zero_iff K k q hq c j).mp h
  · rintro ⟨j, _, rfl, hc, hk⟩
    exact (chamberCorrespondence_transfer_single_ne_zero_iff K k q hq c j).mpr ⟨hc, hk⟩

/-- These binomial branches exhaust all nonzero right-to-left transfers in the
full exponent grading, including the smoothing degree. -/
theorem chamberCorrespondence_symm_transfer_ne_zero_iff (q : exponentMonoid)
    (hq : 0 ≤ q.val.1) (c : K) (η : ℤ × ℤ × ℤ) :
    (chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩ η
      ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ↔
      ∃ j : ℕ, j ≤ q.val.1.toNat ∧ η = (q + tangentDegree j).val ∧
        c * (q.val.1.toNat.choose j : K) ≠ 0 ∧ leftOrder q ≤ k := by
  constructor
  · intro h
    have hs : (∑ j ∈ Finset.range (q.val.1.toNat + 1),
        (DirectSum.decompose (truncatedExponentChamberGrade K k 1)
          (truncatedExponentChamberEquiv K k 1
            (Ideal.Quotient.mk _ (single (q + tangentDegree j)
              (c * (q.val.1.toNat.choose j : K))))) η :
                TruncatedExponentChamber K k 1)) ≠ 0 := by
      simpa only [ne_eq, ← Submodule.coe_eq_zero, GradedCorrespondence.transfer_apply,
        GradedCorrespondence.symm_right, GradedCorrespondence.symm_liftLeft,
        chamberCorrespondence_left_apply, chamberCorrespondence_liftRight,
        rightChamberLift_fst_single K k q hq c, DirectSum.decompose_sum,
        DirectSum.sum_apply, Submodule.coe_sum] using h
    obtain ⟨j, hj, hjn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    have he : η = (q + tangentDegree j).val := by
      by_contra he
      exact hjn (DirectSum.decompose_of_mem_ne _
        ((mem_truncatedExponentChamberGrade_iff_exists K k 1 (q + tangentDegree j) _).mpr
          ⟨_, rfl⟩) (Ne.symm he))
    refine ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), he, ?_⟩
    subst η
    exact (chamberCorrespondence_symm_transfer_single_ne_zero_iff K k q hq c j).mp h
  · rintro ⟨j, _, rfl, hc, hk⟩
    exact (chamberCorrespondence_symm_transfer_single_ne_zero_iff K k q hq c j).mpr ⟨hc, hk⟩

end Mei.FocusFocus
