/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Tangential

/-!
# Individual binomial slab transfers

For the slab parameter `t(1+z^w)` with a nonzero integral tangential exponent
`w`, distinct binomial terms have distinct full exponents. We compute the
individual homogeneous transfers, rather than just their sum. This identifies
exactly the nonzero outgoing decorations, including over coefficient rings
with torsion, nilpotents or zero divisors.

We refine `exponentRightMap_exponentIncomingLift_binomial` and
`exponentCorrespondence_transfer`. The slab interpretation follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, Definitions 3.1–3.3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.NodeAlgebra

open TauCeti AddMonoidAlgebra

variable {R : Type*} [CommRing R] (t c : R) (n : ℕ) (b w : ℤ)

/-- With nonzero integral tangential step, the `j`-th binomial term is the
entire homogeneous transfer at its full exponent, for every natural index.
Indices above `n` have coefficient zero. -/
@[simp↓ high]
theorem exponentCorrespondence_transfer_binomial (hw : w ≠ 0) (j : ℕ) :
    ((exponentCorrespondence (single 0 t + single w t)).transfer
      ⟨((n : ℤ), b), by simp⟩ (-(n : ℤ), b + j * w)
      ⟨single (n, b) c, single_mem_grade _ _⟩ : R[ℤ × ℤ]) =
        single (-(n : ℤ), b + j * w) (c * t ^ n * (n.choose j : R)) := by
  rw [GradedCorrespondence.transfer_apply, exponentCorrespondence_right,
    exponentCorrespondence_liftLeft, AlgHom.toLinearMap_apply,
    exponentRightMap_exponentIncomingLift_binomial, coe_decompose_grade]
  congr 1
  simp only [coeff_sum, Finset.sum_apply', coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro a _ haj
    simp [hw, haj]
  · intro hj
    simp only [Finset.mem_range, not_lt] at hj
    simp [Nat.choose_eq_zero_of_lt (by omega : n < j)]

/-- A nonzero outgoing transfer occurs precisely at a surviving binomial index.
The criterion retains the coefficient product, without cancelling a possibly
nilpotent smoothing parameter or a binomial coefficient in positive characteristic. -/
theorem exponentCorrespondence_transfer_ne_zero_iff (hw : w ≠ 0) (q : ℤ × ℤ) :
    (exponentCorrespondence (single 0 t + single w t)).transfer
      ⟨((n : ℤ), b), by simp⟩ q
      ⟨single (n, b) c, single_mem_grade _ _⟩ ≠ 0 ↔
      ∃ j : ℕ, j ≤ n ∧ q = (-(n : ℤ), b + j * w) ∧
        c * t ^ n * (n.choose j : R) ≠ 0 := by
  have he : (((exponentCorrespondence (single 0 t + single w t)).transfer
      ⟨((n : ℤ), b), by simp⟩ q
      ⟨single (n, b) c, single_mem_grade _ _⟩ : grade R q) : R[ℤ × ℤ]) =
      single q ((∑ j ∈ Finset.range (n + 1),
        single (-(n : ℤ), b + j • w) (c * t ^ n * (n.choose j : R)) : R[ℤ × ℤ]).coeff q) := by
    rw [GradedCorrespondence.transfer_apply, exponentCorrespondence_right,
      exponentCorrespondence_liftLeft, AlgHom.toLinearMap_apply,
      exponentRightMap_exponentIncomingLift_binomial, coe_decompose_grade]
  constructor
  · intro h
    have hc : (∑ j ∈ Finset.range (n + 1),
        single (-(n : ℤ), b + j • w) (c * t ^ n * (n.choose j : R)) : R[ℤ × ℤ]).coeff q ≠ 0 := by
      intro hz
      apply h
      apply Subtype.ext
      rw [he, hz, single_zero]
      rfl
    simp only [coeff_sum, Finset.sum_apply'] at hc
    obtain ⟨j, hj, hjc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    have hq : q = (-(n : ℤ), b + j * w) := by
      by_contra hq
      exact hjc (by simp [coeff_single, Ne.symm hq])
    refine ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), hq, ?_⟩
    simpa [hq, coeff_single, nsmul_eq_mul] using hjc
  · rintro ⟨j, _, rfl, hc⟩ hzero
    have hz := congrArg Subtype.val hzero
    rw [exponentCorrespondence_transfer_binomial t c n b w hw j] at hz
    exact hc (single_eq_zero.mp hz)

end Mei.NodeAlgebra
