/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Incoming.Basic

/-!
# Incoming rays in the truncated focus-focus chambers

An incoming chamber monomial is a whole element of the truncated chamber.
Its faithful Laurent realization absorbs its smoothing power into the scalar
coefficient. The two coefficient choices give the same incoming geometric rays,
including invariant vertical rays, and discard exactly the same vanishing inputs.
We compare the finite sums of their decorations. Adding the constant incoming
section for zero spatial degree gives the original chamber monomial.

These are noncrossing families: proper rays remain on the incoming side and
avoid the slab and the affine singularity. The stationary contribution is
included separately from proper rays. We use the chamber Laurent embeddings,
`IncomingSlabBrokenLine.coefficientEquiv` and `incomingSlabWeightedEvaluation_eq`.
The incoming data follow Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ) (q : exponentMonoid) (c : K) (Q : ℝ × ℝ)

local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "u₋" => truncatedExponentChamberEquiv K k 1
  (Ideal.Quotient.mk _ (single q c))
local notation "u₊" => truncatedExponentChamberEquiv K k 0
  (Ideal.Quotient.mk _ (single q c))
local notation "a₋" => AdjoinRoot.of (Polynomial.X ^ (k + 1) : Polynomial K) c * τ ^ leftOrder q
local notation "a₊" => AdjoinRoot.of (Polynomial.X ^ (k + 1) : Polynomial K) c * τ ^ rightOrder q

private theorem leftIncoming_eq_zero_iff : u₋ = 0 ↔ a₋ = 0 := by
  rw [← map_eq_zero_iff (leftChamberExponentMap K k)
    (leftChamberExponentMap_injective K k), leftChamberExponentMap_single, single_eq_zero]

private theorem rightIncoming_eq_zero_iff : u₊ = 0 ↔ a₊ = 0 := by
  rw [← map_eq_zero_iff (rightChamberExponentMap K k)
    (rightChamberExponentMap_injective K k), rightChamberExponentMap_single, single_eq_zero]

/-- The whole left chamber monomial and its Laurent scalar give the same
incoming-ray fiber, including vertical rays and coefficients killed by the cutoff. -/
def leftChamberIncomingRayEquiv :
    IncomingSlabBrokenLine u₋ q.val.1 q.val.2.1 Q ≃
      IncomingSlabBrokenLine a₋ q.val.1 q.val.2.1 Q :=
  IncomingSlabBrokenLine.coefficientEquiv (leftIncoming_eq_zero_iff K k q c)

/-- The whole right chamber monomial has the corresponding Laurent incoming-ray fiber. -/
def rightChamberIncomingRayEquiv :
    IncomingSlabBrokenLine u₊ q.val.1 q.val.2.1 Q ≃
      IncomingSlabBrokenLine a₊ q.val.1 q.val.2.1 Q :=
  IncomingSlabBrokenLine.coefficientEquiv (rightIncoming_eq_zero_iff K k q c)

/-- The left Laurent embedding preserves the finite sum of whole incoming
chamber decorations. Vanishing coefficients and zero spatial degree give empty fibers. -/
theorem leftChamberExponentMap_sum_incoming (hq : q.val.1 ≤ 0) :
    leftChamberExponentMap K k
        (∑ _β : IncomingSlabBrokenLine u₋ q.val.1 q.val.2.1 Q, u₋) =
      incomingSlabWeightedEvaluation a₋ q.val.1 q.val.2.1 Q := by
  classical
  simp only [map_sum, incomingSlabWeightedEvaluation_def]
  apply Fintype.sum_equiv (leftChamberIncomingRayEquiv K k q c Q)
  intro β
  have ha : -q.val.1 = (q.val.1.natAbs : ℤ) := by omega
  rw [leftChamberExponentMap_single]
  exact congrArg (fun n : ℤ => single (n, q.val.2.1) a₋) ha

/-- The right Laurent embedding preserves the finite sum of whole incoming decorations. -/
theorem rightChamberExponentMap_sum_incoming (hq : 0 ≤ q.val.1) :
    rightChamberExponentMap K k
        (∑ _β : IncomingSlabBrokenLine u₊ q.val.1 q.val.2.1 Q, u₊) =
      incomingSlabWeightedEvaluation a₊ q.val.1 q.val.2.1 Q := by
  classical
  simp only [map_sum, incomingSlabWeightedEvaluation_def]
  apply Fintype.sum_equiv (rightChamberIncomingRayEquiv K k q c Q)
  intro β
  have ha : q.val.1 = (q.val.1.natAbs : ℤ) := by omega
  rw [rightChamberExponentMap_single]
  exact congrArg (fun n : ℤ => single (n, q.val.2.1) a₊) ha

/-- At a left incoming endpoint the proper-ray sum, together with the constant
incoming section in zero spatial degree, is exactly the original chamber monomial.
This includes invariant vertical monomials and monomials killed by truncation. -/
theorem leftChamber_sum_incoming_add_constant (hq : q.val.1 ≤ 0) (hQ : Q.1 < 0) :
    (∑ _β : IncomingSlabBrokenLine u₋ q.val.1 q.val.2.1 Q, u₋) +
        (if (q.val.1, q.val.2.1) = 0 then u₋ else 0) = u₋ := by
  exact incomingSlab_sum_add_constant u₋ q.val.1 q.val.2.1 Q hQ.ne
    (mul_nonneg_of_nonpos_of_nonpos hQ.le (by exact_mod_cast hq))

/-- The analogous right incoming sum includes its stationary sector and gives
the whole original monomial, without a nonzero-coefficient assumption. -/
theorem rightChamber_sum_incoming_add_constant (hq : 0 ≤ q.val.1) (hQ : 0 < Q.1) :
    (∑ _β : IncomingSlabBrokenLine u₊ q.val.1 q.val.2.1 Q, u₊) +
        (if (q.val.1, q.val.2.1) = 0 then u₊ else 0) = u₊ := by
  exact incomingSlab_sum_add_constant u₊ q.val.1 q.val.2.1 Q hQ.ne'
    (mul_nonneg hQ.le (by exact_mod_cast hq))

end Mei.FocusFocus
