/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Polynomial.Laurent
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Decorated
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Incoming.Basic
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Theta

/-!
# Slab lifts of focus-focus broken-line sums

At an endpoint off the slab, sum the actual incoming and crossing fibers and
include the constant incoming section for spatial degree zero. In either chamber,
away from the surviving crossing-height exceptions, this sum is the Laurent
image of the algebraic theta monomial. The two chamber sums therefore have a
unique common lift, namely that theta monomial, even over rings with torsion,
nilpotents or zero divisors. No division by a smoothing parameter or coefficient
is used.

This identifies geometric weighted evaluations with the nodal basis elements;
it does not construct a sheaf of sections or local resolution certificates.
We use the existing decorated-fiber enumeration, incoming-ray classification,
`exponentIncomingLift_single` and `exponentMaps_jointly_injective`.
The slab interpretation follows Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ) (Q : ℝ × ℝ)

/-- The sum of the incoming and crossing decorated-ray fibers, together with
the constant incoming section when both spatial exponents vanish. Normal Laurent
coordinates are positive on the incoming side in either chamber. -/
def slabThetaEvaluation : R[ℤ × ℤ] :=
  incomingSlabWeightedEvaluation c n b Q + slabWeightedEvaluation t c n b Q +
    if (n, b) = 0 then single (0, 0) c else 0

/-- The full evaluation consists of the two ray fibers and the constant sector. -/
theorem slabThetaEvaluation_def :
    slabThetaEvaluation t c n b Q =
      incomingSlabWeightedEvaluation c n b Q + slabWeightedEvaluation t c n b Q +
        if (n, b) = 0 then single (0, 0) c else 0 := (rfl)

/-- Spatial degree zero contributes the constant section, rather than a proper ray. -/
@[simp]
theorem slabThetaEvaluation_zero_zero : slabThetaEvaluation t c 0 0 Q = single (0, 0) c := by
  simp [slabThetaEvaluation]

/-- A zero incoming coefficient has zero evaluation, including the constant sector. -/
@[simp]
theorem slabThetaEvaluation_zero : slabThetaEvaluation t (0 : R) n b Q = 0 := by
  simp [slabThetaEvaluation]

/-- In the incoming chamber the full evaluation is the unchanged incoming monomial,
including invariant vertical monomials and the constant section. -/
@[simp]
theorem slabThetaEvaluation_of_nonneg (hoff : Q.1 ≠ 0)
    (hside : 0 ≤ Q.1 * (n : ℝ)) :
    slabThetaEvaluation t c n b Q = single ((n.natAbs : ℤ), b) c := by
  have hdiv : ¬ Q.1 / (n : ℝ) < 0 :=
    not_lt_of_ge (div_nonneg_iff.mpr (mul_nonneg_iff.mp hside))
  by_cases hv : (n, b) = 0
  · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.mp hv
    simp
  · simp [slabThetaEvaluation, hv, hoff, hside, hdiv]

/-- In the opposite chamber every contribution comes from the crossing fiber. -/
@[simp]
theorem slabThetaEvaluation_of_neg (hside : Q.1 / (n : ℝ) < 0) :
    slabThetaEvaluation t c n b Q = slabWeightedEvaluation t c n b Q := by
  have hmul : ¬ 0 ≤ Q.1 * (n : ℝ) := by
    intro h
    exact (not_lt_of_ge (div_nonneg_iff.mpr (mul_nonneg_iff.mp h))) hside
  have hv : (n, b) ≠ 0 := by
    intro h
    have hn := congrArg Prod.fst h
    simp only [Prod.fst_zero] at hn
    simp [hn] at hside
  simp [slabThetaEvaluation, hmul, hv]

/-- At a generic endpoint in the left chamber, the actual weighted sum is the
left Laurent value of the theta monomial. Only surviving branches impose a
crossing-height exception. The incoming and constant cases need no exceptions. -/
theorem slabThetaEvaluation_eq_exponentLeftMap (hQ : Q.1 < 0)
    (hgeneric : Q.1 / (n : ℝ) < 0 → ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0) :
    slabThetaEvaluation t c n b Q =
      exponentLeftMap (C t * (1 + T 1)) (c • theta t n b) := by
  by_cases hn : n ≤ 0
  · rw [smul_theta_eq_exponentIncomingLift t c n b 0 (by simpa using hn),
      exponentLeftMap_exponentIncomingLift]
    exact slabThetaEvaluation_of_nonneg t c n b Q hQ.ne
      (mul_nonneg_of_nonpos_of_nonpos hQ.le (by exact_mod_cast hn))
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_not_ge hn)
    have hdiv := div_neg_of_neg_of_pos hQ hn'
    rw [slabThetaEvaluation_of_neg t c n b Q hdiv,
      smul_theta_eq_exponentIncomingLift t c n b 1 (by simpa using (le_of_not_ge hn)),
      Mei.LaurentPolynomial.C_mul_one_add_T]
    exact slabWeightedEvaluation_eq_exponentLeftMap_exponentIncomingLift
      t c n b Q hdiv (hgeneric hdiv)

/-- At a generic endpoint in the right chamber, the weighted sum is the right
Laurent value of the same theta monomial. This includes invariant vertical
directions and the constant section. -/
theorem slabThetaEvaluation_eq_exponentRightMap (hQ : 0 < Q.1)
    (hgeneric : Q.1 / (n : ℝ) < 0 → ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0) :
    slabThetaEvaluation t c n b Q =
      exponentRightMap (C t * (1 + T 1)) (c • theta t n b) := by
  by_cases hn : 0 ≤ n
  · rw [smul_theta_eq_exponentIncomingLift t c n b 1 (by simpa using hn),
      exponentRightMap_exponentIncomingLift]
    exact slabThetaEvaluation_of_nonneg t c n b Q hQ.ne'
      (mul_nonneg hQ.le (by exact_mod_cast hn))
  · have hn' : (n : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hn)
    have hdiv := div_neg_of_pos_of_neg hQ hn'
    rw [slabThetaEvaluation_of_neg t c n b Q hdiv,
      smul_theta_eq_exponentIncomingLift t c n b 0 (by simpa using (le_of_not_ge hn)),
      Mei.LaurentPolynomial.C_mul_one_add_T]
    exact slabWeightedEvaluation_eq_exponentRightMap_exponentIncomingLift
      t c n b Q hdiv (hgeneric hdiv)

/-- The two geometric chamber evaluations determine exactly one element of the
slab node: the scalar multiple of its theta basis vector. The two endpoints may
be chosen independently; they need only avoid the surviving branch exceptions.
This is uniqueness of the common algebraic lift, without a sheaf assumption. -/
theorem eq_smul_theta_iff_chamber_values (L U : ℝ × ℝ)
    (hL : L.1 < 0) (hU : 0 < U.1)
    (hgL : L.1 / (n : ℝ) < 0 → ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        L.2 - ((b + j.val : ℤ) : ℝ) * L.1 / n ≠ 0)
    (hgU : U.1 / (n : ℝ) < 0 → ∀ j : Fin (n.natAbs + 1),
      c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0 →
        U.2 - ((b + j.val : ℤ) : ℝ) * U.1 / n ≠ 0)
    (z : TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1))) :
    z = c • theta t n b ↔
      exponentLeftMap (C t * (1 + T 1)) z = slabThetaEvaluation t c n b L ∧
        exponentRightMap (C t * (1 + T 1)) z = slabThetaEvaluation t c n b U := by
  rw [slabThetaEvaluation_eq_exponentLeftMap t c n b L hL hgL,
    slabThetaEvaluation_eq_exponentRightMap t c n b U hU hgU]
  exact ⟨fun h => by simp [h], fun h =>
    exponentMaps_jointly_injective _ (Prod.ext h.1 h.2)⟩

end Mei.FocusFocus
