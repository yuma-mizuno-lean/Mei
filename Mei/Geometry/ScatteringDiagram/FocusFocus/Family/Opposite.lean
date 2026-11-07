/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family.Theta

/-!
# Fibers of the common focus-focus family in the opposite chamber

Let the horizontal exponent `n` of the theta monomial be nonzero. An endpoint `Q` with
`Q.1 / n < 0` lies strictly in the chamber opposite to the incoming side of the monomial.
No incoming chart and no constant chart of the common family `slabThetaFamily` contains such
an endpoint, so every broken line ending there crosses the slab.

Each surviving binomial index `j`, that is one with `c t^{|n|} binom(|n|, j) ≠ 0`, whose crossing
height at `Q` is nonzero contributes exactly one chart, the upper or the lower one according to
the sign of that height. This identifies the fiber of the common family at `Q` with the surviving
nonsingular binomial indices (`slabThetaFamilyOppositeFiberEquiv`). The whole weight of the
chart of `j` is the homogeneous decoration `c t^{|n|} binom(|n|, j) z^{(-|n|, b + j)}`
(`slabThetaChartWeight_of_opposite`). In particular, the number of broken lines of the common
family ending at `Q` is the number of these indices (`card_slabThetaFamily_fiber_of_opposite`).

These are the broken lines of the focus-focus slab in Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.3 (arXiv:0808.2749v2): the incoming monomial bends once on the slab and its
outgoing terms are the terms of the binomial expansion of the slab function.
-/

public noncomputable section

open AddMonoidAlgebra

namespace Mei.FocusFocus

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ) {Q : ℝ × ℝ}

/-- An endpoint of the chamber opposite to the incoming side of the monomial lies in no
incoming chart. -/
theorem notMem_incomingSlabDomain_of_div_neg (hQ : Q.1 / (n : ℝ) < 0)
    (α : IncomingSlabChartIndex c n b) : Q ∉ incomingSlabDomain α.val := by
  obtain ⟨right, -, -, hside⟩ := α
  rw [mem_incomingSlabDomain]
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at hside ⊢
    exact fun hQ₁ => hQ.not_ge (div_nonneg_of_nonpos hQ₁.le (by exact_mod_cast hside))
  · simp only [↓reduceIte] at hside ⊢
    exact fun hQ₁ => hQ.not_ge (div_nonneg hQ₁.le (by exact_mod_cast hside))

/-- An endpoint of the opposite chamber lies in no chart of the constant sector, since that
sector requires the spatial exponent to vanish. -/
theorem notMem_slabThetaChartDomain_constant_of_div_neg (hQ : Q.1 / (n : ℝ) < 0) (u : Unit) :
    Q ∉ slabThetaChartDomain t c n b (.inr (.inr u)) := by
  rw [mem_slabThetaChartDomain_constant]
  rintro ⟨hnb, -⟩
  have hn : n = 0 := congrArg Prod.fst hnb
  simp [hn] at hQ

/-- In the opposite chamber, the charts of the common family containing `Q` are exactly the
crossing charts containing `Q`, with the same labels. -/
def slabThetaOppositeChartEquiv (hQ : Q.1 / (n : ℝ) < 0) :
    {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α} ≃
      {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2} where
  toFun
    | ⟨.inl α, hα⟩ => (notMem_incomingSlabDomain_of_div_neg c n b hQ α
        (by simpa only [slabThetaChartDomain_incoming] using hα)).elim
    | ⟨.inr (.inl α), hα⟩ => ⟨α, by simpa only [slabThetaChartDomain_crossing] using hα⟩
    | ⟨.inr (.inr u), hα⟩ =>
      (notMem_slabThetaChartDomain_constant_of_div_neg t c n b hQ u hα).elim
  invFun α := ⟨.inr (.inl α.val), by simpa only [slabThetaChartDomain_crossing] using α.property⟩
  left_inv
    | ⟨.inl α, hα⟩ => (notMem_incomingSlabDomain_of_div_neg c n b hQ α
        (by simpa only [slabThetaChartDomain_incoming] using hα)).elim
    | ⟨.inr (.inl _), _⟩ => rfl
    | ⟨.inr (.inr u), hα⟩ =>
      (notMem_slabThetaChartDomain_constant_of_div_neg t c n b hQ u hα).elim
  right_inv _ := rfl

/-- The inverse opposite-chamber chart comparison is the inclusion of crossing charts. -/
@[simp]
theorem slabThetaOppositeChartEquiv_symm_apply_val (hQ : Q.1 / (n : ℝ) < 0)
    (α : {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2}) :
    ((slabThetaOppositeChartEquiv t c n b hQ).symm α).val = .inr (.inl α.val) := (rfl)

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- **Opposite-chamber fibers.** At an endpoint of the chamber opposite to the incoming side,
the broken lines of the common focus-focus family correspond to the surviving binomial indices
with nonzero crossing height. -/
def slabThetaFamilyOppositeFiberEquiv (hQ : Q.1 / (n : ℝ) < 0) :
    (slabThetaFamily t c n b h).fiber Q ≃ SlabBranchIndex t c n b Q :=
  (slabThetaFamilyChartFiberEquiv t c n b h Q).symm.trans
    ((slabThetaOppositeChartEquiv t c n b hQ).trans (slabChartIndexEquiv t c n b Q hQ))

/-- The broken line of a surviving binomial index `j` is the crossing chart of `j`, on the upper
side exactly when the crossing height is positive. -/
@[simp]
theorem slabThetaFamilyOppositeFiberEquiv_symm_fst (hQ : Q.1 / (n : ℝ) < 0)
    (j : SlabBranchIndex t c n b Q) :
    ((slabThetaFamilyOppositeFiberEquiv t c n b h hQ).symm j).1 =
      .inr (.inl (⟨j.val, j.property.1⟩,
        decide (0 < Q.2 - ((b + j.val.val : ℤ) : ℝ) * Q.1 / n))) := by
  simp [slabThetaFamilyOppositeFiberEquiv]

/-- In the opposite chamber, the chart label of a broken line is the crossing chart of its
binomial index under `slabThetaFamilyOppositeFiberEquiv`. -/
theorem slabThetaFamily_fiber_fst_of_opposite (hQ : Q.1 / (n : ℝ) < 0)
    (z : (slabThetaFamily t c n b h).fiber Q) :
    z.1 = .inr (.inl (⟨(slabThetaFamilyOppositeFiberEquiv t c n b h hQ z).val,
      (slabThetaFamilyOppositeFiberEquiv t c n b h hQ z).property.1⟩,
        decide (0 < Q.2 - ((b + (slabThetaFamilyOppositeFiberEquiv t c n b h hQ z).val.val :
          ℤ) : ℝ) * Q.1 / n))) := by
  conv_lhs => rw [← (slabThetaFamilyOppositeFiberEquiv t c n b h hQ).symm_apply_apply z]
  rw [slabThetaFamilyOppositeFiberEquiv_symm_fst]

/-- In the opposite chamber, the whole weight of the broken line of the binomial index `j` is
the decoration `c t^{|n|} binom(|n|, j) z^{(-|n|, b + j)}`. -/
theorem slabThetaChartWeight_of_opposite (hQ : Q.1 / (n : ℝ) < 0)
    (z : (slabThetaFamily t c n b h).fiber Q) :
    slabThetaChartWeight t c n b z.1 =
      single (-(n.natAbs : ℤ), b + (slabThetaFamilyOppositeFiberEquiv t c n b h hQ z).val.val)
        (c * t ^ n.natAbs *
          (n.natAbs.choose (slabThetaFamilyOppositeFiberEquiv t c n b h hQ z).val.val : R)) := by
  rw [slabThetaFamily_fiber_fst_of_opposite t c n b h hQ z, slabThetaChartWeight_crossing]

/-- The number of broken lines of the common family ending in the opposite chamber is the
number of surviving binomial indices with nonzero crossing height. -/
theorem card_slabThetaFamily_fiber_of_opposite (hQ : Q.1 / (n : ℝ) < 0) :
    Nat.card ((slabThetaFamily t c n b h).fiber Q) = Nat.card (SlabBranchIndex t c n b Q) :=
  Nat.card_congr (slabThetaFamilyOppositeFiberEquiv t c n b h hQ)

end Mei.FocusFocus
