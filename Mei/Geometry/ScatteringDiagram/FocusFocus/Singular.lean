/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family

/-!
# Local resolutions at singular slab encounters

At an endpoint whose `j`-th binomial branch passes through the singular origin,
a small vertical transverse interval has two complete resolutions by decorated
slab rays. Only branch `j` changes its upper/lower encounter chart. Pairing rays
by their binomial index preserves their whole homogeneous decorations, so the
two weighted evaluations agree over arbitrary commutative coefficient rings.
The closed chart paths on both sides have their limiting encounter at the origin.

The construction uses `slabBrokenLineEquiv`, `slabBranchDomain` and the continuous
closed paths `slabBranchPath`. The local resolution interpretation follows
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

variable {n b : ℤ} {Q : ℝ × ℝ} {j : ℕ}

private theorem singular_height (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    (s : ℝ) (l : ℕ) :
    Q.2 + s - ((b + l : ℤ) : ℝ) * Q.1 / n =
      s + ((j : ℝ) - l) * (Q.1 / (n : ℝ)) := by
  push_cast at hj ⊢
  linear_combination hj

/-- On a sufficiently short transverse interval through the `j`-th singular-height
hyperplane, precisely the `j`-th branch changes its encounter sign. The interval
works for every binomial index and is independent of all coefficients. -/
theorem slabSingular_height_sign (hQ : Q.1 / (n : ℝ) < 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    {s : ℝ} (hs : |s| < -(Q.1 / (n : ℝ))) (l : ℕ) :
    (0 < Q.2 + s - ((b + l : ℤ) : ℝ) * Q.1 / n ↔ j < l ∨ (l = j ∧ 0 < s)) ∧
      (Q.2 + s - ((b + l : ℤ) : ℝ) * Q.1 / n < 0 ↔ l < j ∨ (l = j ∧ s < 0)) := by
  rw [singular_height hj]
  have hs₁ : s < -(Q.1 / (n : ℝ)) := lt_of_le_of_lt (le_abs_self s) hs
  have hs₂ : Q.1 / (n : ℝ) < s := by
    have := neg_le_abs s
    linarith
  rcases lt_trichotomy l j with hl | rfl | hl
  · have hd : (1 : ℝ) ≤ (j : ℝ) - l := by
      have : (l : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : l + 1 ≤ j)
      linarith
    have hm := mul_le_mul_of_nonpos_right hd hQ.le
    constructor <;> constructor <;> intro h <;> first
      | omega
      | nlinarith
  · simp
  · have hd : (j : ℝ) - l ≤ -1 := by
      have : (j : ℝ) + 1 ≤ l := by exact_mod_cast (by omega : j + 1 ≤ l)
      linarith
    have hm := mul_le_mul_of_nonpos_right hd hQ.le
    constructor <;> constructor <;> intro h <;> first
      | omega
      | nlinarith

private theorem singular_height_ne_zero (hQ : Q.1 / (n : ℝ) < 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    {s : ℝ} (hs : |s| < -(Q.1 / (n : ℝ))) (hs₀ : s ≠ 0) (l : ℕ) :
    Q.2 + s - ((b + l : ℤ) : ℝ) * Q.1 / n ≠ 0 := by
  have h := slabSingular_height_sign hQ hj hs l
  rcases lt_trichotomy l j with hl | rfl | hl
  · exact ((h.2).mpr (Or.inl hl)).ne
  · simpa only [singular_height hj, sub_self, zero_mul, add_zero] using hs₀
  · exact ((h.1).mpr (Or.inl hl)).ne'

/-- The chart of every nearby branch is determined by its index and the side of
the transverse interval. Thus other branches retain their chart, even when their
endpoint domains overlap. -/
theorem mem_slabBranchDomain_singular (hQ : Q.1 / (n : ℝ) < 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    {s : ℝ} (hs : |s| < -(Q.1 / (n : ℝ))) (l : ℕ) (upper : Bool) :
    (Q.1, Q.2 + s) ∈ slabBranchDomain n (b + l) upper ↔
      if upper then j < l ∨ (l = j ∧ 0 < s) else l < j ∨ (l = j ∧ s < 0) := by
  rw [mem_slabBranchDomain]
  simp only [hQ, true_and]
  cases upper
  · exact (slabSingular_height_sign hQ hj hs l).2
  · exact (slabSingular_height_sign hQ hj hs l).1

section Coefficients

variable {R : Type*} [CommRing R] (t c : R)
  (hQ : Q.1 / (n : ℝ) < 0)
  (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
  {s : ℝ} (hs₀ : 0 < s) (hs : s < -(Q.1 / (n : ℝ)))

/-- Pair all actual decorated rays on opposite sides of a singular-height event
by their binomial index. The singular branch is replaced by its other encounter
chart; zero decorations are omitted from both fibers. -/
def slabSingularResolutionEquiv :
    SlabBrokenLine t c n b (Q.1, Q.2 - s) ≃
      SlabBrokenLine t c n b (Q.1, Q.2 + s) := by
  let e : SlabBranchIndex t c n b (Q.1, Q.2 - s) ≃
      SlabBranchIndex t c n b (Q.1, Q.2 + s) :=
    Equiv.subtypeEquivRight fun l => by
      have hm := singular_height_ne_zero hQ hj (s := -s)
        (by simpa only [abs_neg, abs_of_pos hs₀] using hs) (neg_ne_zero.mpr hs₀.ne') l.val
      have hp := singular_height_ne_zero hQ hj (s := s)
        (by simpa only [abs_of_pos hs₀] using hs) hs₀.ne' l.val
      exact and_congr_right fun _ => iff_of_true (by simpa only [sub_eq_add_neg] using hm) hp
  exact ((slabBrokenLineEquiv t c n b (Q.1, Q.2 - s) hQ).symm.trans e).trans
    (slabBrokenLineEquiv t c n b (Q.1, Q.2 + s) hQ)

/-- The local resolution pairing preserves the whole outgoing degree. -/
@[simp]
theorem degree_slabSingularResolutionEquiv
    (β : SlabBrokenLine t c n b (Q.1, Q.2 - s)) :
    (slabSingularResolutionEquiv t c hQ hj hs₀ hs β).degree = β.degree := by
  have he := congrArg SlabBrokenLine.degree
    ((slabBrokenLineEquiv t c n b (Q.1, Q.2 - s) hQ).apply_symm_apply β)
  simpa only [slabSingularResolutionEquiv, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply, slabBrokenLineEquiv_apply, degree_slabBrokenLine] using he

/-- Equality with a paired ray is characterized by its degree, without unfolding
the finite enumeration or either geometric realization. -/
theorem slabSingularResolutionEquiv_apply_eq_iff
    (β : SlabBrokenLine t c n b (Q.1, Q.2 - s))
    (γ : SlabBrokenLine t c n b (Q.1, Q.2 + s)) :
    slabSingularResolutionEquiv t c hQ hj hs₀ hs β = γ ↔ β.degree = γ.degree := by
  constructor
  · intro he
    simpa only [degree_slabSingularResolutionEquiv] using congrArg SlabBrokenLine.degree he
  · intro he
    apply SlabBrokenLine.ext
    simpa only [degree_slabSingularResolutionEquiv] using he

/-- The inverse resolution pairing also preserves the outgoing degree. -/
@[simp]
theorem degree_slabSingularResolutionEquiv_symm
    (γ : SlabBrokenLine t c n b (Q.1, Q.2 + s)) :
    ((slabSingularResolutionEquiv t c hQ hj hs₀ hs).symm γ).degree = γ.degree := by
  simpa only [Equiv.apply_symm_apply] using
    (degree_slabSingularResolutionEquiv t c hQ hj hs₀ hs
      ((slabSingularResolutionEquiv t c hQ hj hs₀ hs).symm γ)).symm

/-- Pairing the local resolutions preserves entire homogeneous decorations,
including their binomial multiplicities. -/
@[simp]
theorem decoration_slabSingularResolutionEquiv
    (β : SlabBrokenLine t c n b (Q.1, Q.2 - s)) :
    (slabSingularResolutionEquiv t c hQ hj hs₀ hs β).decoration = β.decoration := by
  rw [SlabBrokenLine.decoration_def, SlabBrokenLine.decoration_def,
    degree_slabSingularResolutionEquiv t c hQ hj hs₀ hs]

include hQ hj hs₀ hs in
/-- Both exhaustive nearby resolutions have the same weighted evaluation.
This holds for every incoming coefficient, so also after precomposition with
any linear map from a module of incoming parameters. -/
theorem slabWeightedEvaluation_singular_resolution :
    slabWeightedEvaluation t c n b (Q.1, Q.2 - s) =
      slabWeightedEvaluation t c n b (Q.1, Q.2 + s) := by
  rw [slabWeightedEvaluation_def, slabWeightedEvaluation_def]
  exact Fintype.sum_equiv (slabSingularResolutionEquiv t c hQ hj hs₀ hs) _ _
    (fun β => (decoration_slabSingularResolutionEquiv t c hQ hj hs₀ hs β).symm)

end Coefficients

/-- Both closed encounter charts of the singular branch meet the origin at the
same affine crossing time. The incoming developed directions may differ. -/
theorem slabBranchPath_singular_crossing (hn : n ≠ 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0) (b₀ : ℤ) :
    slabBranchPath n b₀ (b + j) Q (Q.1 / (n : ℝ)) = 0 := by
  rw [slabBranchPath_crossing hn, hj]
  rfl

end Mei.FocusFocus
