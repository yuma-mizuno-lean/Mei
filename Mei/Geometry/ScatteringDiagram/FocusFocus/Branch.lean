/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Basic

/-!
# One-crossing branches in the focus-focus plane

The signed horizontal exponent `n` distinguishes incoming powers of `X` (`n < 0`)
from powers of `Y` (`n > 0`). A branch with incoming vertical exponent `b` and
outgoing vertical exponent `c` has directions `(n,b)` and `(n,c)`. For an endpoint
`Q` in the opposite chamber, its unique slab encounter occurs at time `Q.1 / n`
and height `Q.2 - c * Q.1 / n`.

We construct these paths using `FiniteAffineRay.insert`, including branches whose
vertical exponent does not change. They are continuous and proper on the incoming
half-line, have no other slab encounter, and avoid the singular origin precisely
when their crossing height is nonzero. The final formulas give the heights of the
binomial branches of `X^d W^b` and `Y^d W^b`. Varying the incoming exponent also
allows the upper-overlap chart, where it is `b + d`, with the same outgoing branch.
Coefficient propagation is not part of this geometric construction.

The coordinates and branch enumeration follow Gross–Siebert, *An Invitation to
Toric Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open Set

/-- The branch from horizontal exponent `n`, incoming vertical exponent `b`, and
outgoing vertical exponent `c`. The endpoint lies on the outgoing side of the slab.
A zero direction increment retains the slab encounter without introducing a bend. -/
def slabBranch (n b c : ℤ) (Q : ℝ × ℝ) (hQ : Q.1 / (n : ℝ) < 0) :
    FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ) :=
  (FiniteAffineRay.straight Q ((n : ℝ), (c : ℝ))).insert
    (Q.1 / (n : ℝ)) (0, (b : ℝ) - c) hQ

variable (n b c : ℤ) (Q : ℝ × ℝ) (hQ : Q.1 / (n : ℝ) < 0)

/-- The constructed branch ends at the prescribed endpoint. -/
@[simp]
theorem endpoint_slabBranch : (slabBranch n b c Q hQ).endpoint = Q := by
  simp [slabBranch]

/-- The terminal direction is the outgoing monomial exponent. -/
@[simp]
theorem direction_slabBranch :
    (slabBranch n b c Q hQ).direction = ((n : ℝ), (c : ℝ)) := by
  simp [slabBranch]

/-- The only possible bend is at the slab encounter; unchanged exponents give no bend. -/
@[simp]
theorem bends_slabBranch :
    (slabBranch n b c Q hQ).bends =
      Finsupp.single (Q.1 / (n : ℝ)) (0, (b : ℝ) - c) := by
  simp [slabBranch]

/-- The incoming direction is the original monomial exponent. -/
@[simp]
theorem incomingDirection_slabBranch :
    (slabBranch n b c Q hQ).incomingDirection = ((n : ℝ), (b : ℝ)) := by
  simp [slabBranch]

/-- The hinge formula realizes both affine segments, including their common endpoint. -/
theorem slabBranch_apply (t : ℝ) :
    slabBranch n b c Q hQ t =
      (Q.1 - t * n, Q.2 - t * c + max (Q.1 / (n : ℝ) - t) 0 * (b - c)) := by
  apply Prod.ext <;> simp [slabBranch, smul_eq_mul] <;> ring

/-- The terminal segment is determined by the endpoint and outgoing exponent.
In particular it is independent of the incoming chart's vertical exponent. -/
theorem slabBranch_apply_of_ge {t : ℝ} (ht : Q.1 / (n : ℝ) ≤ t) :
    slabBranch n b c Q hQ t = (Q.1 - t * n, Q.2 - t * c) := by
  rw [slabBranch_apply, max_eq_right (sub_nonpos.mpr ht)]
  simp

/-- Before the crossing, the ray has its incoming velocity and the crossing
position determines its affine reference point. -/
theorem slabBranch_apply_of_le {t : ℝ} (ht : t ≤ Q.1 / (n : ℝ)) :
    slabBranch n b c Q hQ t =
      (Q.1 - t * n, Q.2 - t * b + Q.1 / (n : ℝ) * (b - c)) := by
  rw [slabBranch_apply, max_eq_left (sub_nonneg.mpr ht)]
  congr 1
  ring

/-- The horizontal coordinate is strictly affine even when the vertical direction bends. -/
@[simp]
theorem fst_slabBranch (t : ℝ) :
    (slabBranch n b c Q hQ t).1 = Q.1 - t * n := by
  rw [slabBranch_apply]

/-- The branch meets the slab at exactly one parameter, strictly before the endpoint. -/
@[simp↓]
theorem fst_slabBranch_eq_zero_iff (t : ℝ) :
    (slabBranch n b c Q hQ t).1 = 0 ↔ t = Q.1 / (n : ℝ) := by
  rw [fst_slabBranch, sub_eq_zero, eq_div_iff ((div_ne_zero_iff.mp hQ.ne).2)]
  exact eq_comm

/-- The slab encounter has the height determined by backward propagation. -/
@[simp]
theorem slabBranch_crossing :
    slabBranch n b c Q hQ (Q.1 / (n : ℝ)) =
      (0, Q.2 - (c : ℝ) * Q.1 / n) := by
  rw [slabBranch_apply_of_ge n b c Q hQ le_rfl]
  have hn := (div_ne_zero_iff.mp hQ.ne).2
  apply Prod.ext
  · exact sub_eq_zero.mpr (div_mul_cancel₀ _ hn).symm
  · dsimp
    ring

/-- Singular incidence occurs exactly when the unique slab encounter is at height zero. -/
@[simp]
theorem slabBranch_eq_zero_iff (t : ℝ) :
    slabBranch n b c Q hQ t = 0 ↔
      t = Q.1 / (n : ℝ) ∧ Q.2 - (c : ℝ) * Q.1 / n = 0 := by
  constructor
  · intro ht
    have hx := congrArg Prod.fst ht
    have ht' := (fst_slabBranch_eq_zero_iff n b c Q hQ t).mp hx
    refine ⟨ht', ?_⟩
    subst t
    rw [slabBranch_crossing] at ht
    exact congrArg Prod.snd ht
  · rintro ⟨rfl, hs⟩
    rw [slabBranch_crossing, hs]
    rfl

/-- The entire incoming half-line avoids the singularity exactly off the crossing-height
hyperplane. The crossing is in the half-line because the endpoint is in the opposite chamber. -/
@[simp↓]
theorem slabBranch_avoids_origin_iff :
    (∀ t ≤ 0, slabBranch n b c Q hQ t ≠ 0) ↔ Q.2 - (c : ℝ) * Q.1 / n ≠ 0 := by
  constructor
  · intro h hs
    exact h _ hQ.le ((slabBranch_eq_zero_iff n b c Q hQ _).mpr ⟨rfl, hs⟩)
  · intro hs t _ ht
    exact hs ((slabBranch_eq_zero_iff n b c Q hQ t).mp ht).2

/-- Nonzero horizontal velocity makes every closed incoming half-line proper,
including branches with no actual change of direction. -/
theorem isProperMap_slabBranch (a : ℝ) :
    IsProperMap (fun t : Iic a => slabBranch n b c Q hQ t) := by
  apply (slabBranch n b c Q hQ).isProperMap_restrict_Iic _ a
  rw [incomingDirection_slabBranch]
  exact fun he => (div_ne_zero_iff.mp hQ.ne).2 (congrArg Prod.fst he)

/-- A finite affine ray with the specified endpoint and incoming and outgoing
exponents, and with all its bends at one slab encounter, is this branch. Neither
the encounter time nor its height needs to be prescribed. This includes an unbent
ray passing through the slab. -/
theorem slabBranch_unique (β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ)) (s : ℝ)
    (hendpoint : β.endpoint = Q) (hdirection : β.direction = ((n : ℝ), (c : ℝ)))
    (hincoming : β.incomingDirection = ((n : ℝ), (b : ℝ)))
    (hbends : β.bends.support ⊆ {s}) (hslab : (β s).1 = 0) :
    β = slabBranch n b c Q hQ := by
  classical
  have hb := Finsupp.support_subset_singleton.mp hbends
  have hinc : β.bends s = (0, (b : ℝ) - c) := by
    rw [FiniteAffineRay.incomingDirection_def, hb, hdirection] at hincoming
    simp only [Finsupp.sum_single_index] at hincoming
    apply Prod.ext
    · have := congrArg Prod.fst hincoming
      simp only [Prod.fst_add] at this
      linarith
    · have := congrArg Prod.snd hincoming
      simp only [Prod.snd_add] at this
      linarith
  have hcross : β s = (-s • ((n : ℝ), (c : ℝ))) + Q := by
    rw [FiniteAffineRay.eval_def, hb, hendpoint, hdirection]
    simp
  have hs : s = Q.1 / (n : ℝ) := by
    rw [hcross] at hslab
    simp only [Prod.smul_mk, Prod.fst_add, smul_eq_mul, neg_mul] at hslab
    apply (eq_div_iff ((div_ne_zero_iff.mp hQ.ne).2)).mpr
    linarith
  apply FiniteAffineRay.ext
  · simpa only [endpoint_slabBranch] using hendpoint
  · simpa only [direction_slabBranch] using hdirection
  · rw [bends_slabBranch, hb, hinc, hs]

/- For `X^d W^b`, the `j`-th outgoing exponent has crossing height
`v + (b+j)u/d`. The incoming vertical exponent can be changed to use the upper chart. -/
example (d : ℕ) (b₀ b : ℤ) (j : ℕ) (Q : ℝ × ℝ)
    (hQ : Q.1 / ((-(d : ℤ) : ℤ) : ℝ) < 0) :
    slabBranch (-(d : ℤ)) b₀ (b + j) Q hQ (-(Q.1 / (d : ℝ))) =
      (0, Q.2 + ((b : ℝ) + j) * Q.1 / d) := by
  simpa only [Int.cast_neg, Int.cast_natCast, Int.cast_add, div_neg,
    mul_div_assoc, neg_div, sub_neg_eq_add] using
    slabBranch_crossing (-(d : ℤ)) b₀ (b + j) Q hQ

/- For `Y^d W^b`, the `j`-th outgoing exponent has crossing height
`v - (b+j)u/d`, with the opposite horizontal direction from the `X` branches. -/
example (d : ℕ) (b₀ b : ℤ) (j : ℕ) (Q : ℝ × ℝ)
    (hQ : Q.1 / ((d : ℤ) : ℝ) < 0) :
    slabBranch (d : ℤ) b₀ (b + j) Q hQ (Q.1 / (d : ℝ)) =
      (0, Q.2 - ((b : ℝ) + j) * Q.1 / d) := by
  simpa only [Int.cast_natCast, Int.cast_add] using
    slabBranch_crossing (d : ℤ) b₀ (b + j) Q hQ

end Mei.FocusFocus
