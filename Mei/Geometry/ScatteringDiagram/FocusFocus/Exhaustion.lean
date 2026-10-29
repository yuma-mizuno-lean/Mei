/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Branch
public import Mei.Geometry.Affine.FiniteRay.Hyperplane

/-!
# Exhaustion of the focus-focus slab branches

In one developed chart, crossing the focus-focus slab preserves the horizontal
exponent. A finite ray whose bends lie on the slab therefore has constant
horizontal velocity and meets the slab at most once. We derive this bound from
the bend conditions, rather than requiring a one-crossing itinerary.

For endpoints in the opposite chamber, the ray is the existing `slabBranch` with
its prescribed incoming and outgoing exponents. In the incoming chamber it is
straight. Classification reduces singular avoidance to the existing crossing-height
test and includes unchanged decorations. Rays of zero horizontal velocity with endpoints
off the slab are also straight. These statements concern geometry; coefficient
propagation and chart identifications are additional conditions.

We use `FiniteAffineRay.support_bends_subset_singleton` and
`FocusFocus.slabBranch_unique`. The one-crossing description follows
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

variable (β : FiniteAffineRay (ℝ × ℝ) (ℝ × ℝ))
  (hvertical : ∀ t ∈ β.bends.support, (β.bends t).1 = 0)
  (hslab : ∀ t ∈ β.bends.support, (β t).1 = 0)

include hvertical hslab

/-- Every transverse slab ray in the opposite chamber is one of the constructed
branches. Only the local bend conditions are assumed; the number and times of
encounters are consequences. -/
theorem eq_slabBranch (n b c : ℤ) (Q : ℝ × ℝ) (hQ : Q.1 / (n : ℝ) < 0)
    (hendpoint : β.endpoint = Q) (hdirection : β.direction = ((n : ℝ), (c : ℝ)))
    (hincoming : β.incomingDirection = ((n : ℝ), (b : ℝ))) :
    β = slabBranch n b c Q hQ := by
  have hn : (n : ℝ) ≠ 0 := (div_ne_zero_iff.mp hQ.ne).2
  have hs : (↑β.bends.support : Set ℝ) ⊆ {Q.1 / (n : ℝ)} := by
    simpa only [AffineMap.coe_fst, AffineMap.fst_linear, LinearMap.fst_apply,
      hendpoint, hdirection, sub_zero] using
      β.support_bends_subset_singleton (AffineMap.fst : (ℝ × ℝ) →ᵃ[ℝ] ℝ)
        hvertical (by simpa [hdirection] using hn) 0 hslab
  apply slabBranch_unique n b c Q hQ β (Q.1 / (n : ℝ))
    hendpoint hdirection hincoming (by simpa only [← Finset.coe_singleton,
      Finset.coe_subset] using hs)
  simpa [hendpoint, hdirection, hn] using
    β.apply_eq_sub_mul (AffineMap.fst : (ℝ × ℝ) →ᵃ[ℝ] ℝ) hvertical (Q.1 / (n : ℝ))

end Mei.FocusFocus
