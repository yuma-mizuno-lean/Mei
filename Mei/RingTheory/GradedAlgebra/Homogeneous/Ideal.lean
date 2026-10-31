/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Powers of homogeneous ideals

Homogeneous ideals remain homogeneous under powers. Consequently homogeneous
projection preserves every term of their adic filtration. This extends Mathlib's
`Ideal.IsHomogeneous.mul` to natural powers.
-/

public section

namespace Ideal.IsHomogeneous

variable {A ι σ : Type*} [CommSemiring A] [DecidableEq ι] [AddMonoid ι]
  [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]
  {I : Ideal A}

/-- Every natural power of a homogeneous ideal is homogeneous. -/
theorem pow (hI : I.IsHomogeneous 𝒜) (n : ℕ) : (I ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero => simpa only [pow_zero, Ideal.one_eq_top] using Ideal.IsHomogeneous.top 𝒜
  | succ n ih => simpa only [pow_succ] using ih.mul hI

end Ideal.IsHomogeneous
