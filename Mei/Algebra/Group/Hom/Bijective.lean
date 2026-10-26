/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Hom.Basic

/-!
# Lifting bijectivity through an additive quotient

A function commuting with a surjective additive map is bijective if its induced
function is bijective and it acts by translations on each fiber. The function
itself need not be additive. This allows induction through central extensions,
where a nonlinear operation becomes translation by the central coordinate.
-/

public section

namespace AddMonoidHom

variable {M N : Type*} [AddGroup M] [AddGroup N]

/-- Lift bijectivity from an additive quotient when the function commutes with
translations by the kernel. -/
theorem bijective_of_semiconj_of_add_ker (p : M →+ N) (hp : Function.Surjective p)
    (f : M → M) (g : N → N) (hg : Function.Bijective g)
    (hfg : Function.Semiconj p f g)
    (hadd : ∀ x z, p z = 0 → f (x + z) = f x + z) : Function.Bijective f := by
  constructor
  · intro x y hxy
    have hp' : p x = p y := hg.injective (by rw [← hfg x, ← hfg y, hxy])
    have hz : p (-x + y) = 0 := by simp [hp']
    have he := hadd x (-x + y) hz
    simp only [add_neg_cancel_left] at he
    rw [← hxy] at he
    have hz' : -x + y = 0 := add_left_cancel (he.symm.trans (add_zero (f x)).symm)
    simpa only [add_neg_cancel_left, add_zero] using (congrArg (x + ·) hz').symm
  · intro y
    obtain ⟨w, hw⟩ := hg.surjective (p y)
    obtain ⟨x, rfl⟩ := hp w
    have hz : p (-f x + y) = 0 := by simp [hfg x, hw]
    exact ⟨x + (-f x + y), by rw [hadd x _ hz, add_neg_cancel_left]⟩

end AddMonoidHom
