/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Sign

/-!
# Computing the sign decomposition

The inverse of TauCeti's sign decomposition adds the three components.
This gives the computation on homogeneous elements and uniqueness from the sum.
-/

public section

open scoped DirectSum

namespace TauCeti

variable {ι R L A : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommMonoid A] [LinearOrder A] [IsOrderedAddMonoid A]
  (ℒ : ι → Submodule R L) [SetLike.GradedBracket ℒ ℒ] [DirectSum.Decomposition ℒ]
  (θ : ι →+ A)

/-- Recombination of sign components is the canonical direct-sum addition map. -/
@[simp]
theorem signDecomposition_symm_apply
    (x : ⨁ s, (signSubalgebra ℒ θ s).toSubmodule) :
    (signDecomposition ℒ θ).symm x = DirectSum.coeLinearMap _ x := by
  have hs := sum_signDecomposition ℒ θ ((signDecomposition ℒ θ).symm x)
  rw [LinearEquiv.apply_symm_apply] at hs
  have hsum := congrArg (DirectSum.coeLinearMap
    (fun s => (signSubalgebra ℒ θ s).toSubmodule)) (DirectSum.sum_univ_of x)
  simp only [map_sum, DirectSum.coeLinearMap_of] at hsum
  exact hs.symm.trans hsum

/-- An element of one sign subalgebra has just that sign component. -/
@[simp]
theorem signDecomposition_coe (s : SignType) (x : signSubalgebra ℒ θ s) :
    signDecomposition ℒ θ x =
      DirectSum.of (fun s => (signSubalgebra ℒ θ s).toSubmodule) s x := by
  apply (signDecomposition ℒ θ).symm.injective
  simp [signDecomposition_symm_apply]

/-- A homogeneous element is recovered in exactly its own sign component. -/
theorem signDecomposition_apply_of_mem {n : ι} {x : L} (hx : x ∈ ℒ n) (s : SignType) :
    (signDecomposition ℒ θ x s : L) =
      if SignType.sign (θ n) = s then x else 0 := by
  have he := signDecomposition_coe ℒ θ (SignType.sign (θ n))
    ⟨x, le_signSubalgebra ℒ θ n hx⟩
  rw [he]
  simp only [DirectSum.coe_of_apply]
  split <;> rfl

/-- The three sign components are uniquely determined by their sum. -/
theorem signDecomposition_eq_iff (x : L)
    (a : ∀ s, signSubalgebra ℒ θ s) :
    (∀ s, signDecomposition ℒ θ x s = a s) ↔ ∑ s, (a s : L) = x := by
  constructor
  · intro ha
    rw [← sum_signDecomposition ℒ θ x]
    exact Finset.sum_congr rfl fun s _ => congrArg Subtype.val (ha s).symm
  · intro ha
    have he : x = ∑ s, (a s : L) := ha.symm
    intro s
    apply Subtype.ext
    rw [he, map_sum]
    simp [signDecomposition_coe, DirectSum.sum_apply, DirectSum.coe_of_apply, apply_ite]

end TauCeti
