/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Basic
public import Mei.Algebra.Lie.Graded.Sign.Chamber

/-!
# Sign factorization in uniform-sign chambers

If a character has one sign on every nonzero retained homogeneous piece,
its factorization has the original element in that sign and identity factors
in the other signs. This follows from uniqueness of sign factorization.
It suffices that all nonzero allowed degrees have the prescribed sign, since
every retained homogeneous piece lies in such a degree.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] (θ : N →+ A) {k : ℕ}

/-- In a uniform-sign chamber the unique factor of that sign is the original
BCH element; the other two factors are identities. -/
theorem signFactorizationEquiv_symm_of_uniformSign (s : SignType)
    (hs : ∀ n, d.truncatedGrading ℒ k n ≠ ⊥ → SignType.sign (θ n) = s)
    (g : d.truncatedGroup ℒ k) (t : SignType) :
    ((signFactorizationEquiv ℒ θ d k).symm g t : d.truncatedGroup ℒ k) =
      if t = s then g else 1 := by
  have hg : g ∈ (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup := by
    rw [signSubalgebra_eq_top_of_sign_eq _ _ s hs, LieSubalgebra.mem_bchSubgroup]
    exact LieSubalgebra.mem_top _
  let a : ∀ t, (signSubalgebra (d.truncatedGrading ℒ k) θ t).bchSubgroup :=
    fun t => if ht : t = s then ⟨g, by simpa only [ht] using hg⟩ else 1
  have ha : (signFactorizationEquiv ℒ θ d k).symm g = a := by
    apply (signFactorizationEquiv ℒ θ d k).symm_apply_eq.mpr
    cases s <;> simp [signFactorizationEquiv_apply, a]
  rw [ha]
  by_cases ht : t = s <;> simp [a, ht]

/-- If all nonzero allowed degrees have one sign, the factorization at every
cutoff is concentrated in that sign. -/
theorem signFactorizationEquiv_symm_of_uniformSign_monoid (s : SignType)
    (hs : ∀ n ∈ d.monoid, n ≠ 0 → SignType.sign (θ n) = s)
    (g : d.truncatedGroup ℒ k) (t : SignType) :
    ((signFactorizationEquiv ℒ θ d k).symm g t : d.truncatedGroup ℒ k) =
      if t = s then g else 1 := by
  apply signFactorizationEquiv_symm_of_uniformSign
  intro n hn
  have hc := d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hn
  exact hs n (d.mem_cutoff.mp hc.1).1 hc.2

end Mei.PositiveDegrees
