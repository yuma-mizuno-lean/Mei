/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Completion
public import Mei.Algebra.Lie.Graded.Sign.Chamber

/-!
# Sign factorization in uniform-sign chambers

If a character has one sign on every nonzero retained homogeneous piece,
its factorization has the original element in that sign and identity factors
in the other signs. This follows from uniqueness of sign factorization.
The analogous formula holds in the completed group when all nonzero allowed
degrees have the prescribed sign, via
`projection_completedSignFactorizationEquiv_symm`. This evaluates factorization
at the two ends of positive-to-negative chamber transport, without a
finite-generation hypothesis on the positive monoid; see Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4
([arXiv:1603.00416](https://arxiv.org/abs/1603.00416)).
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

/-- If all nonzero allowed degrees have one sign, the completed factorization
is concentrated in that sign. -/
theorem completedSignFactorizationEquiv_symm_of_uniformSign (s : SignType)
    (hs : ∀ n ∈ d.monoid, n ≠ 0 → SignType.sign (θ n) = s)
    (g : d.completedBCHGroup ℒ) (t : SignType) :
    ((completedSignFactorizationEquiv ℒ θ d).symm g t : d.completedBCHGroup ℒ) =
      if t = s then g else 1 := by
  have hk (k : ℕ) : ∀ n, d.truncatedGrading ℒ k n ≠ ⊥ → SignType.sign (θ n) = s := by
    intro n hn
    have hc := d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hn
    exact hs n (d.mem_cutoff.mp hc.1).1 hc.2
  split_ifs with hts
  · apply CompletedGroup.ext
    intro k
    rw [projection_completedSignFactorizationEquiv_symm]
    exact (d.signFactorizationEquiv_symm_of_uniformSign ℒ θ s (hk k) _ t).trans
      (ite_eq_left hts)
  · apply CompletedGroup.ext
    intro k
    rw [map_one, projection_completedSignFactorizationEquiv_symm]
    exact (d.signFactorizationEquiv_symm_of_uniformSign ℒ θ s (hk k) _ t).trans
      (ite_eq_right hts)

end Mei.PositiveDegrees
