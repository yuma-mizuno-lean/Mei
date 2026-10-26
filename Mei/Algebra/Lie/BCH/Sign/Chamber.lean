/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Completion

/-!
# Sign factors when all degrees have one sign

If a character has the same sign on every retained nonzero degree, the
corresponding factor of any truncated BCH element is the whole element and
the other factors are identities. The analogous formula holds in the
completed group when all positive degrees have the prescribed sign. This
evaluates factorization at the two ends of positive-to-negative chamber
transport, without a finite-generation hypothesis on the positive monoid.

We use `signFactorizationEquiv_symm_of_mem` for uniqueness and
`projection_completedSignFactorizationEquiv_symm` to pass to the completion.
The chamber interpretation follows Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4
([arXiv:1603.00416](https://arxiv.org/abs/1603.00416)).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] (θ : N →+ A)
  (d : PositiveDegrees N) [IsPositiveGrading d ℒ]

/-- A character of constant sign on retained degrees places the whole
truncated group in that sign subgroup. Only the chosen cutoff is tested. -/
theorem signFactorizationEquiv_symm_of_sign_eq (k : ℕ) (t : SignType)
    (hθ : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (θ n) = t)
    (g : d.truncatedGroup ℒ k) (s : SignType) :
    ((signFactorizationEquiv ℒ θ d k).symm g s : d.truncatedGroup ℒ k) =
      if s = t then g else 1 := by
  apply signFactorizationEquiv_symm_of_mem
  rw [LieSubalgebra.mem_bchSubgroup, mem_signSubalgebra_iff]
  intro n hn
  by_cases hzero : d.truncatedGrading ℒ k n = ⊥
  · simpa only [hzero, Submodule.mem_bot] using
      (DirectSum.decompose (d.truncatedGrading ℒ k) (BCHGroup.log g) n).property
  · exact (hn (hθ n (d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hzero))).elim

/-- If all allowed nonzero degrees have one sign, the completed factorization
is concentrated in that sign. -/
theorem completedSignFactorizationEquiv_symm_of_sign_eq (t : SignType)
    (hθ : ∀ n ∈ d.monoid, n ≠ 0 → SignType.sign (θ n) = t)
    (g : d.completedBCHGroup ℒ) (s : SignType) :
    ((completedSignFactorizationEquiv ℒ θ d).symm g s : d.completedBCHGroup ℒ) =
      if s = t then g else 1 := by
  split_ifs with hst
  · apply CompletedGroup.ext
    intro k
    rw [projection_completedSignFactorizationEquiv_symm]
    exact (signFactorizationEquiv_symm_of_sign_eq ℒ θ d k t
      (fun n hn => hθ n (d.mem_cutoff.mp hn.1).1 hn.2) _ s).trans (ite_eq_left hst)
  · apply CompletedGroup.ext
    intro k
    rw [map_one, projection_completedSignFactorizationEquiv_symm]
    exact (signFactorizationEquiv_symm_of_sign_eq ℒ θ d k t
      (fun n hn => hθ n (d.mem_cutoff.mp hn.1).1 hn.2) _ s).trans (ite_eq_right hst)

end Mei.PositiveDegrees
