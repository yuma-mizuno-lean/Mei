/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Chamber
public import Mei.Geometry.Convex.Cone.Chamber

/-!
# Endpoint factors in positive and negative chambers

In the positive chamber the positive BCH factor is the whole group element;
the middle and negative factors are identities. In the negative chamber the
negative factor is the whole element and the others are identities. Thus the
negative-factor quotient from a positive endpoint to a negative endpoint
recovers the original element, both at finite order and in the completion.
These are the endpoint evaluations for reconstruction transport.

The statements combine `AddSubmonoid.positiveChamber` and `negativeChamber`
with the algebraic one-sign formulas in `Mei.Algebra.Lie.BCH.Sign.Chamber`.
No lattice model, finite generation, saturation or spanning assumption is needed.
The interpretation follows Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4
([arXiv:1603.00416](https://arxiv.org/abs/1603.00416)).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N V R L : Type*} [AddCommMonoid N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (d : PositiveDegrees N) (i : N →+ V)
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {θ φ : V →L[ℝ] ℝ} {k : ℕ}

/-- At a positive chamber point the positive finite factor is the whole
element and the other factors are identities. -/
@[simp] theorem signFactorizationEquiv_symm_of_mem_positiveChamber
    (hθ : θ ∈ d.monoid.positiveChamber i) (g : d.truncatedGroup ℒ k) (s : SignType) :
    ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g s :
        d.truncatedGroup ℒ k) = if s = .pos then g else 1 := by
  apply signFactorizationEquiv_symm_of_sign_eq
  intro n hn
  exact sign_pos (((AddSubmonoid.mem_positiveChamber d.monoid i).mp hθ) n
    (d.mem_cutoff.mp hn.1).1 hn.2)

/-- At a negative chamber point the negative finite factor is the whole
element and the other factors are identities. -/
@[simp] theorem signFactorizationEquiv_symm_of_mem_negativeChamber
    (hθ : θ ∈ d.monoid.negativeChamber i) (g : d.truncatedGroup ℒ k) (s : SignType) :
    ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g s :
        d.truncatedGroup ℒ k) = if s = .neg then g else 1 := by
  apply signFactorizationEquiv_symm_of_sign_eq
  intro n hn
  exact sign_neg (((AddSubmonoid.mem_negativeChamber d.monoid i).mp hθ) n
    (d.mem_cutoff.mp hn.1).1 hn.2)

/-- The finite negative-factor quotient from a positive chamber to a
negative chamber is the original group element. -/
theorem signFactorizationEquiv_neg_mul_inv_eq_of_mem_chambers
    (hθ : θ ∈ d.monoid.positiveChamber i) (hφ : φ ∈ d.monoid.negativeChamber i)
    (g : d.truncatedGroup ℒ k) :
    ((signFactorizationEquiv ℒ (φ.toAddMonoidHom.comp i) d k).symm g .neg :
        d.truncatedGroup ℒ k) *
      ((signFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d k).symm g .neg :
        d.truncatedGroup ℒ k)⁻¹ = g := by
  rw [d.signFactorizationEquiv_symm_of_mem_negativeChamber i ℒ hφ,
    d.signFactorizationEquiv_symm_of_mem_positiveChamber i ℒ hθ]
  simp

/-- The positive completed factor at a positive chamber point is the whole
element; both other completed factors are identities. -/
@[simp] theorem completedSignFactorizationEquiv_symm_of_mem_positiveChamber
    (hθ : θ ∈ d.monoid.positiveChamber i) (g : d.completedBCHGroup ℒ) (s : SignType) :
    ((completedSignFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d).symm g s :
        d.completedBCHGroup ℒ) = if s = .pos then g else 1 := by
  apply completedSignFactorizationEquiv_symm_of_sign_eq
  intro n hn hn0
  exact sign_pos (((AddSubmonoid.mem_positiveChamber d.monoid i).mp hθ) n hn hn0)

/-- The negative completed factor at a negative chamber point is the whole
element; both other completed factors are identities. -/
@[simp] theorem completedSignFactorizationEquiv_symm_of_mem_negativeChamber
    (hθ : θ ∈ d.monoid.negativeChamber i) (g : d.completedBCHGroup ℒ) (s : SignType) :
    ((completedSignFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d).symm g s :
        d.completedBCHGroup ℒ) = if s = .neg then g else 1 := by
  apply completedSignFactorizationEquiv_symm_of_sign_eq
  intro n hn hn0
  exact sign_neg (((AddSubmonoid.mem_negativeChamber d.monoid i).mp hθ) n hn hn0)

/-- The completed negative-factor quotient from a positive chamber to a
negative chamber recovers the element being reconstructed. -/
theorem completedSignFactorizationEquiv_neg_mul_inv_eq_of_mem_chambers
    (hθ : θ ∈ d.monoid.positiveChamber i) (hφ : φ ∈ d.monoid.negativeChamber i)
    (g : d.completedBCHGroup ℒ) :
    ((completedSignFactorizationEquiv ℒ (φ.toAddMonoidHom.comp i) d).symm g .neg :
        d.completedBCHGroup ℒ) *
      ((completedSignFactorizationEquiv ℒ (θ.toAddMonoidHom.comp i) d).symm g .neg :
        d.completedBCHGroup ℒ)⁻¹ = g := by
  rw [d.completedSignFactorizationEquiv_symm_of_mem_negativeChamber i ℒ hφ,
    d.completedSignFactorizationEquiv_symm_of_mem_positiveChamber i ℒ hθ]
  simp

end Mei.PositiveDegrees
