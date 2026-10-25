/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Group.AddSubmonoid.Degree
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Strict dual chambers of additive monoids

The positive chamber consists of continuous real functionals strictly positive on every
nonzero element of an additive monoid mapped into a real normed space. The negative chamber
is defined by strict negativity. Both are convex and avoid all the degree hyperplanes.
For a finitely generated monoid, positivity can be tested on its nonzero generators, so
both chambers are open. Neither the construction nor openness requires finite dimension,
injectivity of the monoid map, or a saturated monoid.

The finite test uses additive closure induction; the topological and convexity arguments
use Mathlib's continuous evaluation map and convex half-spaces.
-/

public section

open Set

namespace AddSubmonoid

variable {M V : Type*} [AddCommMonoid M] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (P : AddSubmonoid M) (i : M →+ V)

/-- Real functionals strictly positive on all nonzero elements of the given monoid. -/
def positiveChamber : Set (V →L[ℝ] ℝ) :=
  {θ | ∀ n ∈ P, n ≠ 0 → 0 < θ (i n)}

/-- Real functionals strictly negative on all nonzero elements of the given monoid. -/
def negativeChamber : Set (V →L[ℝ] ℝ) :=
  {θ | ∀ n ∈ P, n ≠ 0 → θ (i n) < 0}

/-- Membership in the positive chamber is strict positivity on the nonzero monoid. -/
@[simp]
theorem mem_positiveChamber {θ : V →L[ℝ] ℝ} :
    θ ∈ P.positiveChamber i ↔ ∀ n ∈ P, n ≠ 0 → 0 < θ (i n) := Iff.rfl

/-- Membership in the negative chamber is strict negativity on the nonzero monoid. -/
@[simp]
theorem mem_negativeChamber {θ : V →L[ℝ] ℝ} :
    θ ∈ P.negativeChamber i ↔ ∀ n ∈ P, n ≠ 0 → θ (i n) < 0 := Iff.rfl

/-- The negative chamber is the inverse image of the positive chamber under negation. -/
theorem negativeChamber_eq_preimage_neg :
    P.negativeChamber i = Neg.neg ⁻¹' P.positiveChamber i := by
  ext θ
  simp

/-- On a generated monoid, chamber membership is a test on the nonzero generators. -/
theorem mem_positiveChamber_iff_of_closure_eq {s : Set M} (hs : closure s = P)
    {θ : V →L[ℝ] ℝ} :
    θ ∈ P.positiveChamber i ↔ ∀ n ∈ s, n ≠ 0 → 0 < θ (i n) :=
  forall_pos_iff_of_closure_eq hs (θ.toLinearMap.toAddMonoidHom.comp i)

/-- Strict dual chambers are convex, without finite generation. -/
theorem convex_positiveChamber : Convex ℝ (P.positiveChamber i) := by
  have heq : P.positiveChamber i =
      ⋂ n : {n : M // n ∈ P ∧ n ≠ 0}, {θ : V →L[ℝ] ℝ | 0 < θ (i n)} := by
    ext θ
    simp
  rw [heq]
  exact convex_iInter fun n => convex_halfSpace_gt
    (ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap.isLinear 0

/-- The negative strict dual chamber is convex. -/
theorem convex_negativeChamber : Convex ℝ (P.negativeChamber i) := by
  rw [negativeChamber_eq_preimage_neg]
  exact (P.convex_positiveChamber i).linear_preimage (-(LinearMap.id :
    (V →L[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ)))

/-- Finite generation makes the positive chamber open in the normed dual. -/
theorem isOpen_positiveChamber (hP : P.FG) : IsOpen (P.positiveChamber i) := by
  classical
  obtain ⟨s, hs⟩ := AddSubmonoid.isAddFG_iff.mp hP
  have heq : P.positiveChamber i =
      ⋂ n : s.erase 0, {θ : V →L[ℝ] ℝ | 0 < θ (i n)} := by
    ext θ
    rw [P.mem_positiveChamber_iff_of_closure_eq i hs]
    simp only [mem_iInter, Subtype.forall, Finset.mem_coe, Finset.mem_erase]
    grind
  rw [heq]
  exact isOpen_iInter_of_finite fun n =>
    isOpen_lt continuous_const (ContinuousLinearMap.apply ℝ ℝ (i n)).continuous

/-- Finite generation makes the negative chamber open in the normed dual. -/
theorem isOpen_negativeChamber (hP : P.FG) : IsOpen (P.negativeChamber i) := by
  rw [negativeChamber_eq_preimage_neg]
  exact (P.isOpen_positiveChamber i hP).preimage continuous_neg

/-- A positive chamber point avoids every hyperplane of a nonzero monoid element. -/
theorem apply_ne_zero_of_mem_positiveChamber {θ : V →L[ℝ] ℝ}
    (hθ : θ ∈ P.positiveChamber i) {n : M} (hn : n ∈ P) (hn0 : n ≠ 0) :
    θ (i n) ≠ 0 := (hθ n hn hn0).ne'

/-- A negative chamber point avoids every hyperplane of a nonzero monoid element. -/
theorem apply_ne_zero_of_mem_negativeChamber {θ : V →L[ℝ] ℝ}
    (hθ : θ ∈ P.negativeChamber i) {n : M} (hn : n ∈ P) (hn0 : n ≠ 0) :
    θ (i n) ≠ 0 := (hθ n hn hn0).ne

end AddSubmonoid
