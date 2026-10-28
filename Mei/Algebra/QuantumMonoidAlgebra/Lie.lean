/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Basic
public import Mei.Algebra.Lie.Graded.Supported
public import Mei.Algebra.Lie.Graded.Subalgebra

/-!
# The positive quantum Lie algebra

The commutator of the quantum algebra respects its exponent decomposition.
Selecting the nonzero allowed degrees gives an internally and positively graded
Lie algebra, ready for nilpotent truncation and completed BCH groups.

We use `supportedLieSubalgebra` and `LieSubalgebra.gradedLieAlgebra` to retain the
existing quantum homogeneous pieces. The quantum commutator convention is that
of Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Example 2.1(iii).

As for other associative algebras, consumers working with the ambient quantum
Lie algebra should install `LieRing.ofAssociativeRing` locally.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- The quantum exponent decomposition is also a Lie grading for the commutator. -/
instance instGradedBracketGrade : SetLike.GradedBracket (grade q β) (grade q β) where
  bracket_mem := by
    intro n n' x y hx hy
    rw [Ring.lie_def]
    exact (grade q β (n + n')).sub_mem (SetLike.mul_mem_graded hx hy)
      (add_comm n' n ▸ SetLike.mul_mem_graded hy hx)

/-- The quantum exponent decomposition is internal as a Lie grading. -/
instance instGradedLieAlgebraGrade [DecidableEq Γ] : GradedLieAlgebra (grade q β) where
  toGradedBracket := inferInstance

/-- The quantum Lie algebra supported on the nonzero positive degrees. -/
def positiveLieAlgebra (d : PositiveDegrees Γ) : LieSubalgebra R (QuantumMonoidAlgebra q β) :=
  supportedLieSubalgebra (grade q β)
    { carrier := {n | n ∈ d.monoid ∧ n ≠ 0}
      add_mem' := by
        rintro n n' ⟨hn, hne⟩ ⟨hn', hne'⟩
        refine ⟨d.monoid.add_mem hn hn', ?_⟩
        have hp := add_pos (d.degree_pos hn hne) (d.degree_pos hn' hne')
        intro h
        simp [← map_add, h] at hp }

variable (d : PositiveDegrees Γ)

/-- Positive quantum Lie elements are exactly those with no component at zero or
outside the allowed monoid. -/
@[simp]
theorem mem_positiveLieAlgebra_iff [DecidableEq Γ] (x : QuantumMonoidAlgebra q β) :
    x ∈ positiveLieAlgebra q β d ↔ ∀ n, n ∉ d.monoid ∨ n = 0 →
      (DirectSum.decompose (grade q β) x n : QuantumMonoidAlgebra q β) = 0 := by
  simp only [positiveLieAlgebra, mem_supportedLieSubalgebra_iff,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, not_and_or, not_not]

/-- Every allowed nonzero homogeneous piece lies in the positive Lie algebra. -/
theorem grade_le_positiveLieAlgebra {n : Γ} (hn : n ∈ d.monoid) (hne : n ≠ 0) :
    grade q β n ≤ (positiveLieAlgebra q β d).toSubmodule :=
  le_supportedLieSubalgebra (grade q β) (S := _) ⟨hn, hne⟩

/-- The inherited exponent pieces of the positive quantum Lie algebra. -/
def positiveLieGrading (n : Γ) : Submodule R (positiveLieAlgebra q β d) :=
  (grade q β n).comap (positiveLieAlgebra q β d).incl.toLinearMap

/-- The positive grading is the inverse image of the ambient quantum grading. -/
theorem positiveLieGrading_def :
    positiveLieGrading q β d = fun n =>
      (grade q β n).comap (positiveLieAlgebra q β d).incl.toLinearMap := (rfl)

/-- Membership in an inherited piece is ambient homogeneous membership. -/
@[simp]
theorem mem_positiveLieGrading (n : Γ) (x : positiveLieAlgebra q β d) :
    x ∈ positiveLieGrading q β d n ↔ (x : QuantumMonoidAlgebra q β) ∈ grade q β n :=
  Iff.rfl

/-- The restricted quantum commutator adds the Lie and coefficient exponents. -/
instance instGradedBracketPositiveLieGrading :
    SetLike.GradedBracket (positiveLieGrading q β d) (grade q β) where
  bracket_mem _ _ _ _ hx ha := by
    rw [LieSubalgebra.coe_bracket_of_module]
    exact SetLike.GradedBracket.bracket_mem (ℒ := grade q β)
      ((mem_positiveLieGrading q β d _ _).mp hx) ha

/-- Positive quantum Lie elements inherit the internal homogeneous decomposition. -/
instance instGradedLieAlgebraPositiveLieGrading [DecidableEq Γ] :
    GradedLieAlgebra (positiveLieGrading q β d) := by
  rw [positiveLieGrading_def]
  exact (positiveLieAlgebra q β d).gradedLieAlgebra (grade q β)
    (by
      unfold positiveLieAlgebra
      exact supportedLieSubalgebra_isHomogeneous (grade q β) _)

/-- The inherited grading vanishes at zero and outside the allowed degrees. -/
instance instIsPositiveGradingPositiveLieGrading :
    IsPositiveGrading d (positiveLieGrading q β d) where
  eq_bot n hn := by
    classical
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hz := (mem_positiveLieAlgebra_iff q β d x).mp x.property n hn
    rwa [DirectSum.decompose_of_mem_same (grade q β)
      ((mem_positiveLieGrading q β d n x).mp hx)] at hz

end Mei.QuantumMonoidAlgebra
