/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Lie
public import Mei.Algebra.QuantumMonoidAlgebra.Positive
public import Mei.Algebra.Lie.Filtered.Inner.Basic

/-!
# Positive quantum coefficient actions

The strictly positive quantum Lie algebra embeds in every quantum coefficient
algebra whose allowed monoid contains the positive Lie degrees. Restricting the
commutator along this embedding gives a graded action by derivations. If the
coefficient degrees are nonnegative, the action raises their degree filtration.
The action and filtration statements hold over arbitrary commutative rings.
When the coefficient ring additionally carries an `Algebra ℚ R` structure, the
existing filtered exponential and completed BCH actions apply;
`AlgFiltration.expAction_apply_eq_completedExp_mul` identifies the exponential
with conjugation by the completed exponential of the included Lie element.

The construction uses Mathlib's `LieRingModule.compLieHom`, the supported algebra
grading, and `PositiveDegrees.map_degreeSubmodule_le`. The quantum coefficient
and conjugation setting follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §2.1 and Example 2.1(iii) (arXiv:1503.06183).
No faithfulness or genericity assumption on the quantum parameter is required.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (Q : AddSubmonoid Γ)

/-- Positive quantum Lie elements belong to every coefficient algebra containing
their allowed exponent monoid. -/
theorem positiveLieAlgebra_le_positiveSubalgebra_of_le (hQ : d.monoid ≤ Q) :
    (positiveLieAlgebra q β d).toSubmodule ≤ (positiveSubalgebra q β Q).toSubmodule := by
  classical
  intro x hx
  apply (mem_supportedSubalgebra_iff (grade q β) Q x).mpr
  intro n hn
  exact (mem_positiveLieAlgebra_iff q β d x).mp hx n (Or.inl (fun h => hn (hQ h)))

/-- Include the positive quantum Lie algebra in the chosen coefficient algebra,
viewed as a Lie algebra under its commutator. -/
def coefficientLieHom (hQ : d.monoid ≤ Q) :
    positiveLieAlgebra q β d →ₗ⁅R⁆ positiveSubalgebra q β Q :=
  LieSubalgebra.inclusion (K' := lieSubalgebraOfSubalgebra R _ (positiveSubalgebra q β Q))
    (positiveLieAlgebra_le_positiveSubalgebra_of_le q β d Q hQ)

/-- Inclusion into the full quantum algebra forgets the coefficient restriction. -/
@[simp]
theorem coe_coefficientLieHom (hQ : d.monoid ≤ Q) (x : positiveLieAlgebra q β d) :
    (coefficientLieHom q β d Q hQ x : QuantumMonoidAlgebra q β) = x := (rfl)

/-- The coefficient inclusion preserves the original exponent of homogeneous elements. -/
theorem coefficientLieHom_mem_grading (hQ : d.monoid ≤ Q) {n : Γ}
    {x : positiveLieAlgebra q β d} (hx : x ∈ positiveLieGrading q β d n) :
    coefficientLieHom q β d Q hQ x ∈ (positiveSubalgebra q β Q).grading (grade q β) n :=
  (Subalgebra.mem_grading_iff _ _).mpr ((mem_positiveLieGrading q β d n x).mp hx)

variable (hQ : d.monoid ≤ Q)
  (hδ : ∀ n ∈ Q, 0 ≤ d.degree n)

/-- The inclusion takes a positive Lie term above cutoff `k` into coefficient order
`k + 1`. This specializes the existing degree-submodule map theorem. -/
theorem coefficientLieHom_mem_positiveFiltration {k : ℕ} {x : positiveLieAlgebra q β d}
    (hx : x ∈ d.degreeSubmodule (positiveLieGrading q β d) k) :
    coefficientLieHom q β d Q hQ x ∈ (positiveFiltration q β Q d.degree hδ).ideal (k + 1) := by
  classical
  have h := d.map_degreeSubmodule_le (positiveLieGrading q β d) (PositiveDegreeMap.id d)
    ((positiveSubalgebra q β Q).grading (grade q β))
    (coefficientLieHom q β d Q hQ).toLinearMap
    (fun n x hx => by simpa only [PositiveDegreeMap.id_apply, Submodule.mem_comap,
      LieHom.coe_toLinearMap] using
      coefficientLieHom_mem_grading q β d Q hQ hx) k
  have hx' := h (Submodule.mem_map.mpr ⟨x, by
    simpa only [PositiveDegreeMap.id_modulus] using hx, rfl⟩)
  rw [d.degreeSubmodule_eq_degreeTail] at hx'
  rw [← Submodule.restrictScalars_mem R, positiveFiltration_ideal_restrictScalars]
  exact hx'

namespace QuantumCoefficientAction

variable [Fact (d.monoid ≤ Q)]

/-- Select the inner action of positive quantum Lie elements on positive coefficients.
Open the `QuantumCoefficientAction` scope to use this action. -/
scoped instance instLieRingModule :
    LieRingModule (positiveLieAlgebra q β d) (positiveSubalgebra q β Q) :=
  LieRingModule.compLieHom _ (coefficientLieHom q β d Q Fact.out)

/-- The selected inner coefficient action is linear over the coefficient ring. -/
scoped instance instLieModule :
    LieModule R (positiveLieAlgebra q β d) (positiveSubalgebra q β Q) :=
  LieModule.compLieHom _ (coefficientLieHom q β d Q Fact.out)

/-- The selected action is the commutator with the included positive Lie element. -/
@[simp]
theorem lie_eq (x : positiveLieAlgebra q β d) (a : positiveSubalgebra q β Q) :
    ⁅x, a⁆ = coefficientLieHom q β d Q Fact.out x * a -
      a * coefficientLieHom q β d Q Fact.out x := (rfl)

/-- Exponents add under the selected coefficient action. -/
scoped instance instGradedBracket :
    SetLike.GradedBracket (positiveLieGrading q β d)
      ((positiveSubalgebra q β Q).grading (grade q β)) where
  bracket_mem := by
    intro n p x a hx ha
    rw [lie_eq]
    apply (Subalgebra.mem_grading_iff _ _).mpr
    simpa only [Ring.lie_def, Subalgebra.coe_sub, Subalgebra.coe_mul,
      coe_coefficientLieHom] using
      SetLike.GradedBracket.bracket_mem ((mem_positiveLieGrading q β d n x).mp hx)
        ((Subalgebra.mem_grading_iff _ _).mp ha)

/-- Inner quantum coefficient actions satisfy the associative Leibniz rule. -/
scoped instance instIsDerivationAction :
    IsDerivationAction (positiveLieAlgebra q β d) (positiveSubalgebra q β Q) where
  lie_mul x a b :=
    IsDerivationAction.lie_mul (coefficientLieHom q β d Q Fact.out x) a b

/-- Positive quantum Lie degrees raise the coefficient degree filtration. -/
scoped instance instIsFiltrationRaising :
    IsFiltrationRaising d (positiveLieGrading q β d)
      ((positiveFiltration q β Q d.degree hδ).toModuleFiltration R) where
  lie_mem {a b x y} hx hy := by
    let F := positiveFiltration q β Q d.degree hδ
    have hx' := coefficientLieHom_mem_positiveFiltration q β d Q Fact.out hδ hx
    rw [AlgFiltration.toModuleFiltration_submodule,
      Submodule.restrictScalars_mem] at hy ⊢
    rw [lie_eq]
    exact (F.ideal _).sub_mem (by simpa [Nat.add_assoc, Nat.add_comm 1 b] using F.mul_mem hx' hy)
      (by simpa [Nat.add_assoc, Nat.add_comm b a, Nat.add_left_comm] using F.mul_mem hy hx')

end QuantumCoefficientAction
end Mei.QuantumMonoidAlgebra
