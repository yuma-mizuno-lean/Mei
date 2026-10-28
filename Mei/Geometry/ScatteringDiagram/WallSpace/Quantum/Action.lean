/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Quantum.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Action
public import Mei.Algebra.Lie.Graded.Shifted

/-!
# Quantum wall actions on shifted coefficients

The positive quantum Lie algebra acts on the full quantum algebra by commutators.
This action adds exponent degrees and annihilates coefficients tangent to a wall
normal. Consequently it acts on every shifted coefficient completion, and completed
wall labels fix the images of tangent homogeneous coefficients, including those
whose ambient exponent has negative degree.

We retain Mathlib's adjoint action and its restriction to Lie subalgebras, rather
than introduce another coefficient representation. Annihilation uses the existing
`wallSubmodule` kernel criterion and `lie_monomial`; shifted completions and their
actions use `PositiveDegrees.shiftedLieFiltration` and
`ModuleFiltration.completedBCHAction`. The quantum and annihilation conventions
follow Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §2.1 and Example 2.1(iii), arXiv:1503.06183.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- Quantum wall elements commute with every homogeneous coefficient tangent to
their normal, including at specializations where further commutators vanish. -/
instance instIsWallAnnihilatingAmbient (hβ : β.IsAlt) :
    IsWallAnnihilating (ambientWallSpaces q β hβ) (grade q β) where
  lie_eq_zero := by
    intro n p m x a hx ha hm
    rw [ambientWallSpaces_wall] at hx
    rcases (mem_wallSubmodule_iff q β n m x).mp hx with rfl | ⟨_, hk, hx⟩
    · simp
    have hmp : p ∈ m.ker := hm
    have hnp : β n p = 0 := AddMonoidHom.mem_ker.mp (hk ▸ hmp)
    obtain ⟨r, rfl⟩ := (mem_grade_iff q β n x).mp hx
    obtain ⟨s, rfl⟩ := (mem_grade_iff q β p a).mp ha
    simp [lie_smul, smul_lie, lie_monomial q β hβ, hnp]

/-- Positive quantum wall spaces retain the ambient wall-annihilation property. -/
instance instIsWallAnnihilatingPositive (d : PositiveDegrees Γ) (hβ : β.IsAlt) :
    IsWallAnnihilating (wallSpaces q β d hβ) (grade q β) where
  lie_eq_zero hx ha hm := by
    rw [wallSpaces_wall, Submodule.mem_comap] at hx
    exact IsWallAnnihilating.lie_eq_zero
      (H := ambientWallSpaces q β hβ) (𝒜 := grade q β)
      ((ambientWallSpaces_wall q β hβ _ _).symm ▸ hx) ha hm

section Completion

variable [Algebra ℚ R] [DecidableEq Γ] (d : PositiveDegrees Γ)

/-- Rational scalars on the quantum algebra are induced from the coefficient ring. -/
local instance rationalAlgebra : Algebra ℚ (QuantumMonoidAlgebra q β) :=
  Algebra.compHom _ (algebraMap ℚ R)

/-- Completed quantum wall labels fix every embedded tangent homogeneous coefficient
in any shifted coefficient module. The shift and the coefficient exponent may have
arbitrary ambient degree. -/
theorem shifted_completedBCHAction_of_eq_self_of_normal_eq_zero
    (hβ : β.IsAlt) (p : Γ) {w : SupportedRay d} {m : Γ →+ ℤ}
    {g : d.completedBCHGroup (positiveLieGrading q β d)}
    (hg : g ∈ (wallSpaces q β d hβ).wallGroup w m)
    {r : Γ} (a : d.shiftedLieSubmodule (positiveLieGrading q β d) (grade q β) p)
    (ha : (a : QuantumMonoidAlgebra q β) ∈ grade q β r) (hm : m r = 0) :
    (d.shiftedLieFiltration (positiveLieGrading q β d) (grade q β) p).completedBCHAction
        d (positiveLieGrading q β d) g
        ((d.shiftedLieFiltration (positiveLieGrading q β d) (grade q β) p).of a) =
      (d.shiftedLieFiltration (positiveLieGrading q β d) (grade q β) p).of a := by
  exact (wallSpaces q β d hβ).completedBCHAction_of_eq_self_of_normal_eq_zero
    (fun r => (grade q β r).comap
      (d.shiftedLieSubmodule (positiveLieGrading q β d) (grade q β) p).incl.toLinearMap)
    (d.shiftedLieFiltration (positiveLieGrading q β d) (grade q β) p) hg ha hm

end Completion

end Mei.QuantumMonoidAlgebra
