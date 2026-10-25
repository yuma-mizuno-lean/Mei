/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.RestrictScalars
public import Mei.Algebra.PositiveDegrees.RestrictScalars
public import Mei.Algebra.Lie.Graded.Truncation
public import Mei.Algebra.Lie.RestrictScalars
public import Mei.Algebra.Lie.Quotient.Map

/-!
# Restriction of scalars for graded Lie algebras

A grading of a Lie algebra remains a grading after restricting scalars in its
homogeneous pieces. Its homogeneous components have the same underlying values.
This supplies the graded Lie algebra structure over a smaller coefficient ring
without freeness or flatness assumptions.

For positive gradings, the degree ideals have the same carriers, and finite Lie
truncations are canonically equivalent. These equivalences preserve homogeneous
pieces and projections and commute with the truncation transitions. Thus the
entire finite-order tower can be compared before passing to its inverse limit.

The comparison uses Mathlib's `Submodule.quotEquivOfEq` to identify the cutoff
ideals, followed by `LieIdeal.quotientRestrictScalarsEquiv` to restrict scalars.
-/

public section

variable {R S L ι : Type*} [CommRing R] [CommRing S] [LieRing L]
  [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]
  [DecidableEq ι] [AddCommMonoid ι] (ℒ : ι → Submodule S L)

/-- Restricting scalars preserves a bracket-compatible internal grading. -/
instance GradedLieAlgebra.restrictScalars [GradedLieAlgebra ℒ] :
    GradedLieAlgebra (fun i => (ℒ i).restrictScalars R) where
  toDecomposition := inferInstance
  bracket_mem := SetLike.GradedBracket.bracket_mem (ℒ := ℒ) (ℳ := ℒ)

namespace Mei.PositiveDegrees

variable (d : Mei.PositiveDegrees ι) [GradedLieAlgebra ℒ] [Mei.IsPositiveGrading d ℒ]

/-- The degree ideal after restricting scalars is the restriction of the original ideal. -/
@[simp]
theorem degreeIdeal_restrictScalars (k : ℕ) :
    d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k =
      (d.degreeIdeal ℒ k).restrictScalars R := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Restricting scalars commutes with finite Lie truncation. -/
def truncatedRestrictScalarsEquiv (k : ℕ) :
    d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ⁅R⁆
      d.truncatedLie ℒ k := by
  let e : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ[R]
      L ⧸ (d.degreeIdeal ℒ k).restrictScalars R :=
    Submodule.quotEquivOfEq (R := R)
      (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).toSubmodule
      ((d.degreeIdeal ℒ k).restrictScalars R).toSubmodule (by simp)
  have he (x : L) : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
    Submodule.quotEquivOfEq_mk _ _ _ x
  let e' : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ⁅R⁆
      L ⧸ (d.degreeIdeal ℒ k).restrictScalars R :=
    { e with
      map_lie' {x y} := by
        induction x using Submodule.Quotient.induction_on with | _ x
        induction y using Submodule.Quotient.induction_on with | _ y
        -- Expose the linear equivalence behind the Lie-equivalence structure fields.
        change e (Submodule.Quotient.mk ⁅x, y⁆) =
          ⁅e (Submodule.Quotient.mk x), e (Submodule.Quotient.mk y)⁆
        rw [he, he, he]
        exact LieSubmodule.Quotient.mk_bracket _ _ _ }
  exact e'.trans ((d.degreeIdeal ℒ k).quotientRestrictScalarsEquiv R)

/-- The truncation comparison preserves representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_mk (k : ℕ) (x : L) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  simp only [truncatedRestrictScalarsEquiv, LieEquiv.trans_apply]
  -- The first Lie equivalence wraps a linear equivalence; expose it to use its API.
  change (d.degreeIdeal ℒ k).quotientRestrictScalarsEquiv R
      (Submodule.quotEquivOfEq (R := R)
        (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).toSubmodule
        ((d.degreeIdeal ℒ k).restrictScalars R).toSubmodule (by simp)
        (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
  rw [Submodule.quotEquivOfEq_mk, LieIdeal.quotientRestrictScalarsEquiv_mk]

/-- The inverse truncation comparison preserves representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_symm_mk (k : ℕ) (x : L) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  apply (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).injective
  simp

/-- The comparison identifies the homogeneous pieces in the two truncations. -/
theorem truncatedRestrictScalarsEquiv_mem_iff (k : ℕ) (n : ι)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k x ∈ d.truncatedGrading ℒ k n ↔
      x ∈ d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k n := by
  simp only [mem_truncatedGrading_iff, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨y, hy, (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).injective ?_⟩
    simpa only [LieIdeal.mkQ_apply, LieEquiv.coe_coe, truncatedRestrictScalarsEquiv_mk]
      using h
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [LieIdeal.mkQ_apply]⟩

/-- Homogeneous projections commute with the truncation comparison. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_decompose (k : ℕ) (n : ι)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k
        (DirectSum.decompose (d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k) x n :
          d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) =
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k x) n : d.truncatedLie ℒ k) := by
  induction x using Submodule.Quotient.induction_on with | _ x
  simp

/-- The truncation comparisons commute with every transition in the degree tower. -/
theorem truncatedRestrictScalarsEquiv_naturality {k l : ℕ} (h : k ≤ l) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.comp
        ((d.degreeIdeal (fun n => (ℒ n).restrictScalars R) l).factor
          (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k)
          (d.degreeIdeal_antitone _ h)) =
      (((d.degreeIdeal ℒ l).factor (d.degreeIdeal ℒ k)
        (d.degreeIdeal_antitone ℒ h)).restrictScalars R).comp
          (d.truncatedRestrictScalarsEquiv (R := R) ℒ l).toLieHom := by
  apply (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) l).lieHom_qext
  intro x
  simp [LieIdeal.factor_apply, LieIdeal.mkQ_apply]

end Mei.PositiveDegrees
