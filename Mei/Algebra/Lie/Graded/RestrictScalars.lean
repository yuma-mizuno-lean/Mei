/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.RestrictScalars
public import Mei.Algebra.Lie.Graded.Truncation
public import Mei.Algebra.Lie.Quotient.Map
public import Mei.Algebra.Lie.RestrictScalars
public import Mei.Algebra.PositiveDegrees.RestrictScalars

/-!
# Restriction of scalars for graded Lie algebras

A grading of a Lie algebra remains a grading after restricting scalars in its
homogeneous pieces. Its homogeneous components have the same underlying values.
This supplies the graded Lie algebra structure over a smaller coefficient ring
without freeness or flatness assumptions.

For a positive grading, the degree ideals restrict on the same carriers. Consequently
finite Lie truncation commutes with restriction of scalars, preserving homogeneous
pieces, homogeneous projections and transitions between cutoffs. The comparison uses
Mathlib's `Submodule.quotEquivOfEq` and Mei's `LieIdeal.quotientRestrictScalarsEquiv`.
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

/-- The degree ideal of the restricted grading is the restriction of the degree ideal. -/
@[simp]
theorem degreeIdeal_restrictScalars (k : ℕ) :
    d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k =
      (d.degreeIdeal ℒ k).restrictScalars R := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Finite Lie truncation commutes with restriction of scalars. -/
def truncatedRestrictScalarsEquiv (k : ℕ) :
    d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ⁅R⁆ d.truncatedLie ℒ k := by
  let e := Submodule.quotEquivOfEq _ _
    (congrArg LieSubmodule.toSubmodule (d.degreeIdeal_restrictScalars (R := R) ℒ k))
  let eLie : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ⁅R⁆
      L ⧸ (d.degreeIdeal ℒ k).restrictScalars R :=
    { e with
      map_lie' {x y} := by
        induction x using Submodule.Quotient.induction_on
        induction y using Submodule.Quotient.induction_on
        rfl }
  exact eLie.trans ((d.degreeIdeal ℒ k).quotientRestrictScalarsEquiv R)

/-- The comparison preserves quotient representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_mk (k : ℕ) (x : L) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  unfold truncatedRestrictScalarsEquiv
  rw [LieEquiv.trans_apply]
  exact (d.degreeIdeal ℒ k).quotientRestrictScalarsEquiv_mk (R := R) x

/-- The inverse comparison preserves quotient representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_symm_mk (k : ℕ) (x : L) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  apply (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).injective
  simp

/-- The comparison intertwines the restricted quotient projection and the quotient projection
of the restricted grading. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_comp_mkQ (k : ℕ) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.comp
        (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).mkQ =
      (d.degreeIdeal ℒ k).mkQ.restrictScalars R := by
  ext x
  simp [LieIdeal.mkQ_apply]

/-- The comparison identifies homogeneous pieces with their restrictions of scalars. -/
theorem map_truncatedGrading_restrictScalars (k : ℕ) (n : ι) :
    (d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k n).map
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLinearMap =
      (d.truncatedGrading ℒ k n).restrictScalars R := by
  simp only [truncatedGrading_eq, ← Submodule.map_comp, Submodule.restrictScalars_map]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact d.truncatedRestrictScalarsEquiv_mk (R := R) ℒ k x

/-- Homogeneous projection commutes with the scalar-restriction comparison. -/
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

/-- The finite-order comparisons commute with transitions to smaller cutoffs. -/
theorem truncatedRestrictScalarsEquiv_naturality {k l : ℕ} (h : k ≤ l) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.comp
        ((d.degreeIdeal (fun n => (ℒ n).restrictScalars R) l).factor _
          (d.degreeIdeal_antitone _ h)) =
      (((d.degreeIdeal ℒ l).factor _ (d.degreeIdeal_antitone ℒ h)).restrictScalars R).comp
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ l).toLieHom := by
  apply (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) l).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

end Mei.PositiveDegrees
