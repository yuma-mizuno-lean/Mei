/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.BaseChange
public import Mei.Algebra.PositiveDegrees.BaseChange
public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import Mei.Algebra.Lie.Quotient.Map
public import TauCeti.Algebra.Lie.BaseChange.Quotient
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Extension of scalars for graded Lie algebras and truncations

Extending each homogeneous piece gives a Lie grading on the scalar extension.
For positive gradings, degree ideals extend to degree ideals, and truncation
commutes with extension of scalars as a Lie algebra. No flatness, freeness, or
dimension hypothesis is imposed on either the pieces or the coefficient algebra.

The decomposition is Mathlib's `DirectSum.Decomposition.baseChange`; the
truncation comparison uses Tau Ceti's `LieIdeal.quotientBaseChangeEquiv`.
-/

public section

open TensorProduct

variable {N R S L : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [LieRing L] [LieAlgebra R L]

variable [AddCommMonoid N] [DecidableEq N] (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]

namespace Mei.PositiveDegrees

variable (d : PositiveDegrees N) [IsPositiveGrading d ℒ]

/-- Extending scalars commutes with the Lie ideal above a degree cutoff. -/
@[simp]
theorem degreeIdeal_baseChange (k : ℕ) :
    (d.degreeIdeal ℒ k).baseChange S =
      d.degreeIdeal (fun n => (ℒ n).baseChange S) k := by
  apply LieSubmodule.toSubmodule_injective
  simp only [LieSubmodule.coe_baseChange, degreeIdeal_toSubmodule, degreeSubmodule_baseChange]

/-- Truncation and extension of scalars commute as Lie algebras. -/
noncomputable def truncatedBaseChangeEquiv (k : ℕ) :
    d.truncatedLie (fun n => (ℒ n).baseChange S) k ≃ₗ⁅S⁆
      S ⊗[R] d.truncatedLie ℒ k :=
  (LieIdeal.quotEquivOfEq _ _ (d.degreeIdeal_baseChange ℒ k).symm).trans
    ((d.degreeIdeal ℒ k).quotientBaseChangeEquiv S)

/-- The comparison commutes with the scalar extension of the quotient projection. -/
@[simp]
theorem truncatedBaseChangeEquiv_mk (k : ℕ) (z : S ⊗[R] L) :
    d.truncatedBaseChangeEquiv ℒ k (LieSubmodule.Quotient.mk z) =
      LieHom.baseChange S (d.degreeIdeal ℒ k).mkQ z := by
  simp [truncatedBaseChangeEquiv]

/-- The comparison sends the class of a pure tensor to the tensor of the class. -/
theorem truncatedBaseChangeEquiv_mk_tmul (k : ℕ) (s : S) (x : L) :
    d.truncatedBaseChangeEquiv ℒ k (LieSubmodule.Quotient.mk (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k) := by
  simp only [truncatedBaseChangeEquiv_mk, LieHom.baseChange_tmul, LieIdeal.mkQ_apply]

/-- The inverse comparison sends a tensor of a class to the class of the tensor. -/
@[simp]
theorem truncatedBaseChangeEquiv_symm_tmul (k : ℕ) (s : S) (x : L) :
    (d.truncatedBaseChangeEquiv ℒ k).symm
        (s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k)) =
      LieSubmodule.Quotient.mk (s ⊗ₜ[R] x) :=
  (d.truncatedBaseChangeEquiv ℒ k).symm_apply_eq.mpr
    (d.truncatedBaseChangeEquiv_mk_tmul ℒ k s x).symm

/-- Extending scalars intertwines the transitions between finite degree quotients. -/
@[simp]
theorem truncatedBaseChangeEquiv_truncationMap {k l : ℕ} (hkl : k ≤ l)
    (x : d.truncatedLie (fun n => (ℒ n).baseChange S) l) :
    d.truncatedBaseChangeEquiv ℒ k
        (d.truncationMap (fun n => (ℒ n).baseChange S) hkl x) =
      LieHom.baseChange S (d.truncationMap ℒ hkl) (d.truncatedBaseChangeEquiv ℒ l x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal (fun n => (ℒ n).baseChange S) l).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, truncationMap_mk, truncatedBaseChangeEquiv_mk]
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp [LieIdeal.mkQ_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The truncation comparison identifies each extended homogeneous piece. -/
theorem map_truncatedGrading_baseChange (k : ℕ) (n : N) :
    (d.truncatedGrading (fun n => (ℒ n).baseChange S) k n).map
        (d.truncatedBaseChangeEquiv ℒ k).toLinearMap =
      (d.truncatedGrading ℒ k n).baseChange S := by
  have square : (d.truncatedBaseChangeEquiv ℒ k).toLinearMap.comp
      (d.degreeIdeal (fun n => (ℒ n).baseChange S) k).toSubmodule.mkQ =
        (d.degreeIdeal ℒ k).toSubmodule.mkQ.baseChange S := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      LieHom.coe_toLinearMap, LieEquiv.coe_coe]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact d.truncatedBaseChangeEquiv_mk_tmul ℒ k s x
  rw [truncatedGrading_eq, ← Submodule.map_comp, square, truncatedGrading_eq,
    Submodule.baseChange_map]

end Mei.PositiveDegrees
