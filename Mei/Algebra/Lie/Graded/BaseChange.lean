/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.BaseChange
public import TauCeti.Algebra.PositiveDegrees.BaseChange
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

namespace TauCeti.PositiveDegrees

variable (d : PositiveDegrees N) [IsPositiveGrading d ℒ]

/-- Extending scalars commutes with the Lie ideal above a degree cutoff. -/
@[simp]
theorem truncationIdeal_baseChange (k : ℕ) :
    (d.truncationIdeal ℒ k).baseChange S =
      d.truncationIdeal (fun n => (ℒ n).baseChange S) k := by
  apply LieSubmodule.toSubmodule_injective
  simp only [LieSubmodule.coe_baseChange, truncationIdeal_toSubmodule, degreeSubmodule_baseChange]

/-- Truncation and extension of scalars commute as Lie algebras. -/
noncomputable def lieTruncationBaseChangeEquiv (k : ℕ) :
    d.lieTruncation (fun n => (ℒ n).baseChange S) k ≃ₗ⁅S⁆
      S ⊗[R] d.lieTruncation ℒ k :=
  (LieIdeal.quotEquivOfEq _ _ (d.truncationIdeal_baseChange ℒ k).symm).trans
    ((d.truncationIdeal ℒ k).quotientBaseChangeEquiv S)

/-- The comparison commutes with the scalar extension of the quotient projection. -/
@[simp]
theorem lieTruncationBaseChangeEquiv_mk (k : ℕ) (z : S ⊗[R] L) :
    d.lieTruncationBaseChangeEquiv ℒ k (LieSubmodule.Quotient.mk z) =
      LieHom.baseChange S (d.truncationIdeal ℒ k).mkQ z := by
  simp [lieTruncationBaseChangeEquiv]

/-- The comparison sends the class of a pure tensor to the tensor of the class. -/
theorem lieTruncationBaseChangeEquiv_mk_tmul (k : ℕ) (s : S) (x : L) :
    d.lieTruncationBaseChangeEquiv ℒ k (LieSubmodule.Quotient.mk (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.lieTruncation ℒ k) := by
  simp only [lieTruncationBaseChangeEquiv_mk, LieHom.baseChange_tmul, LieIdeal.mkQ_apply]

/-- The inverse comparison sends a tensor of a class to the class of the tensor. -/
@[simp]
theorem lieTruncationBaseChangeEquiv_symm_tmul (k : ℕ) (s : S) (x : L) :
    (d.lieTruncationBaseChangeEquiv ℒ k).symm
        (s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.lieTruncation ℒ k)) =
      LieSubmodule.Quotient.mk (s ⊗ₜ[R] x) :=
  (d.lieTruncationBaseChangeEquiv ℒ k).symm_apply_eq.mpr
    (d.lieTruncationBaseChangeEquiv_mk_tmul ℒ k s x).symm

/-- Extending scalars intertwines the transitions between finite degree quotients. -/
@[simp]
theorem lieTruncationBaseChangeEquiv_lieTruncationMap {k l : ℕ} (hkl : k ≤ l)
    (x : d.lieTruncation (fun n => (ℒ n).baseChange S) l) :
    d.lieTruncationBaseChangeEquiv ℒ k
        (d.lieTruncationMap (fun n => (ℒ n).baseChange S) hkl x) =
      LieHom.baseChange S (d.lieTruncationMap ℒ hkl) (d.lieTruncationBaseChangeEquiv ℒ l x) := by
  obtain ⟨x, rfl⟩ := (d.truncationIdeal (fun n => (ℒ n).baseChange S) l).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, lieTruncationMap_mk, lieTruncationBaseChangeEquiv_mk]
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp [LieIdeal.mkQ_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The truncation comparison identifies each extended homogeneous piece. -/
theorem map_lieTruncationGrading_baseChange (k : ℕ) (n : N) :
    (d.lieTruncationGrading (fun n => (ℒ n).baseChange S) k n).map
        (d.lieTruncationBaseChangeEquiv ℒ k).toLinearMap =
      (d.lieTruncationGrading ℒ k n).baseChange S := by
  have square : (d.lieTruncationBaseChangeEquiv ℒ k).toLinearMap.comp
      (d.truncationIdeal (fun n => (ℒ n).baseChange S) k).toSubmodule.mkQ =
        (d.truncationIdeal ℒ k).toSubmodule.mkQ.baseChange S := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      LieHom.coe_toLinearMap, LieEquiv.coe_coe]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact d.lieTruncationBaseChangeEquiv_mk_tmul ℒ k s x
  rw [lieTruncationGrading_eq, ← Submodule.map_comp, square, lieTruncationGrading_eq,
    Submodule.baseChange_map]

end TauCeti.PositiveDegrees
