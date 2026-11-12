/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.BaseChange
public import Mei.Algebra.PositiveDegrees.BaseChange
public import Mei.Algebra.Lie.BaseChange
public import Mei.Algebra.Lie.Graded.RestrictScalars
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

The map `x ↦ 1 ⊗ x` is an `R`-linear fixed-degree graded Lie homomorphism from the grading to
the restriction to `R` of the extended grading (`Mei.GradedLieHom.includeRight`). Under the
scalar-restriction and truncation comparisons, its finite quotient maps are `x ↦ 1 ⊗ x` on the
truncations (`Mei.GradedLieHom.truncatedMap_includeRight`).
-/

public section

open TensorProduct

variable {N R S L M ι κ : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [LieRing L] [LieAlgebra R L]

/-- Scalar extension preserves a graded bracket action, independently of any decomposition. -/
instance SetLike.GradedBracket.baseChange [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] [VAdd ι κ]
    (ℒ : ι → Submodule R L) (ℳ : κ → Submodule R M)
    [SetLike.GradedBracket ℒ ℳ] :
    SetLike.GradedBracket (fun i => (ℒ i).baseChange S)
      (fun j => (ℳ j).baseChange S) where
  bracket_mem := by
    intro i j x y hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      induction y using TensorProduct.inductionOn with
      | tmul t y =>
        simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
          LieAlgebra.ExtendScalars.bracket_tmul] using
          Submodule.tmul_mem_baseChange_of_mem (s * t)
            (SetLike.GradedBracket.bracket_mem x.property y.property)
      | add y z hy hz =>
        rw [map_add, lie_add]
        exact Submodule.add_mem _ hy hz
    | add x z hx hz =>
      rw [map_add, add_lie ((ℒ i).subtype.baseChange S x)
        ((ℒ i).subtype.baseChange S z) ((ℳ j).subtype.baseChange S y)]
      exact Submodule.add_mem _ hx hz

variable [AddCommMonoid N] [DecidableEq N] (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]

/-- The extended homogeneous pieces form a Lie grading on the scalar extension. -/
instance GradedLieAlgebra.baseChange :
    GradedLieAlgebra (fun n => (ℒ n).baseChange S) where
  toDecomposition := inferInstance
  toGradedBracket := inferInstance

/-- Scalar extension preserves the grading of a representation of a graded Lie algebra. -/
instance GradedLieModule.baseChange [DecidableEq ι] [AddCommMonoid ι]
    [DecidableEq κ] [VAdd ι κ] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M]
    (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]
    (ℳ : κ → Submodule R M) [DirectSum.Decomposition ℳ] [GradedLieModule ℒ ℳ] :
    GradedLieModule (fun i => (ℒ i).baseChange S) (fun j => (ℳ j).baseChange S) where
  toGradedBracket := inferInstance

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

namespace Mei.GradedLieHom

variable {d : PositiveDegrees N}

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
variable (S) in
/-- The `R`-linear fixed-degree graded Lie homomorphism `x ↦ 1 ⊗ x` from the grading `ℒ`,
regarded over `R`, to the restriction to `R` of the extended grading on `S ⊗[R] L`. -/
def includeRight :
    GradedLieHom (PositiveDegreeMap.id d) (fun n => (ℒ n).restrictScalars R)
      (fun n => ((ℒ n).baseChange S).restrictScalars R) where
  toLieHom := LieAlgebra.ExtendScalars.includeRight R S L
  map_mem {n _} hx := by
    rw [Submodule.restrictScalars_mem] at hx ⊢
    simpa using Submodule.tmul_mem_baseChange_of_mem (1 : S) hx

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
/-- The graded inclusion sends `x` to `1 ⊗ x`. -/
@[simp]
theorem includeRight_apply (x : L) : includeRight (d := d) S ℒ x = 1 ⊗ₜ x :=
  LieAlgebra.ExtendScalars.includeRight_apply x

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
/-- The underlying Lie homomorphism of the graded inclusion is `x ↦ 1 ⊗ x`. -/
@[simp]
theorem toLieHom_includeRight :
    (includeRight (d := d) S ℒ).toLieHom = LieAlgebra.ExtendScalars.includeRight R S L := (rfl)

variable [IsPositiveGrading d ℒ]

variable (S) in
/-- Under the scalar-restriction comparisons and the truncation comparison
`PositiveDegrees.truncatedBaseChangeEquiv`, the order-`k` quotient map of the graded inclusion
is the inclusion `x ↦ 1 ⊗ x` of the order-`k` truncation into its scalar extension. -/
theorem truncatedMap_includeRight (k : ℕ) :
    ((d.truncatedBaseChangeEquiv (S := S) ℒ k).toLieHom.restrictScalars R).comp
        ((d.truncatedRestrictScalarsEquiv (R := R) (fun n => (ℒ n).baseChange S) k).toLieHom.comp
          ((includeRight (d := d) S ℒ).truncatedMap (a := k) k
            (PositiveDegreeMap.id_modulus k).le)) =
      (LieAlgebra.ExtendScalars.includeRight R S (d.truncatedLie ℒ k)).comp
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom := by
  apply (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

end Mei.GradedLieHom
