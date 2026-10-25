/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Algebra
public import Mei.LinearAlgebra.End.Exp
public import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# Exponentiating filtration-raising derivation actions

For a filtration-raising Lie action by derivations, the finite operator exponentials are
algebra automorphisms of the coefficient quotients. Quotient transitions intertwine these
automorphisms, so they assemble to an algebra automorphism of the completion for every
Lie element. Negating the Lie element gives the inverse.

The construction uses `AlgFiltration.quotientLieAction`, Mathlib's
`Module.End.commute_exp_left_of_commute`, and the compatible-family algebra lift
`AlgFiltration.liftₐ`. It requires no norm, basis, or separatedness assumption.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei.AlgFiltration

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [Ring A] [Algebra R A]
  [LieRingModule L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)] [IsDerivationAction L A]

variable [Algebra ℚ A]

/-- Exponentiation of a Lie element on the order-`k` coefficient algebra. -/
noncomputable def quotientExp (k : ℕ) (x : L) :
    (A ⧸ F.ideal (k + 1)) ≃ₐ[R] (A ⧸ F.ideal (k + 1)) :=
  (F.quotientLieAction d ℒ k x).expAlgEquiv (F.quotientLieAction_mul d ℒ k x)
    (by exact ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩)

/-- The quotient automorphism applies by the finite operator exponential. -/
@[simp]
theorem quotientExp_apply (k : ℕ) (x : L) (a : A ⧸ F.ideal (k + 1)) :
    F.quotientExp d ℒ k x a = IsNilpotent.exp (F.quotientLieAction d ℒ k x) a := by
  dsimp only [quotientExp]
  exact Module.End.expAlgEquiv_apply _ _ _ _

/-- Negating the Lie element inverts its quotient automorphism. -/
@[simp]
theorem quotientExp_neg (k : ℕ) (x : L) :
    F.quotientExp d ℒ k (-x) = (F.quotientExp d ℒ k x).symm := by
  ext a
  apply (F.quotientExp d ℒ k x).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa only [quotientExp_apply, map_neg, Module.End.mul_apply, Module.End.one_apply] using
    DFunLike.congr_fun (IsNilpotent.exp_mul_exp_neg_self
      (a := F.quotientLieAction d ℒ k x)
      ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩) a

/-- The zero Lie element acts by the identity automorphism. -/
@[simp]
theorem quotientExp_zero (k : ℕ) : F.quotientExp d ℒ k 0 = AlgEquiv.refl := by
  ext a
  simp [IsNilpotent.exp_zero]

/-- Quotient transitions intertwine the finite exponential automorphisms. -/
theorem factor_quotientExp {k l : ℕ} (h : k ≤ l) (x : L)
    (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (F.quotientExp d ℒ l x a) =
        F.quotientExp d ℒ k x
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) := by
  let q := (Ideal.Quotient.factorₐ R (F.antitone (Nat.add_le_add_right h 1))).toLinearMap
  have he := Module.End.commute_exp_left_of_commute
    (g := q) ⟨l + 1, F.quotientLieAction_pow_eq_zero d ℒ l x⟩
    (by exact ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩) (by
      ext a
      exact (F.factor_quotientLieAction d ℒ h x a).symm)
  simpa only [q, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply,
    LinearMap.comp_apply, quotientExp_apply] using
    (DFunLike.congr_fun he a).symm

private noncomputable def expActionHom (x : L) : F.completion →ₐ[R] F.completion :=
  F.liftₐ (fun k => (F.quotientExp d ℒ k x).toAlgHom.comp (F.projectionₐ k)) (by
    intro k l h
    ext a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, projectionₐ_apply,
      Ideal.Quotient.factorₐ_apply]
    rw [F.factor_quotientExp d ℒ h, F.factor_projection h])

/-- The levelwise exponential of a filtration-raising derivation acts on the completion
by an algebra automorphism. -/
noncomputable def expAction (x : L) : F.completion ≃ₐ[R] F.completion :=
  AlgEquiv.ofAlgHom (F.expActionHom d ℒ x) (F.expActionHom d ℒ (-x))
    (by
      apply F.algHom_ext
      intro k
      ext a
      simp only [AlgHom.comp_apply, projectionₐ_apply, expActionHom, projection_liftₐ,
        AlgEquiv.coe_toAlgHom, quotientExp_neg, AlgEquiv.apply_symm_apply, AlgHom.id_apply])
    (by
      apply F.algHom_ext
      intro k
      ext a
      simp only [AlgHom.comp_apply, projectionₐ_apply, expActionHom, projection_liftₐ,
        AlgEquiv.coe_toAlgHom, quotientExp_neg, AlgEquiv.symm_apply_apply, AlgHom.id_apply])

/-- Every projection of the completed automorphism is its finite-order exponential. -/
@[simp]
theorem projection_expAction (x : L) (a : F.completion) (k : ℕ) :
    F.projection k (F.expAction d ℒ x a) =
      F.quotientExp d ℒ k x (F.projection k a) := by
  simp [expAction, expActionHom]

/-- The inverse completed automorphism is the exponential of the negative Lie element. -/
@[simp]
theorem expAction_neg (x : L) :
    F.expAction d ℒ (-x) = (F.expAction d ℒ x).symm := by
  apply AlgEquiv.ext
  intro a
  apply (F.expAction d ℒ x).injective
  apply F.completion_ext
  intro k
  simp

/-- The zero Lie element gives the identity on the completion. -/
@[simp]
theorem expAction_zero : F.expAction d ℒ 0 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro a
  apply F.completion_ext
  intro k
  simp

end Mei.AlgFiltration
