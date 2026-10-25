/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Exponential
public import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# Exponentiating filtration-raising derivation actions

For a filtration-raising Lie action by derivations, the finite operator exponentials are
algebra automorphisms of the coefficient quotients. Quotient transitions intertwine these
automorphisms, so they assemble to an algebra automorphism of the completion for every
Lie element. Negating the Lie element gives the inverse.

The construction uses the finite automorphisms and transition compatibility in
`Mei.Algebra.Lie.Filtered.Exponential`, together with the compatible-family algebra lift
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

private noncomputable def expActionHom (x : L) : F.completion →ₐ[R] F.completion :=
  F.liftₐ (fun k => (F.quotientExpLieAction d ℒ k x).toAlgHom.comp (F.projectionₐ k)) (by
    intro k l h
    ext a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, projectionₐ_apply,
      Ideal.Quotient.factorₐ_apply]
    rw [F.factor_quotientExpLieAction d ℒ h, F.factor_projection h])

/-- The levelwise exponential of a filtration-raising derivation acts on the completion
by an algebra automorphism. -/
noncomputable def expAction (x : L) : F.completion ≃ₐ[R] F.completion :=
  AlgEquiv.ofAlgHom (F.expActionHom d ℒ x) (F.expActionHom d ℒ (-x))
    (by
      apply F.algHom_ext
      intro k
      ext a
      simp only [AlgHom.comp_apply, projectionₐ_apply, expActionHom, projection_liftₐ,
        AlgEquiv.coe_toAlgHom, quotientExpLieAction_neg, AlgEquiv.apply_symm_apply,
        AlgHom.id_apply])
    (by
      apply F.algHom_ext
      intro k
      ext a
      simp only [AlgHom.comp_apply, projectionₐ_apply, expActionHom, projection_liftₐ,
        AlgEquiv.coe_toAlgHom, quotientExpLieAction_neg, AlgEquiv.symm_apply_apply,
        AlgHom.id_apply])

/-- Every projection of the completed automorphism is its finite-order exponential. -/
@[simp]
theorem projection_expAction (x : L) (a : F.completion) (k : ℕ) :
    F.projection k (F.expAction d ℒ x a) =
      F.quotientExpLieAction d ℒ k x (F.projection k a) := by
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
