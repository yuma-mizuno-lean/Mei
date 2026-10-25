/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Action
public import Mei.Algebra.Lie.Graded.Completion
public import Mei.LinearAlgebra.ModuleFiltration.Map
public import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Exponential actions on completed coefficient modules

A filtration-raising Lie module action exponentiates on each finite coefficient quotient.
These linear automorphisms are compatible with both Lie and coefficient truncation, so
an element of the degree-completed Lie algebra acts on the completed module. Negation
inverts the automorphism, and every induced module filtration term is preserved and
reflected. Equivariant filtration-preserving coefficient maps intertwine the exponentials
before and after completion. No derivation rule or multiplication on the coefficient
module is required.

The construction uses `ModuleFiltration.truncatedLieAction`, Mathlib's finite nilpotent
exponential, `LinearEquiv.ofLinearMap`, and the compatible-family lift
`ModuleFiltration.lift`. Multiplicativity for the BCH group is a separate statement.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei.ModuleFiltration

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]
  (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

/-- The rational module structure on each coefficient quotient is induced from `R`. -/
local instance quotientRatModule (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom (F.quotient k) (algebraMap ℚ R)

/-- Exponentiate a truncated Lie element on the matching coefficient quotient.
The inverse is the exponential of its negative. -/
noncomputable def truncatedExpLieAction (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.quotient k ≃ₗ[R] F.quotient k :=
  LinearEquiv.ofLinearMap (IsNilpotent.exp (F.truncatedLieAction d ℒ k x))
    (IsNilpotent.exp (-(F.truncatedLieAction d ℒ k x)))
    (IsNilpotent.exp_mul_exp_neg_self
      ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩)
    (IsNilpotent.exp_neg_mul_exp_self
      ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩)

/-- The finite automorphism evaluates by the nilpotent endomorphism exponential. -/
@[simp]
theorem truncatedExpLieAction_apply (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : F.quotient k) :
    F.truncatedExpLieAction d ℒ k x a = IsNilpotent.exp (F.truncatedLieAction d ℒ k x) a :=
  (rfl)

/-- Zero in the Lie truncation acts as the identity. -/
@[simp]
theorem truncatedExpLieAction_zero (k : ℕ) :
    F.truncatedExpLieAction d ℒ k 0 = LinearEquiv.refl R (F.quotient k) := by
  apply LinearEquiv.ext
  intro a
  simp [IsNilpotent.exp_zero]

/-- Negation in the Lie truncation inverts the finite exponential. -/
@[simp]
theorem truncatedExpLieAction_neg (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.truncatedExpLieAction d ℒ k (-x) = (F.truncatedExpLieAction d ℒ k x).symm := by
  apply LinearEquiv.ext
  intro a
  apply (F.truncatedExpLieAction d ℒ k x).injective
  rw [LinearEquiv.apply_symm_apply, truncatedExpLieAction_apply,
    truncatedExpLieAction_apply, map_neg]
  exact LinearMap.congr_fun
    (IsNilpotent.exp_mul_exp_neg_self
      ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩) a

/-- Lie and coefficient transitions intertwine the finite exponential actions. -/
theorem transition_truncatedExpLieAction {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (a : F.quotient l) :
    F.transition h (F.truncatedExpLieAction d ℒ l x a) =
      F.truncatedExpLieAction d ℒ k (d.truncationMap ℒ h x) (F.transition h a) := by
  have hc : (F.truncatedLieAction d ℒ k (d.truncationMap ℒ h x)).comp (F.transition h) =
      (F.transition h).comp (F.truncatedLieAction d ℒ l x) := by
    apply LinearMap.ext
    intro q
    exact (F.transition_truncatedLieAction d ℒ h x q).symm
  simpa only [truncatedExpLieAction_apply, LinearMap.comp_apply] using
    (LinearMap.congr_fun (Module.End.commute_exp_left_of_commute
      ⟨l + 1, F.truncatedLieAction_pow_eq_zero d ℒ l x⟩
      ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k (d.truncationMap ℒ h x)⟩ hc) a).symm

local notation "π" => LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

private noncomputable def completedExpEnd (x : d.completedLie ℒ) :
    Module.End R F.completion :=
  F.lift (fun k => (F.truncatedExpLieAction d ℒ k (π k x)).toLinearMap.comp (F.projection k))
    (by
      intro k l h
      apply LinearMap.ext
      intro a
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        transition_truncatedExpLieAction, transition_projection]
      rw [PositiveDegrees.truncationMap_def, LieIdeal.factor_completionProjection])

/-- Every degree-completed Lie element exponentiates to a linear automorphism of the
completed coefficient module, computed independently at each finite order. -/
noncomputable def completedExpLieAction (x : d.completedLie ℒ) :
    F.completion ≃ₗ[R] F.completion :=
  LinearEquiv.ofLinearMap (F.completedExpEnd d ℒ x) (F.completedExpEnd d ℒ (-x))
    (by
      apply LinearMap.ext
      intro a
      apply F.completion_ext
      intro k
      simp only [LinearMap.comp_apply, LinearMap.id_apply, completedExpEnd,
        projection_lift, LinearEquiv.coe_coe, map_neg, truncatedExpLieAction_neg,
        LinearEquiv.apply_symm_apply])
    (by
      apply LinearMap.ext
      intro a
      apply F.completion_ext
      intro k
      simp only [LinearMap.comp_apply, LinearMap.id_apply, completedExpEnd,
        projection_lift, LinearEquiv.coe_coe, map_neg, truncatedExpLieAction_neg,
        LinearEquiv.symm_apply_apply])

/-- The completed exponential is characterized by its finite-order actions. -/
@[simp]
theorem projection_completedExpLieAction (x : d.completedLie ℒ) (a : F.completion) (k : ℕ) :
    F.projection k (F.completedExpLieAction d ℒ x a) =
      F.truncatedExpLieAction d ℒ k (π k x) (F.projection k a) := by
  simp [completedExpLieAction, completedExpEnd]

/-- The projection formula uniquely determines the completed linear automorphism. -/
theorem completedExpLieAction_unique (x : d.completedLie ℒ)
    (e : F.completion ≃ₗ[R] F.completion)
    (he : ∀ (a : F.completion) (k : ℕ), F.projection k (e a) =
      F.truncatedExpLieAction d ℒ k (π k x) (F.projection k a)) :
    e = F.completedExpLieAction d ℒ x := by
  apply LinearEquiv.ext
  intro a
  apply F.completion_ext
  intro k
  rw [projection_completedExpLieAction, he]

/-- Zero in the completed Lie algebra acts as the identity. -/
@[simp]
theorem completedExpLieAction_zero :
    F.completedExpLieAction d ℒ 0 = LinearEquiv.refl R F.completion := by
  apply LinearEquiv.ext
  intro a
  apply F.completion_ext
  intro k
  simp

/-- Negating a completed Lie element gives the inverse exponential action. -/
@[simp]
theorem completedExpLieAction_neg (x : d.completedLie ℒ) :
    F.completedExpLieAction d ℒ (-x) = (F.completedExpLieAction d ℒ x).symm := by
  apply LinearEquiv.ext
  intro a
  apply (F.completedExpLieAction d ℒ x).injective
  apply F.completion_ext
  intro k
  simp

/-- Exponentials preserve and reflect every term of the completed module filtration. -/
@[simp]
theorem completedExpLieAction_mem_completedFiltration_iff (x : d.completedLie ℒ)
    (a : F.completion) (k : ℕ) :
    F.completedExpLieAction d ℒ x a ∈ F.completedFiltration.submodule k ↔
      a ∈ F.completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [completedFiltration_succ, LinearMap.mem_ker, projection_completedExpLieAction,
      LinearEquiv.map_eq_zero_iff]

section EquivariantMap

variable {M' : Type*} [AddCommGroup M'] [Module R M']
  [LieRingModule L M'] [LieModule R L M']
  (G : ModuleFiltration R M') [IsFiltrationRaising d ℒ G]
  (f : M →ₗ[R] M')
  (hf : ∀ k, F.submodule (k + 1) ≤ (G.submodule (k + 1)).comap f)
  (hequiv : ∀ (x : L) (m : M), f ⁅x, m⁆ = ⁅x, f m⁆)

include hequiv

/-- An equivariant filtration-preserving linear map intertwines the finite exponentials. -/
theorem mapQ_truncatedExpLieAction (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : F.quotient k) :
    (F.submodule (k + 1)).mapQ (G.submodule (k + 1)) f (hf k)
        (F.truncatedExpLieAction d ℒ k x a) =
      G.truncatedExpLieAction d ℒ k x
        ((F.submodule (k + 1)).mapQ (G.submodule (k + 1)) f (hf k) a) := by
  let qf := (F.submodule (k + 1)).mapQ (G.submodule (k + 1)) f (hf k)
  have hc : (G.truncatedLieAction d ℒ k x).comp qf =
      qf.comp (F.truncatedLieAction d ℒ k x) := by
    apply LinearMap.ext
    intro a
    obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
    obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective a
    simp only [LinearMap.comp_apply, LieIdeal.mkQ_apply, truncatedLieAction_mk,
      Submodule.mkQ_apply, qf, Submodule.mapQ_apply, quotientLieAction_mk, hequiv]
  simpa only [truncatedExpLieAction_apply, LinearMap.comp_apply] using
    (LinearMap.congr_fun (Module.End.commute_exp_left_of_commute
      ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩
      ⟨k + 1, G.truncatedLieAction_pow_eq_zero d ℒ k x⟩ hc) a).symm

/-- Equivariant filtration-preserving linear maps remain equivariant for exponential
operators of completed Lie elements on completed coefficient modules. -/
theorem completionMap_completedExpLieAction (x : d.completedLie ℒ) (a : F.completion) :
    F.completionMap G f id monotone_id hf (F.completedExpLieAction d ℒ x a) =
      G.completedExpLieAction d ℒ x (F.completionMap G f id monotone_id hf a) := by
  apply G.completion_ext
  intro k
  simp only [projection_completionMap, projection_completedExpLieAction, id_eq]
  exact F.mapQ_truncatedExpLieAction d ℒ G f hf hequiv k (π k x) (F.projection k a)

end EquivariantMap

end Mei.ModuleFiltration
