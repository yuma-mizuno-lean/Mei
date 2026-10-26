/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.Algebra.Lie.BCH.RestrictScalars
public import Mei.LinearAlgebra.ModuleFiltration.RestrictScalars

/-!
# Scalar restriction of completed coefficient actions

Restricting scalars in a filtration-raising Lie action preserves its finite
exponentials and its completed BCH action. The comparisons use the same Lie
and coefficient representatives at every order. For module coefficients, the
existing scalar-restriction equivalence of completions intertwines the actions;
for algebra coefficients, the completion has the same underlying ring.

The construction uses `PositiveDegrees.completedBCHRestrictScalarsEquiv`,
`ModuleFiltration.completionRestrictScalarsEquiv`, and Mathlib's finite nilpotent
exponential. No freeness, flatness or separatedness is required.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei

variable {N R S L M : Type*} [AddCommMonoid N] [CommRing R] [CommRing S]
  [SMul R S] [LieRing L] [LieAlgebra S L] [LieAlgebra R L]
  [IsScalarTower R S L] [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M] [LieRingModule L M]

/-- Scalar restriction preserves the filtration-raising condition on a Lie action. -/
instance IsFiltrationRaising.restrictScalars (d : PositiveDegrees N)
    (ℒ : N → Submodule S L) (F : ModuleFiltration S M)
    [IsFiltrationRaising d ℒ F] :
    IsFiltrationRaising d (fun n => (ℒ n).restrictScalars R) (F.restrictScalars R) where
  lie_mem hx hm := IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F)
    (by simpa only [PositiveDegrees.degreeSubmodule_restrictScalars,
      Submodule.restrictScalars_mem] using hx) hm

namespace ModuleFiltration

variable [LieModule S L M] [LieModule R L M]
  (F : ModuleFiltration S M) (d : PositiveDegrees N) (ℒ : N → Submodule S L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

/-- The finite module comparison intertwines the restricted Lie representations. -/
@[simp]
theorem restrictScalarsEquiv_truncatedLieAction (k : ℕ)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k)
    (a : (F.restrictScalars R).quotient k) :
    Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))
        ((F.restrictScalars R).truncatedLieAction d
          (fun n => (ℒ n).restrictScalars R) k x a) =
      F.truncatedLieAction d ℒ k (d.truncatedRestrictScalarsEquiv (R := R) ℒ k x)
        (Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1)) a) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).surjective_mkQ x
  obtain ⟨m, rfl⟩ := ((F.restrictScalars R).submodule (k + 1)).mkQ_surjective a
  simp [LieIdeal.mkQ_apply]

section Rational

variable [Algebra ℚ R] [Algebra ℚ S]

/-- Rational scalars on a coefficient quotient are induced from its original ring. -/
local instance quotientRatModuleRestrict (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom _ (algebraMap ℚ S)

/-- Rational scalars on a restricted coefficient quotient are induced from `R`. -/
local instance restrictedQuotientRatModule (k : ℕ) :
    Module ℚ ((F.restrictScalars R).quotient k) :=
  Module.compHom _ (algebraMap ℚ R)

/-- Finite exponential actions are intertwined by the scalar-restriction comparisons. -/
theorem restrictScalarsEquiv_truncatedExpLieAction (k : ℕ)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k)
    (a : (F.restrictScalars R).quotient k) :
    Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))
        ((F.restrictScalars R).truncatedExpLieAction d
          (fun n => (ℒ n).restrictScalars R) k x a) =
      F.truncatedExpLieAction d ℒ k (d.truncatedRestrictScalarsEquiv (R := R) ℒ k x)
        (Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1)) a) := by
  let e := Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))
  let D := (F.restrictScalars R).truncatedLieAction d
    (fun n => (ℒ n).restrictScalars R) k x
  let E := F.truncatedLieAction d ℒ k (d.truncatedRestrictScalarsEquiv (R := R) ℒ k x)
  have hc : (e.conjAlgEquiv R) D = E.restrictScalars R := by
    ext b
    obtain ⟨a, rfl⟩ := e.surjective b
    simpa only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply, e, D, E] using
      F.restrictScalarsEquiv_truncatedLieAction d ℒ k x a
  have he := (IsNilpotent.map_exp
    ⟨k + 1, (F.restrictScalars R).truncatedLieAction_pow_eq_zero d
      (fun n => (ℒ n).restrictScalars R) k x⟩ (e.conjAlgEquiv R))
  rw [hc, ← Module.End.exp_restrictScalars E
    ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k _⟩] at he
  simpa only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply,
    truncatedExpLieAction_apply, e, D, E] using
    LinearMap.congr_fun he (e a)

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [IsScalarTower ℚ S L]

/-- The finite BCH actions agree after restricting both Lie and coefficient scalars. -/
theorem restrictScalarsEquiv_truncatedBCHAction (k : ℕ)
    (g : BCHGroup (d.truncatedLie (fun n => (ℒ n).restrictScalars R) k))
    (a : (F.restrictScalars R).quotient k) :
    Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1))
        ((F.restrictScalars R).truncatedBCHAction d
          (fun n => (ℒ n).restrictScalars R) k g a) =
      F.truncatedBCHAction d ℒ k
        ((d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.bchGroupMap g)
        (Submodule.Quotient.restrictScalarsEquiv R (F.submodule (k + 1)) a) := by
  simp only [truncatedBCHAction_apply, LieHom.log_bchGroupMap]
  exact F.restrictScalarsEquiv_truncatedExpLieAction d ℒ k (BCHGroup.log g) a

/-- The coefficient completion comparison intertwines the completed BCH representations. -/
@[simp]
theorem completionRestrictScalarsEquiv_completedBCHAction
    (g : d.completedBCHGroup (fun n => (ℒ n).restrictScalars R))
    (a : (F.restrictScalars R).completion) :
    F.completionRestrictScalarsEquiv R
        ((F.restrictScalars R).completedBCHAction d
          (fun n => (ℒ n).restrictScalars R) g a) =
      F.completedBCHAction d ℒ (d.completedBCHRestrictScalarsEquiv (R := R) ℒ g)
        (F.completionRestrictScalarsEquiv R a) := by
  apply F.completion_ext
  intro k
  simp only [projection_completionRestrictScalarsEquiv, projection_completedBCHAction,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv]
  exact F.restrictScalarsEquiv_truncatedBCHAction d ℒ k
    (CompletedGroup.projection k g) ((F.restrictScalars R).projection k a)

end Rational
end ModuleFiltration
end Mei

namespace Mei

/-- A filtration-raising action on an algebra remains filtration-raising over smaller scalars. -/
instance IsFiltrationRaising.restrictScalars_algebra
    {N R S L A : Type*} [AddCommMonoid N] [CommRing R] [CommRing S]
    [SMul R S] [LieRing L] [LieAlgebra S L] [LieAlgebra R L]
    [IsScalarTower R S L] [Ring A] [Algebra S A] [Algebra R A]
    [LieRingModule L A] (F : AlgFiltration A) (d : PositiveDegrees N)
    (ℒ : N → Submodule S L) [IsFiltrationRaising d ℒ (F.toModuleFiltration S)] :
    IsFiltrationRaising d (fun n => (ℒ n).restrictScalars R) (F.toModuleFiltration R) where
  lie_mem hx hm := IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ)
    (F := F.toModuleFiltration S)
    (by simpa only [PositiveDegrees.degreeSubmodule_restrictScalars,
      Submodule.restrictScalars_mem] using hx) hm

end Mei

namespace Mei.AlgFiltration

variable {N R S L A : Type*} [AddCommMonoid N] [CommRing R] [CommRing S]
  [Algebra R S] [LieRing L] [LieAlgebra S L] [LieAlgebra R L]
  [IsScalarTower R S L] [Ring A] [Algebra S A] [Algebra R A]
  [IsScalarTower R S A] [LieRingModule L A] [LieModule S L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule S L)
  [DecidableEq N] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration S)]

/-- Restricting scalars preserves the Lie representation on each coefficient algebra quotient. -/
@[simp]
theorem quotientLieAction_restrictScalars [DirectSum.Decomposition ℒ] (k : ℕ) (x : L) :
    F.quotientLieAction d (fun n => (ℒ n).restrictScalars R) k x =
      (F.quotientLieAction d ℒ k x).restrictScalars R := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp

variable [Algebra ℚ A] [IsDerivationAction L A]

/-- Restricting scalars preserves the finite exponential algebra automorphism. -/
@[simp]
theorem quotientExpLieAction_restrictScalars [DirectSum.Decomposition ℒ] (k : ℕ) (x : L) :
    F.quotientExpLieAction d (fun n => (ℒ n).restrictScalars R) k x =
      (F.quotientExpLieAction d ℒ k x).restrictScalars R := by
  ext a
  simp only [quotientExpLieAction_apply, AlgEquiv.restrictScalars_apply]
  rw [quotientLieAction_restrictScalars,
    ← Module.End.exp_restrictScalars (F.quotientLieAction d ℒ k x)
      ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩]
  rfl

variable [GradedLieAlgebra ℒ]

/-- The finite Lie quotient comparison identifies the exponential algebra actions. -/
@[simp]
theorem truncatedExpLieAction_restrictScalars (k : ℕ)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    F.truncatedExpLieAction d (fun n => (ℒ n).restrictScalars R) k x =
      (F.truncatedExpLieAction d ℒ k
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k x)).restrictScalars R := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).surjective_mkQ x
  simpa only [LieIdeal.mkQ_apply, truncatedExpLieAction_mk,
    PositiveDegrees.truncatedRestrictScalarsEquiv_mk] using
    F.quotientExpLieAction_restrictScalars d ℒ k x

variable [Algebra ℚ R] [Algebra ℚ S] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [IsScalarTower ℚ S L]

/-- The scalar-restriction group comparison identifies the finite BCH algebra actions. -/
theorem truncatedBCHAction_restrictScalars (k : ℕ)
    (g : BCHGroup (d.truncatedLie (fun n => (ℒ n).restrictScalars R) k)) :
    F.truncatedBCHAction d (fun n => (ℒ n).restrictScalars R) k g =
      (F.truncatedBCHAction d ℒ k
        ((d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.bchGroupMap
          g)).restrictScalars R := by
  ext a
  simp only [truncatedBCHAction_apply, AlgEquiv.restrictScalars_apply,
    LieHom.log_bchGroupMap]
  exact DFunLike.congr_fun (F.truncatedExpLieAction_restrictScalars d ℒ k (BCHGroup.log g)) a

/-- Scalar restriction identifies the completed BCH actions as algebra automorphisms. -/
@[simp]
theorem completedBCHAction_restrictScalars
    (g : d.completedBCHGroup (fun n => (ℒ n).restrictScalars R)) :
    F.completedBCHAction d (fun n => (ℒ n).restrictScalars R) g =
      (F.completedBCHAction d ℒ
        (d.completedBCHRestrictScalarsEquiv (R := R) ℒ g)).restrictScalars R := by
  apply AlgEquiv.ext
  intro a
  apply F.completion_ext
  intro k
  simp only [projection_completedBCHAction, AlgEquiv.restrictScalars_apply,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv]
  have h := DFunLike.congr_fun (F.truncatedBCHAction_restrictScalars d ℒ k
    (CompletedGroup.projection k g)) (F.projection k a)
  rw [F.truncatedBCHAction_apply d (fun n => (ℒ n).restrictScalars R) k
    (CompletedGroup.projection k g) (F.projection k a)] at h
  rw [AlgEquiv.restrictScalars_apply, F.truncatedBCHAction_apply d ℒ] at h
  exact h

end Mei.AlgFiltration
