/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Basic

/-!
# Completed sign factorization

The positive, zero and negative sign subgroups of a completed BCH group consist
of compatible families lying in the corresponding finite sign subgroups.
Multiplication in that order is a bijection onto the completed group. Its inverse
extracts the three factors and is computed by finite sign factorization at every
cutoff, including the middle factor used as a wall label.

For the attribution to Bridgeland's sign factorization, see the module docstring
of `Mei.Algebra.Lie.BCH.Sign.Basic`.

The construction assembles `Mei.PositiveDegrees.signFactorizationEquiv` using its
transition law. The carrier is the existing `Mei.completedGroup`; no additional
completeness or surjectivity assumption is required.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] (θ : N →+ A)
  (d : PositiveDegrees N) [IsPositiveGrading d ℒ]

/-- The subgroup whose logarithm has only degrees of the specified sign at
every finite cutoff. -/
def completedSignSubgroup (s : SignType) : Subgroup (d.completedBCHGroup ℒ) :=
  ⨅ k : ℕ, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup.comap
    (CompletedGroup.projection k)

/-- Membership in a completed sign subgroup is tested at every finite cutoff. -/
@[simp]
theorem mem_completedSignSubgroup (s : SignType) (g : d.completedBCHGroup ℒ) :
    g ∈ completedSignSubgroup ℒ θ d s ↔
      ∀ k, CompletedGroup.projection k g ∈
        (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup := by
  simp only [completedSignSubgroup, Subgroup.mem_iInf]
  exact forall_congr' fun k => Iff.rfl

private def completedSignFactor (g : d.completedBCHGroup ℒ) (s : SignType) :
    completedSignSubgroup ℒ θ d s :=
  ⟨⟨fun k => ((signFactorizationEquiv ℒ θ d k).symm (CompletedGroup.projection k g) s :
      d.truncatedGroup ℒ k), (mem_completedGroup_iff _ _).mpr (by
        intro k l h
        -- The categorical tower arrow has the concrete quotient BCH map as its homomorphism.
        change (d.truncationMap ℒ h).bchGroupMap
          ((signFactorizationEquiv ℒ θ d l).symm
            (CompletedGroup.projection l g) s : d.truncatedGroup ℒ l) =
          ((signFactorizationEquiv ℒ θ d k).symm
            (CompletedGroup.projection k g) s : d.truncatedGroup ℒ k)
        exact (truncationMap_signFactorizationEquiv_symm ℒ θ d h
          (CompletedGroup.projection l g) s).trans (congrArg (fun a =>
          ((signFactorizationEquiv ℒ θ d k).symm a s : d.truncatedGroup ℒ k))
          (CompletedGroup.map_projection k l h g)))⟩,
    (mem_completedSignSubgroup ℒ θ d s _).mpr (fun k => by
      rw [CompletedGroup.projection_apply]
      exact ((signFactorizationEquiv ℒ θ d k).symm
        (CompletedGroup.projection k g) s).property)⟩

private theorem projection_completedSignFactor (g : d.completedBCHGroup ℒ)
    (s : SignType) (k : ℕ) :
    CompletedGroup.projection k (completedSignFactor ℒ θ d g s : d.completedBCHGroup ℒ) =
      ((signFactorizationEquiv ℒ θ d k).symm (CompletedGroup.projection k g) s :
        d.truncatedGroup ℒ k) := by
  rw [CompletedGroup.projection_apply, completedSignFactor]

/-- Multiplication in positive-zero-negative order identifies the three completed
sign subgroups with the completed BCH group as sets. -/
def completedSignFactorizationEquiv :
    (∀ s, completedSignSubgroup ℒ θ d s) ≃ d.completedBCHGroup ℒ where
  toFun a := a .pos * a .zero * a .neg
  invFun := completedSignFactor ℒ θ d
  left_inv a := by
    funext s
    apply Subtype.ext
    apply CompletedGroup.ext
    intro k
    rw [projection_completedSignFactor]
    let b : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup := fun s =>
      ⟨CompletedGroup.projection k (a s : d.completedBCHGroup ℒ),
        (mem_completedSignSubgroup ℒ θ d s _).mp (a s).property k⟩
    have hb : (signFactorizationEquiv ℒ θ d k).symm
        (CompletedGroup.projection k ((a .pos : d.completedBCHGroup ℒ) *
          (a .zero : d.completedBCHGroup ℒ) * (a .neg : d.completedBCHGroup ℒ))) = b := by
      apply (signFactorizationEquiv ℒ θ d k).symm_apply_eq.mpr
      simp only [signFactorizationEquiv_apply, map_mul, b]
      rfl
    exact congrArg (fun a => (a s : d.truncatedGroup ℒ k)) hb
  right_inv g := by
    apply CompletedGroup.ext
    intro k
    simp only [map_mul, projection_completedSignFactor]
    have h := (signFactorizationEquiv ℒ θ d k).apply_symm_apply (CompletedGroup.projection k g)
    rw [signFactorizationEquiv_apply] at h
    exact h

/-- Completed recombination multiplies in positive-zero-negative order. -/
@[simp]
theorem completedSignFactorizationEquiv_apply (a : ∀ s, completedSignSubgroup ℒ θ d s) :
    completedSignFactorizationEquiv ℒ θ d a =
      (a .pos : d.completedBCHGroup ℒ) * a .zero * a .neg := (rfl)

/-- Each factor of a completed element projects to the corresponding finite factor. -/
@[simp]
theorem projection_completedSignFactorizationEquiv_symm (g : d.completedBCHGroup ℒ)
    (s : SignType) (k : ℕ) :
    CompletedGroup.projection k
        ((completedSignFactorizationEquiv ℒ θ d).symm g s : d.completedBCHGroup ℒ) =
      ((signFactorizationEquiv ℒ θ d k).symm (CompletedGroup.projection k g) s :
        d.truncatedGroup ℒ k) :=
  projection_completedSignFactor ℒ θ d g s k

/-- All three completed sign factors of the identity are identities. -/
@[simp]
theorem completedSignFactorizationEquiv_symm_one :
    (completedSignFactorizationEquiv ℒ θ d).symm 1 = 1 := by
  funext s
  apply Subtype.ext
  apply CompletedGroup.ext
  intro k
  rw [projection_completedSignFactorizationEquiv_symm]
  simp only [map_one, Pi.one_apply, OneMemClass.coe_one]
  exact congrArg (fun a => (a s : d.truncatedGroup ℒ k))
    (signFactorizationEquiv_symm_one ℒ θ d k)

end Mei.PositiveDegrees
