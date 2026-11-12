/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.LinearAlgebra.GradedCorrespondence.Hom
public import Mei.LinearAlgebra.GradedCorrespondence.Terminal

/-!
# Finite shifted wall actions as graded correspondences

Each finite BCH action on shifted coefficients defines the graph correspondence
of its linear equivalence. Its transfers are the selected homogeneous components
of the action. Changing the cutoff gives a morphism of these correspondences,
including compatibility of the chosen inverse lifts.
The same coefficient truncation commutes with both terminal chamber totals,
by the generic naturality of the homogeneous graph construction.

Thus either sign of a wall label can be used on the same finite coefficient
modules. The construction reuses `GradedCorrespondence.graph` and the existing
finite BCH action and its truncation naturality theorem.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ : Type} {R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)

/-- The graph of the finite BCH action on a shifted coefficient module.
Taking the inverse label gives the opposite sign of the ordinary wall action. -/
abbrev shiftedBCHCorrespondence (k : ℕ) (g : BCHGroup (d.lieTruncation ℒ k)) :
    GradedCorrespondence (B := (d.shiftedLieFiltration ℒ ℳ p).quotient k)
      (d.shiftedQuotientGrading ℳ p k).piece (d.shiftedQuotientGrading ℳ p k).piece
      Set.univ Set.univ :=
  GradedCorrespondence.graph
    (d.shiftedQuotientGrading ℳ p k).piece (d.shiftedQuotientGrading ℳ p k).piece
    ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k g)

/-- Coefficient truncation is a morphism of the graph correspondences of compatible
finite wall labels. It intertwines both forward transfers and inverse lifts. -/
def shiftedBCHCorrespondenceHom {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.lieTruncation ℒ l)) :
    GradedCorrespondence.Hom (d.shiftedBCHCorrespondence ℒ ℳ p l g)
      (d.shiftedBCHCorrespondence ℒ ℳ p k ((d.lieTruncationMap ℒ h).bchGroupMap g)) id id where
  middle := (d.shiftedLieFiltration ℒ ℳ p).transition h
  left := (d.shiftedLieFiltration ℒ ℳ p).transition h
  right := (d.shiftedLieFiltration ℒ ℳ p).transition h
  left_comm := by simp
  right_comm := by
    apply LinearMap.ext
    intro a
    simpa only [LinearMap.comp_apply, GradedCorrespondence.graph_right,
      LinearEquiv.coe_coe] using
      (d.shiftedLieFiltration ℒ ℳ p).transition_truncatedBCHAction d ℒ h g a
  left_mem n a ha := d.transition_mem_shiftedQuotientGrading ℳ p h ha
  right_mem n a ha := d.transition_mem_shiftedQuotientGrading ℳ p h ha
  admissible_left _ _ := trivial
  admissible_right _ _ := trivial
  middle_liftLeft _ _ := by
    simp only [shiftedBCHCorrespondence, GradedCorrespondence.graph_liftLeft,
      Submodule.subtype_apply]
  middle_liftRight j a := by
    apply ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
      ((d.lieTruncationMap ℒ h).bchGroupMap g)).injective
    simpa only [shiftedBCHCorrespondence, GradedCorrespondence.graph_liftRight,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      LinearEquiv.apply_symm_apply] using
      ((d.shiftedLieFiltration ℒ ℳ p).transition_truncatedBCHAction d ℒ h g
        (((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ l g).symm a)).symm

/-- The middle map of the cutoff comparison is coefficient truncation. -/
@[simp]
theorem shiftedBCHCorrespondenceHom_middle {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.lieTruncation ℒ l)) :
    (d.shiftedBCHCorrespondenceHom ℒ ℳ p h g).middle =
      (d.shiftedLieFiltration ℒ ℳ p).transition h := (rfl)

/-- The left chamber map of the cutoff comparison is coefficient truncation. -/
@[simp]
theorem shiftedBCHCorrespondenceHom_left {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.lieTruncation ℒ l)) :
    (d.shiftedBCHCorrespondenceHom ℒ ℳ p h g).left =
      (d.shiftedLieFiltration ℒ ℳ p).transition h := (rfl)

/-- The right chamber map of the cutoff comparison is coefficient truncation. -/
@[simp]
theorem shiftedBCHCorrespondenceHom_right {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.lieTruncation ℒ l)) :
    (d.shiftedBCHCorrespondenceHom ℒ ℳ p h g).right =
      (d.shiftedLieFiltration ℒ ℳ p).transition h := (rfl)

/-- Cutting off coefficients commutes with the negative-side terminal total
for a compatible finite BCH wall label, including mixed normal signs. -/
theorem transition_terminalGraphLift_shiftedBCHAction {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.lieTruncation ℒ l)) (w : Γ → ℤ) :
    ((d.shiftedLieFiltration ℒ ℳ p).transition h).comp
        (GradedCorrespondence.terminalGraphLift (d.shiftedQuotientGrading ℳ p l).piece
          ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ l g) w) =
      (GradedCorrespondence.terminalGraphLift (d.shiftedQuotientGrading ℳ p k).piece
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
          ((d.lieTruncationMap ℒ h).bchGroupMap g)) w).comp
            ((d.shiftedLieFiltration ℒ ℳ p).transition h) := by
  refine GradedCorrespondence.terminalGraphLift_naturality
    _ _ w _ _ w _ id ?_ ?_ (fun _ => Iff.rfl)
  · intro i a ha
    exact d.transition_mem_shiftedQuotientGrading ℳ p h ha
  · exact LinearMap.ext
      ((d.shiftedLieFiltration ℒ ℳ p).transition_truncatedBCHAction d ℒ h g)

/-- Cutting off coefficients commutes with the positive-side terminal total
for a compatible finite BCH wall label, including mixed normal signs. -/
theorem transition_terminalGraphRight_shiftedBCHAction {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.lieTruncation ℒ l)) (w : Γ → ℤ) :
    ((d.shiftedLieFiltration ℒ ℳ p).transition h).comp
        (GradedCorrespondence.terminalGraphRight (d.shiftedQuotientGrading ℳ p l).piece
          ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ l g) w) =
      (GradedCorrespondence.terminalGraphRight (d.shiftedQuotientGrading ℳ p k).piece
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
          ((d.lieTruncationMap ℒ h).bchGroupMap g)) w).comp
            ((d.shiftedLieFiltration ℒ ℳ p).transition h) := by
  refine GradedCorrespondence.terminalGraphRight_naturality
    _ _ w _ _ w _ id ?_ ?_ (fun _ => Iff.rfl)
  · intro i a ha
    exact d.transition_mem_shiftedQuotientGrading ℳ p h ha
  · exact LinearMap.ext
      ((d.shiftedLieFiltration ℒ ℳ p).transition_truncatedBCHAction d ℒ h g)

end TauCeti.PositiveDegrees
