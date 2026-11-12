/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Component

/-!
# Reconstruction of shifted coefficients from ambient homogeneous components

A family of ambient homogeneous coefficients that vanishes outside a translate of
the positive monoid determines a unique shifted completed coefficient. The inverse
is the existing product comparison for the relative grading, so reconstruction
uses the original completion carrier and its finite-cutoff interpretation.
-/

public section

open TauCeti (PositiveDegrees)
noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

private def shiftedFamily (x : ∀ q, ℳ q)
    (hx : ∀ q, q - p ∉ d.monoid → x q = 0) (n : Γ) :
    shiftedGrading ℳ d.monoid p n := by
  have hmem : (x (p + n) : M) ∈ shiftedSubmodule ℳ d.monoid p := by
    by_cases hn : n ∈ d.monoid
    · exact le_shiftedSubmodule ℳ d.monoid p hn (x (p + n)).property
    · have hz := hx (p + n) (by simpa only [add_sub_cancel_left] using hn)
      rw [hz, Submodule.coe_zero]
      exact Submodule.zero_mem _
  exact ⟨⟨x (p + n), hmem⟩, (mem_shiftedGrading ℳ d.monoid p).mpr (x (p + n)).property⟩

/-- Reconstruct a shifted completion from a family vanishing outside its translated support. -/
def shiftedCoefficientsOfComponents (x : ∀ q, ℳ q)
    (hx : ∀ q, q - p ∉ d.monoid → x q = 0) : d.ShiftedCoefficients ℳ p :=
  (d.completionEquivPi (shiftedGrading ℳ d.monoid p) (d.shiftedFiltration ℳ p)
    (d.shiftedFiltration_succ ℳ p) (fun _ hn => shiftedGrading_eq_bot ℳ d.monoid p hn)).symm
      (shiftedFamily d ℳ p x hx)

/-- Reconstruction has the prescribed ambient homogeneous components. -/
@[simp]
theorem shiftedHomogeneousComponent_ofComponents (x : ∀ q, ℳ q)
    (hx : ∀ q, q - p ∉ d.monoid → x q = 0) (q : Γ) :
    d.shiftedHomogeneousComponent ℳ p q (d.shiftedCoefficientsOfComponents ℳ p x hx) =
      x q := by
  apply Subtype.ext
  have he : p + (q - p) = q := by abel_nf
  calc
    _ = (d.shiftedHomogeneousComponent ℳ p (p + (q - p))
        (d.shiftedCoefficientsOfComponents ℳ p x hx) : M) := by rw [he]
    _ = ((d.completionComponent (shiftedGrading ℳ d.monoid p) (d.shiftedFiltration ℳ p)
        (d.shiftedFiltration_succ ℳ p) (q - p)
        (d.shiftedCoefficientsOfComponents ℳ p x hx) : shiftedSubmodule ℳ d.monoid p) : M) :=
      (d.coe_completionComponent_shiftedGrading ℳ p (q - p) _).symm
    _ = (x (p + (q - p)) : M) := by
      rw [shiftedCoefficientsOfComponents, completionComponent_completionEquivPi_symm]
      rfl
    _ = (x q : M) := congrArg (fun u => (x u : M)) he

/-- Reconstructing the homogeneous components of a completed coefficient returns it. -/
@[simp]
theorem shiftedCoefficientsOfComponents_homogeneous (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedCoefficientsOfComponents ℳ p (fun q => d.shiftedHomogeneousComponent ℳ p q x)
      (fun _ hq => d.shiftedHomogeneousComponent_eq_zero ℳ p hq x) = x := by
  apply d.shiftedCoefficients_ext ℳ p
  intro q
  exact d.shiftedHomogeneousComponent_ofComponents ℳ p _ _ q

/-- A supported family is realized by exactly one completed shifted coefficient. -/
theorem existsUnique_shiftedCoefficients_components (x : ∀ q, ℳ q)
    (hx : ∀ q, q - p ∉ d.monoid → x q = 0) :
    ∃! a : d.ShiftedCoefficients ℳ p, ∀ q, d.shiftedHomogeneousComponent ℳ p q a = x q := by
  refine ⟨d.shiftedCoefficientsOfComponents ℳ p x hx, ?_, ?_⟩
  · intro q
    exact d.shiftedHomogeneousComponent_ofComponents ℳ p x hx q
  · intro a ha
    apply d.shiftedCoefficients_ext ℳ p
    intro q
    exact (ha q).trans (d.shiftedHomogeneousComponent_ofComponents ℳ p x hx q).symm

end TauCeti.PositiveDegrees
