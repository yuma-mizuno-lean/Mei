/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Basic
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Homogeneous pieces of finite shifted coefficient modules

The relative-degree filtration of a shifted module is homogeneous, so each
finite quotient inherits its internal grading. Its degree-`n` piece is the
image of the original relative piece; it vanishes above the cutoff. Retained
homogeneous coefficients embed faithfully, and quotient transitions preserve
the homogeneous pieces.

The construction uses `TauCeti.InternalGrading.quotient` for the existing
shifted filtration, keeping the quotient carrier used by filtered Lie actions.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R M : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

/-- The internal relative grading of the existing order-`k` shifted module. -/
def shiftedQuotientGrading (k : ℕ) :
    TauCeti.InternalGrading R ((d.shiftedFiltration ℳ p).quotient k) Γ :=
  (TauCeti.InternalGrading.ofDecomposition (shiftedGrading ℳ d.monoid p)).quotient
    ((d.shiftedFiltration ℳ p).submodule (k + 1))
    (by simpa using d.shiftedFiltration_succ_isHomogeneous ℳ p k)

/-- A finite relative piece is the quotient image of its original piece. -/
@[simp]
theorem shiftedQuotientGrading_piece (k : ℕ) (n : Γ) :
    (d.shiftedQuotientGrading ℳ p k).piece n =
      (shiftedGrading ℳ d.monoid p n).map
        ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ := by
  unfold shiftedQuotientGrading
  rw [TauCeti.InternalGrading.quotient_piece,
    TauCeti.InternalGrading.ofDecomposition_piece]
  rfl

/-- A finite homogeneous coefficient has a homogeneous representative. -/
theorem mem_shiftedQuotientGrading_iff {k : ℕ} {n : Γ}
    {x : (d.shiftedFiltration ℳ p).quotient k} :
    x ∈ (d.shiftedQuotientGrading ℳ p k).piece n ↔
      ∃ a ∈ shiftedGrading ℳ d.monoid p n, Submodule.Quotient.mk a = x := by
  rw [shiftedQuotientGrading_piece]
  exact Submodule.mem_map

/-- The quotient image of a relative piece above the retained order vanishes.
This is the simplifier normal form of the finite-piece vanishing law. -/
@[simp]
theorem map_shiftedGrading_eq_bot {k : ℕ} {n : Γ} (hn : (k : ℤ) < d.degree n) :
    (shiftedGrading ℳ d.monoid p n).map
      ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ = ⊥ := by
  rw [← LinearMap.le_ker_iff_map, Submodule.ker_mkQ, shiftedFiltration_succ]
  exact d.le_degreeSubmodule _ hn

/-- Nonzero finite shifted homogeneous pieces have degrees in the positive
cutoff, even when the original ambient shift has negative degree. -/
theorem mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero
    {k : ℕ} {n : Γ} {a : (d.shiftedFiltration ℳ p).quotient k}
    (ha : a ∈ (d.shiftedQuotientGrading ℳ p k).piece n) (hne : a ≠ 0) :
    n ∈ d.cutoff k := by
  rw [d.mem_cutoff]
  constructor
  · by_contra hn
    simp only [shiftedQuotientGrading_piece,
      shiftedGrading_eq_bot ℳ d.monoid p hn, Submodule.map_bot, Submodule.mem_bot] at ha
    exact hne ha
  · by_contra hn
    rw [shiftedQuotientGrading_piece,
      d.map_shiftedGrading_eq_bot ℳ p (lt_of_not_ge hn), Submodule.mem_bot] at ha
    exact hne ha

/-- Changing the cutoff preserves the ambient relative degree of every coefficient. -/
theorem transition_mem_shiftedQuotientGrading {k l : ℕ} (h : k ≤ l) {n : Γ}
    {x : (d.shiftedFiltration ℳ p).quotient l}
    (hx : x ∈ (d.shiftedQuotientGrading ℳ p l).piece n) :
    (d.shiftedFiltration ℳ p).transition h x ∈ (d.shiftedQuotientGrading ℳ p k).piece n := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  exact (d.mem_shiftedQuotientGrading_iff ℳ p).mpr ⟨a, ha, by simp⟩

end Mei.PositiveDegrees
