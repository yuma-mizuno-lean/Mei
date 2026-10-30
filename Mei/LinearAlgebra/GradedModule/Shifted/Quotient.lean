/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Component
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Homogeneous pieces of finite shifted coefficient modules

The relative-degree filtration of a shifted module is homogeneous, so each
finite quotient inherits its internal grading. Its degree-`n` piece is the
image of the original relative piece; it vanishes above the cutoff. Retained
homogeneous coefficients embed faithfully, and quotient transitions preserve
the homogeneous pieces. Projections in the inherited grading are the quotient
classes of the retained ambient components.

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

/-- Projection in the inherited quotient grading is the quotient class of the
retained ambient component. The relative degree is `n`, and its ambient degree
is `p + n`. -/
@[simp↓]
theorem decompose_shiftedQuotientGrading (k : ℕ) (n : d.monoid)
    (hn : d.degree n ≤ k) (x : (d.shiftedFiltration ℳ p).quotient k) :
    (DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece x n :
        (d.shiftedFiltration ℳ p).quotient k) =
      Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p n
        (d.shiftedQuotientComponent ℳ p (p + n) k (by simpa using hn) x)) := by
  obtain ⟨a, rfl⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective x
  simp only [Submodule.mkQ_apply, shiftedQuotientComponent_mk]
  have hproj := DirectSum.map_decompose_shift (shiftedGrading ℳ d.monoid p)
    (d.shiftedQuotientGrading ℳ p k).piece
    ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ.toAddMonoidHom
    id Function.injective_id
    (fun n a ha => (d.mem_shiftedQuotientGrading_iff ℳ p).mpr ⟨a, ha, rfl⟩) n a
  refine hproj.symm.trans (congrArg Submodule.Quotient.mk ?_)
  apply Subtype.ext
  simpa only [coe_shiftedInclusion] using coe_decompose_shiftedGrading ℳ d.monoid p a n

/-- The quotient image of a relative piece above the retained order vanishes.
This is the simplifier normal form of the finite-piece vanishing law. -/
@[simp]
theorem map_shiftedGrading_eq_bot {k : ℕ} {n : Γ} (hn : (k : ℤ) < d.degree n) :
    (shiftedGrading ℳ d.monoid p n).map
      ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ = ⊥ := by
  rw [← LinearMap.le_ker_iff_map, Submodule.ker_mkQ, shiftedFiltration_succ]
  exact d.le_degreeSubmodule _ hn

/-- Changing the cutoff preserves the ambient relative degree of every coefficient. -/
theorem transition_mem_shiftedQuotientGrading {k l : ℕ} (h : k ≤ l) {n : Γ}
    {x : (d.shiftedFiltration ℳ p).quotient l}
    (hx : x ∈ (d.shiftedQuotientGrading ℳ p l).piece n) :
    (d.shiftedFiltration ℳ p).transition h x ∈ (d.shiftedQuotientGrading ℳ p k).piece n := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  exact (d.mem_shiftedQuotientGrading_iff ℳ p).mpr ⟨a, ha, by simp⟩

end Mei.PositiveDegrees
