/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Basic
public import Mathlib.Order.Preorder.Finite

/-! # Minimal containing cells

Every nonempty set contained in a cell of a finite polyhedral complex has a
unique smallest containing cell. Nonemptiness guarantees that intersections
of containing cells remain cells.
-/

public section

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A nonempty intersection of two cells is again a cell. -/
theorem inter_mem_cells (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hne : (P ∩ Q).Nonempty) :
    P ∩ Q ∈ C.cells :=
  C.face_closed P hP (P ∩ Q) (isPolyhedralFace_iff.mpr ⟨hne, C.inter_face P hP Q hQ hne⟩)

/-- Every nonempty set contained in a cell has a unique smallest containing cell. -/
theorem exists_unique_minimalContainingCell (C : FinitePolyhedralComplex h) {A : Set V}
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) :
    ∃! P : Set V, P ∈ C.cells ∧ A ⊆ P ∧ ∀ Q ∈ C.cells, A ⊆ Q → P ⊆ Q := by
  classical
  let S := C.cells.filter (fun P => A ⊆ P)
  have hS : S.Nonempty := by
    obtain ⟨P, hP, hAP⟩ := hcontained
    exact ⟨P, Finset.mem_filter.mpr ⟨hP, hAP⟩⟩
  obtain ⟨P, hP, hmin⟩ := S.exists_minimal hS
  obtain ⟨hPC, hAP⟩ := Finset.mem_filter.mp hP
  have hleast : ∀ Q ∈ C.cells, A ⊆ Q → P ⊆ Q := by
    intro Q hQ hAQ
    have hAPQ : A ⊆ P ∩ Q := fun x hx => ⟨hAP hx, hAQ hx⟩
    have hPQ : (P ∩ Q).Nonempty := hne.mono hAPQ
    have hmem : P ∩ Q ∈ S :=
      Finset.mem_filter.mpr ⟨C.inter_mem_cells hPC hQ hPQ, hAPQ⟩
    exact (hmin hmem Set.inter_subset_left).trans Set.inter_subset_right
  refine ⟨P, ⟨hPC, hAP, hleast⟩, ?_⟩
  intro Q hQ
  exact Set.Subset.antisymm (hQ.2.2 P hPC hAP) (hleast Q hQ.1 hQ.2.1)

/-- The actual smallest cell containing a nonempty set already contained in some cell. -/
noncomputable def minimalContainingCell (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) : Set V :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose

/-- The selected smallest containing cell belongs to the complex. -/
theorem minimalContainingCell_mem (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) :
    C.minimalContainingCell A hne hcontained ∈ C.cells :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose_spec.1.1

/-- The selected cell contains the prescribed set. -/
theorem subset_minimalContainingCell (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) :
    A ⊆ C.minimalContainingCell A hne hcontained :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose_spec.1.2.1

/-- The selected cell is contained in every other containing cell. -/
theorem minimalContainingCell_subset (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) {Q : Set V}
    (hQ : Q ∈ C.cells) (hAQ : A ⊆ Q) :
    C.minimalContainingCell A hne hcontained ⊆ Q :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose_spec.1.2.2 Q hQ hAQ

/-- Weak refinement carries a partial-order structure on actual complexes. -/
@[instance_reducible]
def weakRefinementPartialOrder : PartialOrder (FinitePolyhedralComplex h) where
  le := IsWeakRefinement
  le_refl := IsWeakRefinement.refl
  le_trans _ _ _ := IsWeakRefinement.trans
  le_antisymm _ _ := IsWeakRefinement.antisymm

/-- Subdivision carries its own partial-order structure, with support equality built in. -/
@[instance_reducible]
def subdivisionPartialOrder : PartialOrder (FinitePolyhedralComplex h) where
  le := IsSubdivision
  le_refl := IsSubdivision.refl
  le_trans _ _ _ := IsSubdivision.trans
  le_antisymm _ _ := IsSubdivision.antisymm

end Mei.FinitePolyhedralComplex
