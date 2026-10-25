/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Polyhedron.Face

/-!
# Rational presentations of polyhedral faces

Making selected inequalities active preserves rational normals: retain the
original rows and add their negatives at the selected indices. This also
preserves rational offsets when they are present.

The active-constraint classification of convex extreme subsets therefore gives
actual rational presentations of all faces. The argument does not assume that
an independently chosen exposing functional is rational. Arbitrary real offsets,
unbounded polyhedra and lineality are allowed.
-/

public section

namespace Mei.RationalAffinePolyhedron

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Impose equality in the selected rows by retaining the original inequalities
and adding their negatives, giving an actual finite rational-normal presentation. -/
noncomputable def activeFace (P : RationalAffinePolyhedron h)
    (I : Finset (Fin P.numConstraints)) : RationalAffinePolyhedron h :=
  ofFinite (Sum.elim P.inequality (fun j : I => -P.inequality j.val)) (by
    intro j
    cases j with
    | inl j => exact P.rational_linear j
    | inr j => exact (P.rational_linear j.val).neg)

/-- The active presentation is exactly the original carrier with all selected
inequalities made equalities. This statement does not require nonemptiness. -/
@[simp]
theorem carrier_activeFace (P : RationalAffinePolyhedron h)
    (I : Finset (Fin P.numConstraints)) :
    (P.activeFace I).carrier = {x : V | x ∈ P.carrier ∧ ∀ j ∈ I, P.inequality j x = 0} := by
  ext x
  rw [activeFace, mem_carrier_ofFinite]
  simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, ContinuousAffineMap.neg_apply,
    neg_nonpos, Set.mem_ofPred_eq, mem_carrier]
  constructor
  · rintro ⟨hx, hxI⟩
    exact ⟨hx, fun j hj => le_antisymm (hx j) (hxI ⟨j, hj⟩)⟩
  · rintro ⟨hx, hxI⟩
    exact ⟨hx, fun j => (hxI j.val j.property).ge⟩

/-- Active constraints preserve rational affine offsets because added rows are
negatives of existing rows. -/
theorem HasRationalOffsets.activeFace {P : RationalAffinePolyhedron h}
    (hP : P.HasRationalOffsets) (I : Finset (Fin P.numConstraints)) :
    (P.activeFace I).HasRationalOffsets := by
  rw [Mei.RationalAffinePolyhedron.activeFace]
  apply hasRationalOffsets_ofFinite
  intro j
  cases j with
  | inl j => exact hasRationalOffsets_iff.mp hP j
  | inr j =>
    obtain ⟨q, hq⟩ := hasRationalOffsets_iff.mp hP j.val
    refine ⟨-q, ?_⟩
    simp only [Sum.elim_inr, ContinuousAffineMap.neg_apply, hq, Rat.cast_neg]

/-- Every nonempty convex extreme subset of the carrier is the carrier of one
of its active rational-normal presentations. -/
theorem exists_activeFace_of_isExtreme (P : RationalAffinePolyhedron h) {F : Set V}
    (hF : IsExtreme ℝ P.carrier F) (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ I : Finset (Fin P.numConstraints), F = (P.activeFace I).carrier := by
  have hcarrier : P.carrier = {x : V | ∀ j, P.inequality j x ≤ 0} :=
    Set.ext fun _ => mem_carrier
  rw [hcarrier] at hF
  obtain ⟨I, hI⟩ := hF.eq_setOf_active (fun j => (P.inequality j).toAffineMap) hconv hne
  refine ⟨I, ?_⟩
  rw [carrier_activeFace]
  simpa only [mem_carrier, ContinuousAffineMap.coe_toAffineMap] using hI

/-- An active presentation is an exposed subset of the original carrier. The
empty subset is included according to Mathlib's exposed-set convention. -/
theorem isExposed_activeFace (P : RationalAffinePolyhedron h)
    (I : Finset (Fin P.numConstraints)) :
    IsExposed ℝ P.carrier (P.activeFace I).carrier := by
  have hcarrier : P.carrier = {x : V | ∀ j, P.inequality j x ≤ 0} :=
    Set.ext fun _ => mem_carrier
  rw [carrier_activeFace, hcarrier]
  exact Mei.Convex.isExposed_setOf_active P.inequality I

end Mei.RationalAffinePolyhedron

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A constant contradictory row gives an empty presentation with rational offsets. -/
theorem IsRationalPolyhedron.empty (h : TauCeti.Toric.IsIntegralLattice i) :
    IsRationalPolyhedron h (∅ : Set V) := by
  exact isRationalPolyhedron_iff.mpr
    ⟨RationalAffinePolyhedron.empty h, RationalAffinePolyhedron.carrier_empty h,
      RationalAffinePolyhedron.hasRationalOffsets_empty h⟩

/-- Every convex extreme subset of a rational-normal polyhedron is
rational-normal, including the empty subset. -/
theorem _root_.IsExtreme.isRationalNormalPolyhedron {P F : Set V}
    (hF : IsExtreme ℝ P F) (hP : IsRationalNormalPolyhedron h P) (hconv : Convex ℝ F) :
    IsRationalNormalPolyhedron h F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact isRationalNormalPolyhedron_iff.mpr
      ⟨RationalAffinePolyhedron.empty h, RationalAffinePolyhedron.carrier_empty h⟩
  obtain ⟨Q, hQ⟩ := isRationalNormalPolyhedron_iff.mp hP
  rw [← hQ] at hF
  obtain ⟨I, hI⟩ := Q.exists_activeFace_of_isExtreme hF hconv hne
  exact isRationalNormalPolyhedron_iff.mpr ⟨Q.activeFace I, hI.symm⟩

/-- Every convex extreme subset of a polyhedron with rational normals and
rational offsets has both properties. No rational exposing functional is assumed. -/
theorem _root_.IsExtreme.isRationalPolyhedron {P F : Set V}
    (hF : IsExtreme ℝ P F) (hP : IsRationalPolyhedron h P) (hconv : Convex ℝ F) :
    IsRationalPolyhedron h F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact IsRationalPolyhedron.empty h
  obtain ⟨Q, hQ, hQrational⟩ := isRationalPolyhedron_iff.mp hP
  rw [← hQ] at hF
  obtain ⟨I, hI⟩ := Q.exists_activeFace_of_isExtreme hF hconv hne
  exact isRationalPolyhedron_iff.mpr ⟨Q.activeFace I, hI.symm, hQrational.activeFace I⟩

end Mei
