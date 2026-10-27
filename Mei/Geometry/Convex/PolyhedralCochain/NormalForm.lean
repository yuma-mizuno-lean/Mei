/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Separation

/-!
# Signed coefficients on a finite polyhedral complex

A finite presentation supported on cells of a fixed complex may use both
orientations of each cell. Choosing one orientation per cell combines these
contributions by subtracting the coefficient of the reversed orientation.
These signed coefficients determine the cochain, and vanish exactly when it
represents zero. Transverse affine tests detect zero for these arbitrary
presentations, without requiring their orientations to agree in advance.

This supplies the orientation grouping needed after geometric common refinement.
It uses `OrientedCell.eq_or_eq_reverse_of_carrier_eq`,
`PolyhedralCochain.sum_mk_eq_zero_iff` and
`OrientedCell.exists_isolating_transverse_test`. The normal-quotient orientation
dichotomy ultimately comes from Mathlib's `Orientation.eq_or_eq_neg`.
-/

public section

noncomputable section

open Set Module

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  (C : FinitePolyhedralComplex h) [Fintype (C.cellsOfCodimension k)]
  (σ : C.cellsOfCodimension k → OrientedCell h k)
  (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))

section

variable {E : Type*} [AddCommMonoid E]
  (f : OrientedCell h k →₀ E)
  (hf : ∀ τ ∈ f.support, τ.carrier ∈ C.cells)

include hσ hf

/-- A presentation on a complex splits into its two oriented coefficients on
each geometric cell. In particular no incidence multiplicity is discarded. -/
theorem eq_sum_single_add_single_reverse :
    f = ∑ Q, (Finsupp.single (σ Q) (f (σ Q)) +
      Finsupp.single (σ Q).reverse (f (σ Q).reverse)) := by
  classical
  ext τ
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.add_apply]
  by_cases hτ : τ.carrier ∈ C.cells
  · let Q : C.cellsOfCodimension k :=
      ⟨τ.carrier, (C.mem_cellsOfCodimension k _).mpr ⟨hτ, τ.finrank_direction_add⟩⟩
    rw [Finset.sum_eq_single Q]
    · rcases τ.eq_or_eq_reverse_of_carrier_eq (σ Q) (hσ Q).symm with he | he
      · rw [he]
        simp [OrientedCell.reverse_ne_self]
      · rw [he]
        simp [OrientedCell.reverse_ne_self]
    · intro P _ hPQ
      have hne : τ ≠ σ P := by
        intro he
        apply hPQ
        apply Subtype.ext
        exact (hσ P).symm.trans (congrArg OrientedCell.carrier he).symm
      have hnerev : τ ≠ (σ P).reverse := by
        intro he
        apply hPQ
        apply Subtype.ext
        exact (hσ P).symm.trans
          ((congrArg OrientedCell.carrier he).trans (σ P).reverse_carrier).symm
      simp [Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hnerev]
    · simp
  · have hz : f τ = 0 := by
      by_contra hne
      exact hτ (hf τ (Finsupp.mem_support_iff.mpr hne))
    rw [hz, eq_comm]
    apply Finset.sum_eq_zero
    intro Q _
    have hne : τ ≠ σ Q := fun he => hτ (he ▸ hσ Q ▸
      ((C.mem_cellsOfCodimension k Q).mp Q.property).1)
    have hnerev : τ ≠ (σ Q).reverse := fun he => hτ (by
      rw [he, OrientedCell.reverse_carrier, hσ Q]
      exact ((C.mem_cellsOfCodimension k Q).mp Q.property).1)
    simp [Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hnerev]

end

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]
  (f : OrientedCell h k →₀ E)
  (hf : ∀ τ ∈ f.support, τ.carrier ∈ C.cells)

include hσ hf

/-- On a fixed complex the signed coefficient is the coefficient of the chosen
orientation minus that of its reverse. These coefficients give a canonical
presentation of the cochain. -/
theorem ofFinsupp_eq_sum_sub_reverse :
    ofFinsupp (R := R) f = ∑ Q, mk (σ Q) (f (σ Q) - f (σ Q).reverse) := by
  conv_lhs => rw [eq_sum_single_add_single_reverse C σ hσ f hf]
  simp only [map_sum, map_add, ofFinsupp_single, mk_reverse, sub_eq_add_neg, map_neg]

omit [Fintype (C.cellsOfCodimension k)] in
/-- A presentation on a fixed complex represents zero exactly when its two
oriented coefficients agree on every cell. -/
theorem ofFinsupp_eq_zero_iff_eq_reverse :
    ofFinsupp (R := R) f = 0 ↔ ∀ Q, f (σ Q) = f (σ Q).reverse := by
  let := Fintype.ofFinite (C.cellsOfCodimension k)
  rw [ofFinsupp_eq_sum_sub_reverse C σ hσ f hf, sum_mk_eq_zero_iff C σ hσ]
  simp only [sub_eq_zero]

/-- The same signed coefficients compute every intersection pairing, including
for tests that are not transverse. -/
theorem intersectionPairing_eq_sum_sub_reverse (v : Fin (k + 1) → V) :
    OrientedCell.intersectionPairing (R := R) v f =
      ∑ Q, (σ Q).intersectionIndex v • (f (σ Q) - f (σ Q).reverse) := by
  conv_lhs => rw [eq_sum_single_add_single_reverse C σ hσ f hf]
  simp only [map_sum, map_add, OrientedCell.intersectionPairing_single,
    OrientedCell.intersectionIndex_reverse, neg_smul, sub_eq_add_neg, smul_add, smul_neg]

omit [Fintype (C.cellsOfCodimension k)] in
/-- Transverse tests detect zero for any presentation on a finite complex,
including presentations containing both orientations of the same cell. It
suffices to test simplices lying in balls of any prescribed positive radius. -/
theorem ofFinsupp_eq_zero_iff_intersectionPairing_eq_zero {ε : ℝ} (hε : 0 < ε) :
    ofFinsupp (R := R) f = 0 ↔
      ∀ (p : V) (v : Fin (k + 1) → V),
        convexHull ℝ (range v) ⊆ Metric.ball p ε →
        (∀ τ ∈ f.support, τ.IsTransverse v) →
        OrientedCell.intersectionPairing (R := R) v f = 0 := by
  classical
  let := Fintype.ofFinite (C.cellsOfCodimension k)
  have := h.finiteDimensional
  constructor
  · intro hz p v _ hv
    simpa only [map_zero] using
      intersectionPairing_eq_of_ofFinsupp_eq (hz.trans (map_zero _).symm) hv
        (by simp : ∀ τ ∈ (0 : OrientedCell h k →₀ E).support, τ.IsTransverse v)
  · intro htest
    rw [ofFinsupp_eq_zero_iff_eq_reverse C σ hσ f hf]
    intro Q
    have hQC := ((C.mem_cellsOfCodimension k Q).mp Q.property).1
    obtain ⟨p, hp⟩ := (C.nonempty Q hQC).intrinsicInterior
      (C.isConvexPolyhedron hQC).convex
    obtain ⟨s, htrans, hball, hmeet, _, hother⟩ := (σ Q).exists_isolating_transverse_test C
      (hσ Q ▸ hQC) (hσ Q ▸ hp) hε
    have hdisj (P : C.cellsOfCodimension k) (hne : P ≠ Q) :
        Disjoint (convexHull ℝ (range s.points)) (σ P).carrier := by
      rw [hσ P]
      exact hother P P.property (by rw [hσ Q]; exact Subtype.coe_ne_coe.mpr hne)
    have hall : ∀ τ ∈ f.support, τ.IsTransverse s.points := by
      intro τ hτ
      let P : C.cellsOfCodimension k := ⟨τ.carrier,
        (C.mem_cellsOfCodimension k _).mpr ⟨hf τ hτ, τ.finrank_direction_add⟩⟩
      by_cases hPQ : P = Q
      · have hc : τ.carrier = (σ Q).carrier :=
          (congrArg Subtype.val hPQ).trans (hσ Q).symm
        rcases τ.eq_or_eq_reverse_of_carrier_eq (σ Q) hc with he | he
        · exact he ▸ htrans
        · rw [he, OrientedCell.isTransverse_reverse_iff]
          exact htrans
      · apply τ.isTransverse_of_disjoint
        simpa only [hσ P] using hdisj P hPQ
    have hz := htest p s.points hball hall
    rw [intersectionPairing_eq_sum_sub_reverse C σ hσ f hf,
      Finset.sum_eq_single Q (fun P _ hPQ => by
        rw [OrientedCell.intersectionIndex_of_disjoint (hdisj P hPQ), zero_smul])
        (by simp)] at hz
    rcases htrans.intersectionIndex_eq_one_or_neg_one
      (hmeet ▸ singleton_nonempty p) with hi | hi
    · simpa only [hi, one_smul, sub_eq_zero] using hz
    · simpa only [hi, neg_smul, one_smul, neg_eq_zero, sub_eq_zero] using hz

end Mei.PolyhedralCochain
