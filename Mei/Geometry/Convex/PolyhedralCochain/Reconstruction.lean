/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.NormalForm
public import Mei.Geometry.Convex.PolyhedralCochain.Differential

/-!
# Reconstructing cochains from isolating pairings

One transverse test meeting each cell of a finite complex and missing all other
cells of the same codimension determines every cochain presented on that complex.
The intersection index, which is `1` or `-1`, converts each pairing back to the
chosen cell orientation. Thus local pairing identities assemble into equality
of cochains, including orientation and subdivision relations.

In particular, the signed boundary of a presentation can be identified with a
prescribed cochain by one test per cell of the next codimension. This is useful
when local Stokes formulas compute those tests independently. Coefficients may
have torsion; no division or determinant magnitude is used.

The reconstruction uses `PolyhedralCochain.intersectionPairing_eq_sum_sub_reverse`
and `PolyhedralCochain.sum_mk_eq_zero_iff`. The required geometric tests exist by
`OrientedCell.exists_isolating_transverse_test`.
-/

public section

noncomputable section

open Set

namespace Mei.PolyhedralCochain

variable {N V R E : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}
  (C : FinitePolyhedralComplex h) [Fintype (C.cellsOfCodimension k)]
  (σ : C.cellsOfCodimension k → OrientedCell h k)
  (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
  (f : OrientedCell h k →₀ E)
  (hf : ∀ τ ∈ f.support, τ.carrier ∈ C.cells)

include hσ hf

omit [Fintype (C.cellsOfCodimension k)] in
/-- A test isolating one cell reads its signed coefficient, even if the
presentation uses both orientations. No transversality is needed for this
evaluation formula. -/
theorem intersectionPairing_eq_index_smul_sub_reverse_of_isolating
    (Q : C.cellsOfCodimension k) (v : Fin (k + 1) → V)
    (ho : ∀ P : C.cellsOfCodimension k, P ≠ Q →
      Disjoint (convexHull ℝ (range v)) (P : Set V)) :
    OrientedCell.intersectionPairing (R := R) v f =
      (σ Q).intersectionIndex v • (f (σ Q) - f (σ Q).reverse) := by
  classical
  let := Fintype.ofFinite (C.cellsOfCodimension k)
  rw [intersectionPairing_eq_sum_sub_reverse C σ hσ f hf]
  exact Finset.sum_eq_single Q (fun P _ hPQ => by
    rw [OrientedCell.intersectionIndex_of_disjoint (hσ P ▸ ho P hPQ), zero_smul])
    (by simp)

variable (v : C.cellsOfCodimension k → Fin (k + 1) → V)
  (ht : ∀ Q, (σ Q).IsTransverse (v Q))
  (hm : ∀ Q, (convexHull ℝ (range (v Q)) ∩ (Q : Set V)).Nonempty)
  (ho : ∀ Q P : C.cellsOfCodimension k, P ≠ Q →
    Disjoint (convexHull ℝ (range (v Q))) (P : Set V))

include ht hm ho

/-- Recover a cochain from one isolating transverse pairing per cell.
Multiplication by the intersection sign corrects an arbitrarily oriented test,
so the formula works also with torsion coefficients. -/
theorem ofFinsupp_eq_sum_intersectionPairing_of_isolating :
    ofFinsupp (R := R) f = ∑ Q, mk (σ Q)
      ((σ Q).intersectionIndex (v Q) • OrientedCell.intersectionPairing (R := R) (v Q) f) := by
  classical
  rw [ofFinsupp_eq_sum_sub_reverse C σ hσ f hf]
  apply Finset.sum_congr rfl
  intro Q _
  rw [intersectionPairing_eq_index_smul_sub_reverse_of_isolating C σ hσ f hf Q (v Q) (ho Q)]
  rcases (ht Q).intersectionIndex_eq_one_or_neg_one (hσ Q ▸ hm Q) with hi | hi
  · simp only [hi, one_smul]
  · simp only [hi, neg_smul, one_smul, neg_neg]

/-- Equality with specified cell coefficients is equivalent to the corresponding
identities for one isolating transverse pairing per cell. The tests may have
either orientation. -/
theorem ofFinsupp_eq_sum_mk_iff_isolating_pairings (c : C.cellsOfCodimension k → E) :
    ofFinsupp (R := R) f = ∑ Q, mk (σ Q) (c Q) ↔
      ∀ Q, OrientedCell.intersectionPairing (R := R) (v Q) f =
        (σ Q).intersectionIndex (v Q) • c Q := by
  classical
  have hcoeff : ofFinsupp (R := R) f = ∑ Q, mk (σ Q) (c Q) ↔
      ∀ Q, f (σ Q) - f (σ Q).reverse = c Q := by
    rw [ofFinsupp_eq_sum_sub_reverse C σ hσ f hf, ← sub_eq_zero,
      ← Finset.sum_sub_distrib]
    simp only [← map_sub]
    rw [sum_mk_eq_zero_iff C σ hσ]
    simp only [sub_eq_zero]
  rw [hcoeff]
  apply forall_congr'
  intro Q
  rw [intersectionPairing_eq_index_smul_sub_reverse_of_isolating C σ hσ f hf Q (v Q) (ho Q)]
  rcases (ht Q).intersectionIndex_eq_one_or_neg_one (hσ Q ▸ hm Q) with hi | hi
  · simp only [hi, one_smul]
  · simp only [hi, neg_smul, one_smul, neg_inj]

section Coboundary

variable {C}
omit hσ ht hm ho [Fintype (C.cellsOfCodimension k)] in
/-- Identify the entire coboundary by one isolating transverse test per cell
of the next codimension. The source may have repeated or oppositely oriented
contributions. Equality is in cochains, rather than in formal presentations. -/
theorem coboundary_eq_sum_mk_iff_isolating_pairings
    [Fintype (C.cellsOfCodimension (k + 1))]
    (τ : C.cellsOfCodimension (k + 1) → OrientedCell h (k + 1))
    (hτ : ∀ Q, (τ Q).carrier = (Q : Set V))
    (w : C.cellsOfCodimension (k + 1) → Fin (k + 2) → V)
    (htw : ∀ Q, (τ Q).IsTransverse (w Q))
    (hmw : ∀ Q, (convexHull ℝ (range (w Q)) ∩ (Q : Set V)).Nonempty)
    (how : ∀ Q P : C.cellsOfCodimension (k + 1), P ≠ Q →
      Disjoint (convexHull ℝ (range (w Q))) (P : Set V))
    (c : C.cellsOfCodimension (k + 1) → E) :
    coboundary (ofFinsupp (R := R) f) = ∑ Q, mk (τ Q) (c Q) ↔
      ∀ Q, OrientedCell.intersectionPairing (R := R) (w Q)
          (coboundaryPresentation (R := R) f) = (τ Q).intersectionIndex (w Q) • c Q := by
  have hboundary (υ) (hυ : υ ∈ (coboundaryPresentation (R := R) f).support) :
      υ.carrier ∈ C.cells :=
    ((C.mem_cellsOfCodimension (k + 1) _).mp
      (mem_cellsOfCodimension_of_mem_support_coboundaryPresentation (R := R) C f hf hυ)).1
  simpa only [ofFinsupp_coboundaryPresentation, coboundary_ofFinsupp] using
    ofFinsupp_eq_sum_mk_iff_isolating_pairings (R := R) C τ hτ
      (coboundaryPresentation (R := R) f) hboundary w htw hmw how c

end Coboundary

end Mei.PolyhedralCochain
