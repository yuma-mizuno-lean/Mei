/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Pairing
public import Mei.Geometry.Convex.PolyhedralComplex.Strata

/-!
# Local evaluation of a cell presentation

Near a relative interior point of a cell of a finite complex, every sufficiently
small transverse affine test containing that point pairs with the presentation
of cells of the same codimension by extracting its coefficient, with the
orientation sign. The radius works for every such test and every coefficient
family. All cells in the presentation are transverse to the test, so the
pairing also respects cochain relations.

The neighborhood is supplied by `FinitePolyhedralComplex.exists_isolating_ball`.
The sign and transversality use `OrientedCell.intersectionIndex` and the conormal
normal-quotient criterion `Module.Ray.IsConormal.evalSign_ne_zero_iff`.
This local evaluation connects geometric wall coefficients to transport defects.
-/

public section

noncomputable section

open Set Module

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Near a cell interior point, an affine test containing that point with nonzero
oriented normal evaluation is transverse to every cell of the same codimension.
Its pairing with any indexed presentation of those cells is the selected
coefficient times that sign. The neighborhood is independent of the coefficient
family and of the test. -/
theorem exists_ball_intersectionPairing_eq (C : FinitePolyhedralComplex h) {k : ℕ}
    (σ : C.cellsOfCodimension k → OrientedCell h k)
    (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
    (Q : C.cellsOfCodimension k) {q : V} (hq : q ∈ intrinsicInterior ℝ (Q : Set V)) :
    ∃ ε > 0, ∀ {v : Fin (k + 1) → V}, (∀ j, v j ∈ Metric.ball q ε) →
      q ∈ convexHull ℝ (range v) →
      (σ Q).orientation.evalSign (fun j : Fin k => v j.succ - v 0) ≠ 0 →
      (∀ P, (σ P).IsTransverse v) ∧
      ∀ c : C.cellsOfCodimension k → E,
        OrientedCell.intersectionPairing (R := R) v
          (∑ P, Finsupp.single (σ P) (c P)) =
            ((σ Q).orientation.evalSign (fun j : Fin k => v j.succ - v 0) : ℤ) • c Q := by
  classical
  have := h.finiteDimensional
  obtain ⟨ε, hε, _, hfront, hother, _⟩ := C.exists_isolating_ball Q.property hq
  refine ⟨ε, hε, fun {v} hv hqv hsign => ?_⟩
  have hsmall : convexHull ℝ (range v) ⊆ Metric.ball q ε :=
    convexHull_min (range_subset_iff.mpr hv) (convex_ball q ε)
  have hdisj (P : C.cellsOfCodimension k) (hne : P ≠ Q) :
      Disjoint (convexHull ℝ (range v)) (σ P).carrier := by
    rw [hσ P]
    exact (hother P P.property (Subtype.coe_ne_coe.mpr hne)).mono_left hsmall
  refine ⟨fun P => ?_, fun c => ?_⟩
  · by_cases he : P = Q
    · subst P
      refine ⟨?_, fun _ => ?_⟩
      · rw [hσ Q]
        exact hfront.mono_left hsmall
      · apply ((σ Q).isConormal.evalSign_ne_zero_iff
          ((σ Q).finrank_quotient_direction.trans (Fintype.card_fin k).symm) _).mp
        exact hsign
    · exact (σ P).isTransverse_of_disjoint (hdisj P he)
  · simp only [map_sum, OrientedCell.intersectionPairing_single]
    rw [Finset.sum_eq_single Q (fun P _ hPQ => by
      rw [OrientedCell.intersectionIndex_of_disjoint (hdisj P hPQ), zero_smul]) (by simp)]
    rw [OrientedCell.intersectionIndex_of_nonempty
      ⟨q, hqv, (hσ Q).symm ▸ intrinsicInterior_subset hq⟩]

end Mei.PolyhedralCochain
