/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Pairing
public import Mei.Geometry.Convex.PolyhedralComplex.Strata

/-!
# Local evaluation of a wall presentation

Near a relative interior point of a wall of a finite complex, every transverse
segment through that point pairs with the wall presentation by extracting its
coefficient, with the sign of the crossing. The radius works for every such
segment and every coefficient family. All cells in the presentation are
transverse to the segment, so the pairing also respects cochain relations.

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

/-- Near a wall interior point, a segment through that point with nonzero
oriented normal evaluation is transverse to every wall cell. Its pairing with
any indexed wall presentation is the selected coefficient times that sign.
The neighborhood is independent of the coefficient family and of the segment. -/
theorem exists_ball_intersectionPairing_eq (C : FinitePolyhedralComplex h)
    (σ : C.walls → OrientedCell h 1) (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
    (Q : C.walls) {q : V} (hq : q ∈ intrinsicInterior ℝ (Q : Set V)) :
    ∃ ε > 0, ∀ {x y : V}, x ∈ Metric.ball q ε → y ∈ Metric.ball q ε →
      q ∈ segment ℝ x y →
      (σ Q).orientation.evalSign (fun _ : Fin 1 => y - x) ≠ 0 →
      (∀ P, (σ P).IsTransverse ![x, y]) ∧
      ∀ c : C.walls → E,
        OrientedCell.intersectionPairing (R := R) ![x, y]
          (∑ P, Finsupp.single (σ P) (c P)) =
            ((σ Q).orientation.evalSign (fun _ : Fin 1 => y - x) : ℤ) • c Q := by
  classical
  have := h.finiteDimensional
  obtain ⟨ε, hε, _, hfront, hother, _⟩ := C.exists_isolating_ball Q.property hq
  refine ⟨ε, hε, fun {x y} hx hy hqxy hsign => ?_⟩
  have hhull : convexHull ℝ (range ![x, y]) = segment ℝ x y := by
    rw [Matrix.range_cons_cons_empty, convexHull_pair]
  have hsmall : convexHull ℝ (range ![x, y]) ⊆ Metric.ball q ε := by
    rw [hhull]
    exact (convex_ball q ε).segment_subset hx hy
  have hdisj (P : C.walls) (hne : P ≠ Q) :
      Disjoint (convexHull ℝ (range ![x, y])) (σ P).carrier := by
    rw [hσ P]
    exact (hother P P.property (Subtype.coe_ne_coe.mpr hne)).mono_left hsmall
  have hframe : (fun j : Fin 1 => ![x, y] j.succ - ![x, y] 0) =
      fun _ : Fin 1 => y - x := by ext j; fin_cases j; rfl
  refine ⟨fun P => ?_, fun c => ?_⟩
  · by_cases he : P = Q
    · subst P
      refine ⟨?_, fun _ => ?_⟩
      · rw [hσ Q]
        exact hfront.mono_left hsmall
      · apply ((σ Q).isConormal.evalSign_ne_zero_iff
          ((σ Q).finrank_quotient_direction.trans (Fintype.card_fin 1).symm) _).mp
        rwa [hframe]
    · exact (σ P).isTransverse_of_disjoint (hdisj P he)
  · simp only [map_sum, OrientedCell.intersectionPairing_single]
    rw [Finset.sum_eq_single Q (fun P _ hPQ => by
      rw [OrientedCell.intersectionIndex_of_disjoint (hdisj P hPQ), zero_smul]) (by simp)]
    rw [OrientedCell.intersectionIndex_of_nonempty
      ⟨q, hhull.symm ▸ hqxy, (hσ Q).symm ▸ intrinsicInterior_subset hq⟩, hframe]

end Mei.PolyhedralCochain
