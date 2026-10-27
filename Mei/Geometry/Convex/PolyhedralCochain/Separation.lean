/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Pairing
public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Affine.Simplex.Transverse

/-!
# Detecting coefficients on a finite polyhedral complex

An arbitrarily small transverse simplex at a relative interior point of a cell
isolates that cell from all other cells of the same codimension. Its intersection
index is a unit sign. Consequently a finite sum with one chosen orientation on
each cell of a complex represents zero exactly when all its coefficients vanish.
The conclusion concerns equality in polyhedral cochains, including all subdivision
relations, rather than equality of formal presentations.

The tests use `FinitePolyhedralComplex.exists_isolating_ball`,
`AffineSubspace.exists_small_transverse_simplex` and
`Affine.Simplex.conormal_apply_ne_zero`. Detection uses the representative
invariance of `OrientedCell.intersectionPairing`. This lets geometric cochain
identities be checked coefficient by coefficient after a common subdivision.
Unbounded cells and lineality are allowed.
-/

public section

noncomputable section

open Set Module

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

namespace OrientedCell

/-- A relative interior point of a cell in a finite complex admits arbitrarily
small transverse simplex tests isolating it from every other cell of the same
codimension. The intersection lies in the relative interior of the test itself. -/
theorem exists_isolating_transverse_test (σ : OrientedCell h k)
    (C : FinitePolyhedralComplex h) (hσ : σ.carrier ∈ C.cells)
    {p : V} (hp : p ∈ intrinsicInterior ℝ σ.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Affine.Simplex ℝ V k,
      σ.IsTransverse s.points ∧
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε ∧
      convexHull ℝ (range s.points) ∩ σ.carrier = {p} ∧
      p ∈ intrinsicInterior ℝ (convexHull ℝ (range s.points)) ∧
      ∀ Q ∈ C.cellsOfCodimension k, Q ≠ σ.carrier →
        Disjoint (convexHull ℝ (range s.points)) Q := by
  have := h.finiteDimensional
  obtain ⟨r, hr, _, hfront, hother, _⟩ := C.exists_isolating_ball
    ((C.mem_cellsOfCodimension k _).mpr ⟨hσ, σ.finrank_direction_add⟩) hp
  obtain ⟨s, hcompl, hball, hinter, hpint⟩ :=
    (affineSpan ℝ σ.carrier).exists_small_transverse_simplex σ.finrank_quotient_direction
      (subset_affineSpan ℝ _ (intrinsicInterior_subset hp)) (lt_min hr hε)
  have hsmall : convexHull ℝ (range s.points) ⊆ Metric.ball p r :=
    hball.trans (Metric.ball_subset_ball (min_le_left _ _))
  refine ⟨s, σ.isTransverse_of_isCompl s hcompl (hfront.mono_left hsmall),
    hball.trans (Metric.ball_subset_ball (min_le_right _ _)), ?_, hpint,
    fun Q hQ hne => (hother Q hQ hne).mono_left hsmall⟩
  apply Set.Subset.antisymm
  · exact (inter_subset_inter_right _ (subset_affineSpan ℝ _)).trans hinter.le
  · rintro y (rfl : y = p)
    exact ⟨intrinsicInterior_subset hpint, intrinsicInterior_subset hp⟩

end OrientedCell

namespace PolyhedralCochain

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- With one orientation on each codimension-`k` cell of a finite complex, a
linear combination represents the zero cochain exactly when all coefficients
are zero. In particular subdivision relations introduce no extra dependencies
among these oriented cells. -/
@[simp]
theorem sum_mk_eq_zero_iff (C : FinitePolyhedralComplex h)
    [Fintype (C.cellsOfCodimension k)]
    (σ : C.cellsOfCodimension k → OrientedCell h k)
    (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
    (c : C.cellsOfCodimension k → E) :
    (∑ Q, mk (R := R) (σ Q) (c Q)) = 0 ↔ ∀ Q, c Q = 0 := by
  classical
  have := h.finiteDimensional
  constructor
  · intro hz Q
    have hQC := ((C.mem_cellsOfCodimension k Q).mp Q.property).1
    obtain ⟨p, hp⟩ := (C.nonempty Q hQC).intrinsicInterior
      (C.isConvexPolyhedron hQC).convex
    obtain ⟨s, htrans, _, hmeet, _, hother⟩ := (σ Q).exists_isolating_transverse_test C
      (hσ Q ▸ hQC) (hσ Q ▸ hp) (by norm_num : (0 : ℝ) < 1)
    have hdisj (P : C.cellsOfCodimension k) (hne : P ≠ Q) :
        Disjoint (convexHull ℝ (range s.points)) (σ P).carrier := by
      rw [hσ P]
      exact hother P P.property (by rw [hσ Q]; exact Subtype.coe_ne_coe.mpr hne)
    -- All other cells miss this test; only the selected coefficient contributes.
    let f : OrientedCell h k →₀ E := ∑ P, Finsupp.single (σ P) (c P)
    have hf : ofFinsupp (R := R) f = 0 := by
      simpa only [f, map_sum, ofFinsupp_single] using hz
    have hftrans : ∀ τ ∈ f.support, τ.IsTransverse s.points := by
      intro τ hτ
      obtain ⟨P, _, hP⟩ := Finsupp.mem_support_finsetSum τ hτ
      have he : τ = σ P := ((Finsupp.mem_support_single _ _ _).mp hP).1
      subst τ
      by_cases hPQ : P = Q
      · exact hPQ ▸ htrans
      · exact (σ P).isTransverse_of_disjoint (hdisj P hPQ)
    -- Representative invariance transfers zero in the quotient to zero pairing.
    have heval := intersectionPairing_eq_of_ofFinsupp_eq (hf.trans (map_zero _).symm) hftrans
      (by simp : ∀ τ ∈ (0 : OrientedCell h k →₀ E).support, τ.IsTransverse s.points)
    have hvalue : OrientedCell.intersectionPairing (R := R) s.points f =
        (σ Q).intersectionIndex s.points • c Q := by
      simp only [f, map_sum, OrientedCell.intersectionPairing_single]
      exact Finset.sum_eq_single Q (fun P _ hPQ => by
        rw [OrientedCell.intersectionIndex_of_disjoint (hdisj P hPQ), zero_smul])
        (by simp)
    rw [map_zero, hvalue] at heval
    rcases htrans.intersectionIndex_eq_one_or_neg_one
      (hmeet ▸ singleton_nonempty p) with hindex | hindex
    · simpa only [hindex, one_smul] using heval
    · simpa only [hindex, neg_smul, one_smul, neg_eq_zero] using heval
  · intro hc
    simp only [hc, map_zero, Finset.sum_const_zero]

end PolyhedralCochain

end Mei
