/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Facet
public import Mei.Geometry.Convex.PolyhedralCochain.Meridian

/-!
# Stokes for wall presentations near a joint

At a relative interior point of a joint of a finite polyhedral complex, one
ball works simultaneously for every wall in a finite cochain presentation.
For complementary triangles containing the point in their interior, the
pairing with the signed boundary equals the alternating sum of the three
edge pairings. Vertices must avoid the supporting hyperplanes of incident
walls; walls missing the joint impose no vertex condition.

The common-face property makes every incident wall contain the joint as a
facet. The local facet formula
`OrientedCell.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet`
therefore applies. All other walls miss a sufficiently small ball. Finite
addition assembles these formulas without any assumption on the coefficients,
including when orientations or supports repeat. For isolating triangles the
boundary presentation is a transverse test, by
`PolyhedralCochain.isTransverse_coboundaryPresentation`, and its pairing is the
signed incidence sum on the joint. These are the geometric equalities used
to compare meridian transport with the coboundary of crossing coefficients.
-/

public section

noncomputable section

open Set Module

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace OrientedCell

private theorem exists_ball_stokes_at_joint (σ : OrientedCell h 1)
    (C : FinitePolyhedralComplex h) (hσ : σ.carrier ∈ C.cells)
    {J : Set V} (hJ : J ∈ C.joints) {p : V} (hp : p ∈ intrinsicInterior ℝ J) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, p ∈ s.interior →
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε →
      (J ⊆ σ.carrier → ∀ j, s.points j ∉ affineSpan ℝ σ.carrier) →
      (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex s.points) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (s.points ∘ m.succAbove) := by
  have := h.finiteDimensional
  have hJC := ((C.mem_cellsOfCodimension 2 J).mp hJ).1
  by_cases hpσ : p ∈ σ.carrier
  · have hsub := C.subset_of_mem_intrinsicInterior hJC hσ hp hpσ
    have hface := (isPolyhedralFace_iff.mp (C.face_of_subset hJC hσ hsub)).2
    have hdJ := ((C.mem_cellsOfCodimension 2 J).mp hJ).2
    have hdσ := σ.finrank_direction_add
    rw [direction_affineSpan] at hdJ hdσ
    obtain ⟨ε, hε, hstokes⟩ :=
      σ.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet
        hface (by omega) hp
    exact ⟨ε, hε, fun s hps hT hs hv => hstokes s hps hT hs (hv hsub)⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp σ.isClosed_carrier.isOpen_compl p hpσ
    refine ⟨ε, hε, fun s _ _ hs _ => ?_⟩
    exact σ.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_disjoint
      (Set.disjoint_left.mpr fun y hy hyσ => hball (hs hy) hyσ)

end OrientedCell

namespace PolyhedralCochain

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Near a joint, Stokes holds simultaneously for a finite wall presentation,
with arbitrary coefficients. The radius depends on the presentation and the
joint point, and works for every complementary triangle satisfying the vertex
avoidance condition on incident supporting hyperplanes. -/
theorem exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove
    (C : FinitePolyhedralComplex h) (f : OrientedCell h 1 →₀ E)
    (hf : ∀ σ ∈ f.support, σ.carrier ∈ C.cells)
    {J : Set V} (hJ : J ∈ C.joints) {p : V} (hp : p ∈ intrinsicInterior ℝ J) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, p ∈ s.interior →
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε →
      (∀ σ ∈ f.support, J ⊆ σ.carrier → ∀ j, s.points j ∉ affineSpan ℝ σ.carrier) →
      OrientedCell.intersectionPairing (R := R) s.points (coboundaryPresentation (R := R) f) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) •
          OrientedCell.intersectionPairing (R := R) (s.points ∘ m.succAbove) f := by
  classical
  choose r hr hstokes using fun σ : f.support =>
    σ.val.exists_ball_stokes_at_joint C (hf σ.val σ.property) hJ hp
  -- Adjoin one so that the empty presentation also has a positive radius.
  let S : Finset ℝ := insert 1 (Finset.univ.image r)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hpos : 0 < S.min' hS := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · norm_num
    · obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp ha
      exact hr σ
  refine ⟨S.min' hS, hpos, fun s hps hT hs hv => ?_⟩
  have he (σ : OrientedCell h 1) (hσ : σ ∈ f.support) :=
    hstokes ⟨σ, hσ⟩ s hps hT
      (hs.trans (Metric.ball_subset_ball (Finset.min'_le S _
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨σ, hσ⟩, Finset.mem_univ _, rfl⟩)))))
      (hv σ hσ)
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, coboundaryPresentation_single,
    OrientedCell.intersectionPairing_single]
  conv_rhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, OrientedCell.intersectionPairing_single,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← Finset.sum_smul, he σ hσ, Finset.sum_smul]
  simp only [mul_smul]

/-- On a sufficiently small isolating triangle, the alternating edge pairing
of a wall presentation equals precisely its signed facet incidences on the
chosen joint. The signed boundary is transverse to that triangle, so its
pairing also respects equality of cochains. -/
theorem exists_ball_sum_incident_eq_sum_succAbove
    (C : FinitePolyhedralComplex h) (f : OrientedCell h 1 →₀ E)
    (hf : ∀ σ ∈ f.support, σ.carrier ∈ C.cells)
    {J : Set V} (hJ : J ∈ C.joints) {p : V} (hp : p ∈ intrinsicInterior ℝ J) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, p ∈ s.interior →
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε →
      (∀ σ ∈ f.support, J ⊆ σ.carrier → ∀ j, s.points j ∉ affineSpan ℝ σ.carrier) →
      (∀ τ ∈ (coboundaryPresentation (R := R) f).support, τ.IsTransverse s.points) ∧
      (∑ σ ∈ f.support, ∑ τ ∈ σ.boundaryFacets with τ.carrier = J,
          (τ.orientation.evalSign (fun j : Fin 2 => s.points j.succ - s.points 0) : ℤ) • f σ) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) •
          OrientedCell.intersectionPairing (R := R) (s.points ∘ m.succAbove) f := by
  obtain ⟨r, hr, hstokes⟩ :=
    exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove (R := R) C f hf hJ hp
  obtain ⟨δ, hδ, _, hfront, hother, _⟩ := C.exists_isolating_ball hJ hp
  refine ⟨min r δ, lt_min hr hδ, fun s hps hT hs hv => ?_⟩
  have hsδ := hs.trans (Metric.ball_subset_ball (min_le_right _ _))
  have htrans := isTransverse_coboundaryPresentation (R := R) C f hf s hT
    (hfront.mono_left hsδ) (fun Q hQ hne => (hother Q hQ hne).mono_left hsδ)
  refine ⟨htrans, ?_⟩
  rw [← intersectionPairing_coboundaryPresentation_eq_sum_incident (R := R) C f hf
    ⟨p, s.convexHull_eq_closedInterior.symm ▸ s.interior_subset_closedInterior hps,
      intrinsicInterior_subset hp⟩
    (fun Q hQ hne => (hother Q hQ hne).mono_left hsδ)]
  exact hstokes s hps hT (hs.trans (Metric.ball_subset_ball (min_le_left _ _))) hv

end PolyhedralCochain

end Mei
