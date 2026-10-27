/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Facet
public import Mei.Geometry.Convex.PolyhedralCochain.Meridian

/-!
# Stokes for finite wall presentations near a joint

At a relative interior point of a joint, every wall cell containing the point
has the joint as a facet. All other wall cells miss a sufficiently small ball.
Consequently a finite wall presentation satisfies Stokes on every sufficiently
small complementary triangle containing the point in its interior, with vertices
off the affine spans of the participating walls. The radius is uniform over the
whole presentation, and coefficients may lie in an arbitrary module.

The radius also ensures that the triangle misses every other joint, so the
boundary pairing is the sum of the signed incidences at the joint. The final
formula identifies this sum with the signed edge pairings, allowing comparison
with additive meridian transport.

This assembles `FinitePolyhedralComplex.subset_of_mem_intrinsicInterior`,
`FinitePolyhedralComplex.exists_isolating_ball`,
`OrientedCell.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet`
and `PolyhedralCochain.intersectionPairing_coboundaryPresentation_eq_sum_incident`.
No local Stokes equation or facet-incidence equation is assumed.
-/

public section

noncomputable section

open Set Module Filter Topology

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace OrientedCell

/-- Near a relative interior point of a complex joint, a wall cell satisfies
Stokes on all sufficiently small complementary triangles. A wall missing the
point contributes zero; a wall containing it has that joint as a facet. -/
theorem exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_at_joint
    (σ : OrientedCell h 1) (C : FinitePolyhedralComplex h)
    (hσ : σ.carrier ∈ C.cells) {J : Set V} (hJ : J ∈ C.joints)
    {q : V} (hq : q ∈ intrinsicInterior ℝ J) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, q ∈ s.interior →
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball q ε →
      (∀ j, s.points j ∉ affineSpan ℝ σ.carrier) →
      (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex s.points) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) *
          σ.intersectionIndex (s.points ∘ m.succAbove) := by
  by_cases hqσ : q ∈ σ.carrier
  · have hJC := ((C.mem_cellsOfCodimension 2 J).mp hJ).1
    have hJσ := C.subset_of_mem_intrinsicInterior hJC hσ hq hqσ
    have hface := (isPolyhedralFace_iff.mp (C.face_of_subset hJC hσ hJσ)).2
    have hdimJ := ((C.mem_cellsOfCodimension 2 J).mp hJ).2
    have hdimσ := σ.finrank_direction_add
    rw [direction_affineSpan] at hdimJ hdimσ
    obtain ⟨ε, hε, hstokes⟩ :=
      σ.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet
        hface (by omega) hq
    refine ⟨ε, hε, fun s hqs hc hs hv => hstokes s hqs hc hs ?_⟩
    exact fun j hj => hv j (subset_affineSpan ℝ σ.carrier hj)
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp σ.isClosed_carrier.isOpen_compl q hqσ
    refine ⟨ε, hε, fun s _ _ hs _ => ?_⟩
    exact σ.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_disjoint
      (Set.disjoint_left.mpr fun y hy hyσ => hball (hs hy) hyσ)

end OrientedCell

namespace PolyhedralCochain

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- A finite wall presentation satisfies coefficient-valued Stokes uniformly
near a joint. The boundary is its actual signed facet presentation, including
overlapping or cancelling contributions. No division or coefficient freeness
is required. -/
theorem exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove
    (C : FinitePolyhedralComplex h) (f : OrientedCell h 1 →₀ E)
    (hf : ∀ σ ∈ f.support, σ.carrier ∈ C.cells)
    {J : Set V} (hJ : J ∈ C.joints) {q : V} (hq : q ∈ intrinsicInterior ℝ J) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, q ∈ s.interior →
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball q ε →
      (∀ σ ∈ f.support, ∀ j, s.points j ∉ affineSpan ℝ σ.carrier) →
      OrientedCell.intersectionPairing (R := R) s.points
          (coboundaryPresentation (R := R) f) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) •
          OrientedCell.intersectionPairing (R := R) (s.points ∘ m.succAbove) f := by
  classical
  choose r hr hlocal using fun σ : f.support =>
    σ.val.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_at_joint
      C (hf σ σ.property) hJ hq
  have hnear : ∀ᶠ y in 𝓝 q, ∀ σ : f.support, y ∈ Metric.ball q (r σ) :=
    Filter.eventually_all.mpr fun σ => Metric.ball_mem_nhds q (hr σ)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨ε, hε, fun s hqs hc hs hv => ?_⟩
  have hstokes (σ : OrientedCell h 1) (hσ : σ ∈ f.support) :=
    hlocal ⟨σ, hσ⟩ s hqs hc (fun y hy => hball (hs hy) ⟨σ, hσ⟩) (hv σ hσ)
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, coboundaryPresentation_single,
    OrientedCell.intersectionPairing_single]
  simp only [OrientedCell.intersectionPairing_apply, Finsupp.sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← Finset.sum_smul, hstokes σ hσ, Finset.sum_smul]
  simp only [mul_smul]

/-- On every sufficiently small complementary triangle near a joint, the signed
incidence sum of a finite wall presentation equals its signed edge pairings.
The radius ensures avoidance of every other joint. Each parent keeps its own
coefficient and induced facet orientation. -/
theorem exists_ball_sum_incident_eq_sum_succAbove
    (C : FinitePolyhedralComplex h) (f : OrientedCell h 1 →₀ E)
    (hf : ∀ σ ∈ f.support, σ.carrier ∈ C.cells)
    {J : Set V} (hJ : J ∈ C.joints) {q : V} (hq : q ∈ intrinsicInterior ℝ J) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, q ∈ s.interior →
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball q ε →
      (∀ σ ∈ f.support, ∀ j, s.points j ∉ affineSpan ℝ σ.carrier) →
      (∑ σ ∈ f.support, ∑ τ ∈ σ.boundaryFacets with τ.carrier = J,
        (τ.orientation.evalSign (fun j : Fin 2 => s.points j.succ - s.points 0) : ℤ) • f σ) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) •
          OrientedCell.intersectionPairing (R := R) (s.points ∘ m.succAbove) f := by
  obtain ⟨ε, hε, hstokes⟩ :=
    exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove (R := R) C f hf hJ hq
  obtain ⟨r, hr, _, _, hother, _⟩ := C.exists_isolating_ball hJ hq
  refine ⟨min ε r, lt_min hε hr, fun s hqs hc hs hv => ?_⟩
  have hsε := hs.trans (Metric.ball_subset_ball (min_le_left ε r))
  have hsr := hs.trans (Metric.ball_subset_ball (min_le_right ε r))
  have ho : ∀ Q ∈ C.joints, Q ≠ J → Disjoint (convexHull ℝ (range s.points)) Q :=
    fun Q hQ hne => (hother Q hQ hne).mono_left hsr
  have hqHull : q ∈ convexHull ℝ (range s.points) := by
    rw [s.convexHull_eq_closedInterior]
    exact s.interior_subset_closedInterior hqs
  rw [← intersectionPairing_coboundaryPresentation_eq_sum_incident (R := R) C f hf
    ⟨q, hqHull, intrinsicInterior_subset hq⟩ ho]
  exact hstokes s hqs hc hsε hv

end PolyhedralCochain

end Mei
