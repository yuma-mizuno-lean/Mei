/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Reconstruction
public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Joint

/-!
# Assembling local Stokes identities into a cochain identity

For a finite wall presentation, choose an orientation and a relative interior
point on each joint of its complex. There are positive radii such that any
complementary triangles inside these balls, enclosing the chosen points and
with vertices off the walls, identify the entire coboundary by their signed
edge pairings. One triangle per joint suffices; the triangles need not have
compatible shapes, sizes or orientations.

This turns local meridian calculations into equality of cochains, after
combining all coincident signed facets. The comparison permits arbitrary module
coefficients, real offsets, unbounded cells and lineality.

The local input is
`PolyhedralCochain.exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove`.
`FinitePolyhedralComplex.exists_isolating_ball` separates the joint tests, and
`PolyhedralCochain.coboundary_eq_sum_mk_iff_isolating_pairings` assembles them.
-/

public section

noncomputable section

open Set

namespace Mei.PolyhedralCochain

variable {N V R E : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  [Ring R] [AddCommGroup E] [Module R E]

/-- Local signed edge-pairing identities on one small triangle at each joint
are equivalent to the global coboundary identity. The intersection sign allows
either triangle orientation; for a positive meridian this sign is one.
The radii depend only on the presentation and chosen joint centers, not on the
proposed coefficients or on the triangles. -/
theorem exists_radii_coboundary_eq_sum_mk_iff_edge_pairings
    (C : FinitePolyhedralComplex h) [Fintype C.joints]
    (f : OrientedCell h 1 →₀ E)
    (hf : ∀ σ ∈ f.support, σ.carrier ∈ C.cells)
    (τ : C.joints → OrientedCell h 2)
    (hτ : ∀ J, (τ J).carrier = (J : Set V))
    (q : C.joints → V) (hq : ∀ J : C.joints, q J ∈ intrinsicInterior ℝ (J : Set V)) :
    ∃ ε : C.joints → ℝ, (∀ J, 0 < ε J) ∧
      ∀ s : C.joints → Affine.Triangle ℝ V,
        (∀ J, q J ∈ (s J).interior) →
        (∀ J : C.joints, IsCompl (affineSpan ℝ (J : Set V)).direction
          (vectorSpan ℝ (range (s J).points))) →
        (∀ J, convexHull ℝ (range (s J).points) ⊆ Metric.ball (q J) (ε J)) →
        (∀ J, ∀ σ ∈ f.support, ∀ m, (s J).points m ∉ σ.carrier) →
        ∀ c : C.joints → E,
          (coboundary (ofFinsupp (R := R) f) = ∑ J, mk (τ J) (c J) ↔
            ∀ J, (∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) •
              OrientedCell.intersectionPairing (R := R) ((s J).points ∘ m.succAbove) f) =
              (τ J).intersectionIndex (s J).points • c J) := by
  classical
  choose δ hδ hstokes using fun J : C.joints =>
    exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove (R := R)
      C f hf J.property (hq J)
  choose r hr _ hfront hother _ using fun J : C.joints =>
    C.exists_isolating_ball J.property (hq J)
  refine ⟨fun J => min (δ J) (r J), fun J => lt_min (hδ J) (hr J),
    fun s hqs hc hs hv c => ?_⟩
  have hsmall (J) : convexHull ℝ (range (s J).points) ⊆ Metric.ball (q J) (r J) :=
    (hs J).trans (Metric.ball_subset_ball (min_le_right _ _))
  have ho (J P : C.joints) (hne : P ≠ J) :
      Disjoint (convexHull ℝ (range (s J).points)) (P : Set V) :=
    (hother J P P.property (Subtype.coe_ne_coe.mpr hne)).mono_left (hsmall J)
  have hm (J) : (convexHull ℝ (range (s J).points) ∩ (J : Set V)).Nonempty := by
    refine ⟨q J, ?_, intrinsicInterior_subset (hq J)⟩
    rw [(s J).convexHull_eq_closedInterior]
    exact (s J).interior_subset_closedInterior (hqs J)
  have ht (J) : (τ J).IsTransverse (s J).points :=
    (τ J).isTransverse_of_isolating_simplex C (hτ J ▸ J.property) (s J) (hc J)
      ((hfront J).mono_left (hsmall J))
      (fun P hP hne => (hother J P hP hne).mono_left (hsmall J))
  rw [coboundary_eq_sum_mk_iff_isolating_pairings f hf τ hτ
    (fun J => (s J).points) ht hm ho c]
  apply forall_congr'
  intro J
  rw [hstokes J (s J) (hqs J) (hc J)
    ((hs J).trans (Metric.ball_subset_ball (min_le_left _ _))) (hv J)]

end Mei.PolyhedralCochain
