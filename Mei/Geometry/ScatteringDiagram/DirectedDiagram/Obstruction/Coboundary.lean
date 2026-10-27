/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Meridian
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Cochain
public import Mei.Geometry.Convex.PolyhedralCochain.Differential

/-!
# The joint obstruction cochain is a coboundary

For every lower-order chamber trivialization, positive isolating meridians can
be chosen at prescribed joint centers and within prescribed positive radii so
that their kernel-valued obstruction cochain equals the coboundary of the
crossing-defect cochain. Square-zero then makes this actual obstruction closed,
as needed to fill its homogeneous components by outgoing sweeps.

The construction uses
`DirectedDiagram.exists_joint_meridian_loopObstruction_eq_boundaryPairing`
and the signed coefficient formulas
`PolyhedralCochain.ofFinsupp_eq_sum_sub_reverse` and
`PolyhedralCochain.intersectionPairing_eq_sum_sub_reverse`.
It retains every signed facet occurrence, including opposite orientations on
the same joint. Real offsets, unbounded cells and lineality are allowed.

This is the cochain obstruction comparison in Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, proof of Theorem 2.6,
and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Appendix C.3.
-/

public section

noncomputable section

open Set Module Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι} {k : ℕ}
  (σ : (D.adaptedComplex (k + 1)).walls → OrientedCell h 1)
  (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
  (cross : ∀ Q, D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
  (hk : D.LevelConsistent k)
  (b : WallComplement (fun j : D.active k => (D.wall j).support))
  (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
  (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)),
    x.val ∈ interior (P : Set V) →
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)

/-- For every lower-order chamber trivialization, choose positive isolating
meridians at prescribed joint centers, within prescribed positive radii, so
that their central obstruction cochain is the coboundary of the crossing-defect
cochain. Thus square-zero proves closedness of the actual obstruction cochain.
No hypothesis on the initial walls or on higher-order consistency is needed. -/
theorem exists_jointObstructionCochain_eq_coboundary
    (τ : (D.adaptedComplex (k + 1)).joints → OrientedCell h 2)
    (hτ : ∀ J, (τ J).carrier = (J : Set V))
    (q : (D.adaptedComplex (k + 1)).joints → V)
    (hq : ∀ J : (D.adaptedComplex (k + 1)).joints,
      q J ∈ intrinsicInterior ℝ (J : Set V))
    (ε : (D.adaptedComplex (k + 1)).joints → ℝ) (hε : ∀ J, 0 < ε J) :
    ∃ (s : (D.adaptedComplex (k + 1)).joints → Affine.Triangle ℝ V)
      (x : (D.adaptedComplex (k + 1)).joints →
        WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
      (γ : ∀ J, AdmissiblePLPath (x J) (x J)),
      (∀ J,
        0 < (τ J).orientation.someVector (fun j : Fin 2 => (s J).points j.succ - (s J).points 0) ∧
        (s J).centroid = q J ∧
        (γ J).vertices.map WallComplement.val =
          [(s J).points 0, (s J).points 1, (s J).points 2, (s J).points 0] ∧
        IsCompl (affineSpan ℝ (J : Set V)).direction (vectorSpan ℝ (range (s J).points)) ∧
        convexHull ℝ (range (s J).points) ⊆ Metric.ball (q J) (ε J) ∧
        convexHull ℝ (range (s J).points) ∩
          ((D.adaptedComplex (k + 1)).codimensionAtLeast 2).support = {q J} ∧
        Disjoint (convexHull ℝ (range (s J).points)) (intrinsicFrontier ℝ (J : Set V)) ∧
        ∀ Q ∈ (D.adaptedComplex (k + 1)).joints, Q ≠ (J : Set V) →
          Disjoint (convexHull ℝ (range (s J).points)) Q) ∧
      D.jointObstructionCochain τ x γ hτ hk =
        PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht) := by
  classical
  let C := D.adaptedComplex (k + 1)
  let := Fintype.ofFinite C.joints
  -- Shrink the requested radii so all chosen tests also miss other joints.
  choose r hr hisolate hfrontier hothers hincident using fun J : C.joints =>
    C.exists_isolating_ball J.property (hq J)
  choose s x p hpos hcenter hp hc hs hskel htrans hloop using fun J : C.joints =>
    exists_joint_meridian_loopObstruction_eq_boundaryPairing
      σ hσ cross hk b t ht J (hq J) (τ J) (hτ J) (lt_min (hε J) (hr J))
  have hsmall (J : C.joints) :
      convexHull ℝ (range (s J).points) ⊆ Metric.ball (q J) (r J) :=
    (hs J).trans (Metric.ball_subset_ball (min_le_right _ _))
  let F := D.adaptedPathPrefunctor (k + 1)
  refine ⟨s, fun J => F.obj (x J), fun J => F.mapPath (p J), ?_, ?_⟩
  · intro J
    refine ⟨hpos J, hcenter J, ?_, ?_⟩
    · simpa only [F, Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        D.adaptedPathPrefunctor_obj_val] using hp J
    · exact ⟨hc J, (hs J).trans (Metric.ball_subset_ball (min_le_left _ _)),
        hskel J, (hfrontier J).mono_left (hsmall J),
        fun Q hQ hne => (hothers J Q hQ hne).mono_left (hsmall J)⟩
  -- Every signed facet occurrence is a joint of the same adapted complex.
  let f := ∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht)
  let B := PolyhedralCochain.coboundaryPresentation (R := R) f
  have hB : ∀ υ ∈ B.support, υ.carrier ∈ C.cells := by
    intro υ hυ
    simp only [B, f, map_sum, PolyhedralCochain.coboundaryPresentation_single] at hυ
    obtain ⟨W, _, hW⟩ := Finsupp.mem_support_finsetSum υ hυ
    obtain ⟨ω, hω, hυ⟩ := Finsupp.mem_support_finsetSum υ hW
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hυ
    exact ((C.mem_cellsOfCodimension 2 υ.carrier).mp
      ((σ W).mem_cellsOfCodimension_of_mem_boundaryFacets C
        (hσ W ▸ C.mem_cells_of_mem_walls W.property) hω)).1
  have hboundary : PolyhedralCochain.ofFinsupp (R := R) B =
      PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht) := by
    rw [PolyhedralCochain.ofFinsupp_coboundaryPresentation,
      ← PolyhedralCochain.coboundary_ofFinsupp]
    congr 1
    simp only [f, map_sum, PolyhedralCochain.ofFinsupp_single, crossingDefectCochain_def]
  rw [← hboundary, jointObstructionCochain_def,
    PolyhedralCochain.ofFinsupp_eq_sum_sub_reverse C τ hτ B hB]
  apply Finset.sum_congr rfl
  intro J _
  congr 1
  -- A positive isolating triangle extracts the chosen signed coefficient.
  have hindex : (τ J).intersectionIndex (s J).points = 1 := by
    rw [OrientedCell.intersectionIndex_of_nonempty]
    · have he := Module.Ray.evalSign_rayOfNeZero (τ J).orientation.someVector_ne_zero
        (fun j : Fin 2 => (s J).points j.succ - (s J).points 0)
      rw [Module.Ray.someVector_ray] at he
      rw [he, sign_pos (hpos J), SignType.coe_one]
    · refine ⟨q J, ?_, (hτ J).symm ▸ intrinsicInterior_subset (hq J)⟩
      have hm := (s J).centroid_eq_affineCombination
      rw [← hcenter J, hm]
      exact affineCombination_mem_convexHull (by simp [Finset.centroidWeights_apply])
        (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ Finset.univ_nonempty)
  have hvalue := hloop J
  rw [PolyhedralCochain.intersectionPairing_eq_sum_sub_reverse C τ hτ B hB,
    Finset.sum_eq_single J] at hvalue
  · simpa only [hindex, one_smul] using hvalue
  · intro K _ hKJ
    rw [OrientedCell.intersectionIndex_of_disjoint, zero_smul]
    rw [hτ K]
    exact (hothers J K K.property (Subtype.coe_ne_coe.mpr hKJ)).mono_left (hsmall J)
  · simp

end Mei.DirectedDiagram
