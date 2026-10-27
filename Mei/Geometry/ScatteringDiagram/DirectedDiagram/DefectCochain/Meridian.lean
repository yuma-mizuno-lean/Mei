/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Transport
public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Joint
public import Mei.Geometry.Convex.PolyhedralComplex.Meridian
public import Mei.Geometry.Convex.PolyhedralCochain.Crossing

/-!
# Meridian holonomy as a signed boundary pairing

At each oriented joint of an adapted complex, construct arbitrarily small
positive isolating triangular meridians whose actual central loop obstruction
is the pairing with the signed boundary of the crossing-defect presentation.
Both sides take values in the successive truncation kernel. The triangle is
transverse to that boundary presentation, so its pairing is independent of
replacement by any equal cochain presentation transverse to the same test.

This connects `DirectedDiagram.coe_loopObstruction_eq_neg_wallCrossingSum_defect`
with `PolyhedralCochain.exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove`
and `FinitePolyhedralComplex.exists_positive_isolating_joint_triangle`.
The triangle boundary runs from vertex zero to one to two to zero; its middle
parameter face has the opposite orientation. This is the meridian/Stokes
comparison in Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, proof of Theorem 2.6. No higher-order consistency is required.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι} {k : ℕ}

variable
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

/-- At any oriented adapted joint, an arbitrarily small positive isolating
meridian computes the signed boundary pairing of the actual crossing defects.
The equality holds in the central Lie kernel, and the test is transverse to
the full signed boundary presentation. The filled triangle isolates the whole
codimension-two skeleton, not only its selected joint. -/
theorem exists_joint_meridian_loopObstruction_eq_boundaryPairing
    (J : (D.adaptedComplex (k + 1)).joints) {q : V}
    (hq : q ∈ intrinsicInterior ℝ (J : Set V))
    (o : OrientedCell h 2) (ho : o.carrier = (J : Set V))
    {ε : ℝ} (hε : 0 < ε) :
    let f := ∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht)
    ∃ (s : Affine.Triangle ℝ V)
      (x : WallComplement (fun W : (D.adaptedComplex (k + 1)).walls => (W : Set V)))
      (p : AdmissiblePLPath x x),
      0 < o.orientation.someVector (fun j : Fin 2 => s.points j.succ - s.points 0) ∧
      s.centroid = q ∧
      p.vertices.map WallComplement.val = [s.points 0, s.points 1, s.points 2, s.points 0] ∧
      IsCompl (affineSpan ℝ (J : Set V)).direction (vectorSpan ℝ (range s.points)) ∧
      convexHull ℝ (range s.points) ⊆ Metric.ball q ε ∧
      convexHull ℝ (range s.points) ∩
        ((D.adaptedComplex (k + 1)).codimensionAtLeast 2).support = {q} ∧
      (∀ τ ∈ (PolyhedralCochain.coboundaryPresentation (R := R) f).support,
        τ.IsTransverse s.points) ∧
      D.loopObstruction hk ((D.adaptedPathPrefunctor (k + 1)).mapPath p) =
        OrientedCell.intersectionPairing (R := R) s.points
          (PolyhedralCochain.coboundaryPresentation (R := R) f) := by
  classical
  dsimp only
  let C := D.adaptedComplex (k + 1)
  let f := ∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht)
  have hf : ∀ τ ∈ f.support, τ.carrier ∈ C.cells := by
    intro τ hτ
    obtain ⟨W, _, hW⟩ := Finsupp.mem_support_finsetSum τ hτ
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hW
    rw [hσ W]
    exact C.mem_cells_of_mem_walls W.property
  -- Choose one triangle small enough for both Stokes and the prescribed bound.
  obtain ⟨r, hr, hstokes⟩ :=
    PolyhedralCochain.exists_ball_intersectionPairing_coboundaryPresentation_eq_sum_succAbove
      (R := R) C f hf J.property hq
  obtain ⟨s, x, p, hpos, hcenter, hvertices, hcompl, hball, hskeleton,
      hfront, hother, _, _⟩ :=
    C.exists_positive_isolating_joint_triangle J.property hq o.orientation
      (by simpa only [ho] using o.isConormal) (lt_min hr hε)
  have hqinterior : q ∈ s.interior := by
    rw [← hcenter, s.centroid_eq_affineCombination]
    apply (Affine.Simplex.affineCombination_mem_interior_iff
      (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ Finset.univ_nonempty)).mpr
    intro j
    norm_num [Finset.centroidWeights_apply]
  have hv : ∀ τ ∈ f.support, ∀ j, s.points j ∉ τ.carrier := by
    intro τ hτ j
    obtain ⟨W, _, hW⟩ := Finsupp.mem_support_finsetSum τ hτ
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hW
    have hj : s.points j ∈ p.vertices.map WallComplement.val := by
      rw [hvertices]
      fin_cases j <;> simp
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hj
    rw [hσ W, ← he]
    exact y.notMem W
  -- This particular meridian's vertices avoid the higher skeleton by isolation,
  -- and avoid its walls by admissibility. Thus its basepoint has a full chamber.
  have hx0 : x.val = s.points 0 := by
    have he := congrArg List.head? hvertices
    simpa using he
  have hxskel : x.val ∉ (C.codimensionAtLeast 1).support := by
    intro hx
    obtain ⟨Q, hQ, hxQ⟩ := FinitePolyhedralComplex.mem_support.mp hx
    obtain ⟨hQC, hdQ⟩ := (C.mem_codimensionAtLeast_cells 1 Q).mp hQ
    by_cases hdim : Module.finrank ℝ (affineSpan ℝ Q).direction + 1 = Module.finrank ℝ V
    · exact x.notMem ⟨Q, (C.mem_cellsOfCodimension 1 Q).mpr ⟨hQC, hdim⟩⟩ hxQ
    · have hx2 : x.val ∈ (C.codimensionAtLeast 2).support :=
        FinitePolyhedralComplex.mem_support.mpr ⟨Q, (C.mem_codimensionAtLeast_cells 2 Q).mpr
          ⟨hQC, by omega⟩, hxQ⟩
      have he : x.val = q := Set.mem_singleton_iff.mp (hskeleton ▸
        ⟨hx0 ▸ subset_convexHull ℝ _ (mem_range_self 0), hx2⟩)
      exact s.point_notMem_interior 0 ((hx0.symm.trans he).symm ▸ hqinterior)
  obtain ⟨P, ⟨hP, hxP⟩, _⟩ := C.exists_unique_mem_interior_cellsOfCodimension_zero
    (D.support_adaptedComplex (k + 1)) hxskel
  -- Compare the actual transport with the same coefficient-valued edge sum
  -- used by Stokes, retaining equality in the successive Lie kernel.
  have hlog := coe_loopObstruction_eq_neg_wallCrossingSum_defect
    σ hσ cross hk b t ht p ⟨P, hP⟩ hxP
  have hpair : p.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
      ![u.val, v.val] f) =
        -p.wallCrossingSum (fun W => h.realCharacter (cross W).normal)
          (fun W => (cross W).defect hk b t ht) := by
    have he : ∀ {x y : WallComplement (fun W => (σ W).carrier)}
        (p : AdmissiblePLPath x y),
        p.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] f) =
          -p.wallCrossingSum (fun W => h.realCharacter (cross W).normal)
            (fun W => (cross W).defect hk b t ht) :=
      fun p => p.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum
        _ _ (fun W _ v => (cross W).sign_normal v)
    -- Rewrite the carrier family so the pairing theorem uses the actual
    -- adapted endpoint subtype, rather than transporting the path by unfolding it.
    rw [show (fun W => (σ W).carrier) =
      (fun W : C.walls => (W : Set V)) from funext hσ] at he
    exact he p
  have heq : D.loopObstruction hk ((D.adaptedPathPrefunctor (k + 1)).mapPath p) =
      p.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] f) := by
    apply Subtype.ext
    have he := congrArg
      (d.truncationMap ℒ (Nat.le_succ k)).ker.incl.toLinearMap.toAddMonoidHom hpair
    simp only [map_neg, AddMonoidHom.map_wallCrossingSum, LinearMap.toAddMonoidHom_coe,
      LieHom.coe_toLinearMap, LieIdeal.incl_apply] at he
    exact hlog.trans he.symm
  refine ⟨s, x, p, hpos, hcenter, hvertices, hcompl,
    hball.trans (Metric.ball_subset_ball (min_le_right _ _)), hskeleton,
    PolyhedralCochain.isTransverse_coboundaryPresentation C f hf s hcompl hfront hother, ?_⟩
  rw [heq, p.addWeightOfEPs_intersectionPairing_eq_sum_succAbove s.points hvertices]
  exact (hstokes s hqinterior hcompl
    (hball.trans (Metric.ball_subset_ball (min_le_left _ _))) hv).symm

end Mei.DirectedDiagram
