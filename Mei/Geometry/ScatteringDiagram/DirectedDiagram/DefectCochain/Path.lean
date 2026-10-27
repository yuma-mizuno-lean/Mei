/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Traversal
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Realization
public import Mei.Geometry.Convex.PolyhedralComplex.SingleCrossing
public import Mei.Geometry.Convex.PolyhedralCochain.LocalCrossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Basic
public import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Central defect pairings along subdivided paths

Every admissible path on the adapted complex has a subdivision on which the sum
of segment pairings with the crossing-defect presentation is the logarithm of
the original directed transport, gauged by its endpoint chamber lifts. For a loop,
the sum is the actual kernel-valued loop obstruction. The subdivision retains
endpoints and crossing words; no higher-order consistency is required.

The calculation combines `AdaptedWallCrossing.mem_interiors_of_crossings_singleton`,
its label formula, `Quiver.Path.exists_subdivision_subsingleton_crossings`, and
`LieHom.logDefect_mul`. This is the transport side of the central obstruction
argument in Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, proof of Theorem 2.6. Comparison with pairings on the original
unsubdivided segments and with signed boundary incidences is separate.
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

private theorem positive_segment_log
    {x y : WallComplement (fun W : (D.adaptedComplex (k + 1)).walls => (W : Set V))}
    (e : x ⟶ y) (W : (D.adaptedComplex (k + 1)).walls) (a : ℝ)
    (he : crossings x y = {(W, a)})
    (hv : 0 < h.realCharacter (cross W).normal (y.val - x.val))
    (P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) (hy : y.val ∈ interior (Q : Set V)) :
    log ((t Q)⁻¹ *
      D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).map e).toPath * t P) =
      ((cross W).defect hk b t ht : d.truncatedLie ℒ (k + 1)) := by
  have he' : crossings x y = {(⟨(σ W).carrier, (hσ W).symm ▸ W.property⟩, a)} := by
    simpa only [hσ W] using he
  obtain ⟨hxm, hyp⟩ := (cross W).mem_interiors_of_crossings_singleton e a he' hv
  have hP : P = (cross W).minus := by
    apply Subtype.ext
    exact (D.adaptedComplex (k + 1)).eq_of_mem_intrinsicInterior
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp P.property).1
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp (cross W).minus.property).1
      (interior_subset_intrinsicInterior hx) (interior_subset_intrinsicInterior hxm)
  have hQ : Q = (cross W).plus := by
    apply Subtype.ext
    exact (D.adaptedComplex (k + 1)).eq_of_mem_intrinsicInterior
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp Q.property).1
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp (cross W).plus.property).1
      (interior_subset_intrinsicInterior hy) (interior_subset_intrinsicInterior hyp)
  rw [hP, hQ, (cross W).levelPathProduct_eq_label_of_crossings_singleton e a he' hv
    ((D.adaptedPathPrefunctor (k + 1)).map e)
    (D.adaptedPathPrefunctor_obj_val _ _) (D.adaptedPathPrefunctor_obj_val _ _),
    AdaptedWallCrossing.coe_defect]

/-- A segment meeting at most one adapted wall computes the pairing of the
entire crossing-defect presentation using the lifts of its actual endpoint
chambers. Negative crossings and wall-free segments are included. -/
theorem log_levelPathProduct_eq_intersectionPairing_of_subsingleton
    {x y : WallComplement (fun W : (D.adaptedComplex (k + 1)).walls => (W : Set V))}
    (e : x ⟶ y) (he : (crossings x y).Subsingleton)
    (P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) (hy : y.val ∈ interior (Q : Set V)) :
    log ((t Q)⁻¹ *
      D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).map e).toPath * t P) =
      ((OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
        (∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht)) :
          (d.truncationMap ℒ (Nat.le_succ k)).ker) : d.truncatedLie ℒ (k + 1)) := by
  classical
  -- A wall-free segment stays in one chamber and pairs to zero.
  rcases he.eq_empty_or_singleton with he | ⟨⟨W, a⟩, he⟩
  · have hyP := (D.adaptedComplex (k + 1)).lineMap_mem_interior_of_crossings_eq_empty
      P.property hx he 1 (by simp)
    have hPQ : P = Q := by
      apply Subtype.ext
      exact (D.adaptedComplex (k + 1)).eq_of_mem_intrinsicInterior
        (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp P.property).1
        (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp Q.property).1
        (interior_subset_intrinsicInterior
          (by simpa only [AffineMap.lineMap_apply_one] using hyP))
        (interior_subset_intrinsicInterior hy)
    subst Q
    rw [D.levelPathProduct_toPath_eq_adaptedDiagram
      (fun W => h.realCharacter (cross W).normal)
      (fun W => by simpa only [hσ W] using (cross W).ker_normal),
      FiniteWallDiagram.pathProduct_toPath_eq_one _ e he]
    have hz : OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
        (∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht)) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro W _
      rw [OrientedCell.intersectionPairing_single,
        OrientedCell.intersectionIndex_of_disjoint, zero_smul]
      rw [Matrix.range_cons_cons_empty, convexHull_pair, segment_eq_image_lineMap]
      apply disjoint_left.mpr
      rintro z ⟨u, hu, rfl⟩ hz
      have hm := (mem_crossings x y W u).mpr ⟨hu, (hσ W) ▸ hz⟩
      simp only [he, mem_empty_iff_false] at hm
    rw [hz]
    simp only [mul_one, inv_mul_cancel, log_one, ZeroMemClass.coe_zero]
  · have hm : (W, a) ∈ crossings x y := he ▸ mem_singleton _
    have hn := (D.adaptedComplex (k + 1)).normal_velocity_ne_zero
      (h.realCharacter (cross W).normal) e
      (((D.adaptedComplex (k + 1)).mem_orderedCrossings e _).mpr hm)
      (by simpa only [hσ W] using (cross W).ker_normal)
    have hpair := PolyhedralCochain.intersectionPairing_eq_of_crossings_singleton
      (R := R) σ hσ (fun W => (cross W).defect hk b t ht) he
    -- Reverse negative crossings; positive crossings use the stored wall defect.
    rcases lt_or_gt_of_ne hn with hv | hv
    · have her : crossings y x = {(W, 1 - a)} := by
        rw [crossings_swap, he, Set.image_singleton]
      have hvr : 0 < h.realCharacter (cross W).normal (x.val - y.val) := by
        simpa only [map_sub, neg_sub] using neg_pos.mpr hv
      have hlog := positive_segment_log σ hσ cross hk b t ht
        (Quiver.reverse e) W (1 - a) her hvr Q P hy hx
      have hinv :
          (t Q)⁻¹ *
            D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).map e).toPath *
            t P =
          ((t P)⁻¹ *
            D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).map
              (Quiver.reverse e)).toPath * t Q)⁻¹ := by
        rw [Prefunctor.map_reverse, ← Quiver.Path.reverse_toPath,
          D.levelPathProduct_reverse]
        group
      rw [hinv, log_inv, hlog, hpair]
      have hs := (cross W).sign_normal (y.val - x.val)
      rw [sign_neg hv] at hs
      simp only [← hs, SignType.coe_neg_one, neg_one_zsmul, LieSubmodule.coe_neg]
    · rw [positive_segment_log σ hσ cross hk b t ht e W a he hv P Q hx hy, hpair]
      have hs := (cross W).sign_normal (y.val - x.val)
      rw [sign_pos hv] at hs
      simp only [← hs, SignType.coe_one, one_smul]

private theorem sum_pairings_of_single_crossings
    {x y : WallComplement (fun W : (D.adaptedComplex (k + 1)).walls => (W : Set V))}
    (p : AdmissiblePLPath x y)
    (hp : p.vertices.IsChain (fun u v => (crossings u v).Subsingleton))
    (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) :
    ∃ Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0,
      y.val ∈ interior (Q : Set V) ∧
      log ((t Q)⁻¹ *
        D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).mapPath p) * t P) =
        ((p.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] (∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht))) :
            (d.truncationMap ℒ (Nat.le_succ k)).ker) : d.truncatedLie ℒ (k + 1)) := by
  induction p with
  | nil => exact ⟨P, hx, by simp [Quiver.Path.addWeightOfEPs_nil]⟩
  | @cons y z p e ih =>
    have hp' : p.vertices.IsChain (fun u v => (crossings u v).Subsingleton) ∧
        (crossings y z).Subsingleton := by
      simpa only [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.isChain_vertices_comp,
        Quiver.Path.vertices_toPath, List.isChain_pair] using hp
    obtain ⟨Q, hy, hlog⟩ := ih hp'.1
    -- Propagate the endpoint chamber through a wall-free or singleton segment.
    have hz : ∃ S : (D.adaptedComplex (k + 1)).cellsOfCodimension 0,
        z.val ∈ interior (S : Set V) := by
      rcases hp'.2.eq_empty_or_singleton with he | ⟨⟨W, a⟩, he⟩
      · refine ⟨Q, ?_⟩
        simpa using (D.adaptedComplex (k + 1)).lineMap_mem_interior_of_crossings_eq_empty
          Q.property hy he 1 (by simp)
      · obtain ⟨_, _, S, hS, _, _, _, hafter⟩ :=
          (D.adaptedComplex (k + 1)).exists_chambers_of_crossings_singleton e W a he (by simp)
        have ha := (mem_crossings y z W a).mp (he ▸ mem_singleton _)
        exact ⟨⟨S, hS⟩, by simpa using (hafter 1
          ⟨(e.down.crossing_mem_intrinsicInterior ha.1 ha.2).1.2, le_rfl⟩)⟩
    obtain ⟨S, hz⟩ := hz
    refine ⟨S, hz, ?_⟩
    have he := log_levelPathProduct_eq_intersectionPairing_of_subsingleton
      σ hσ cross hk b t ht e hp'.2 Q S hy hz
    let f := d.truncationMap ℒ (Nat.le_succ k)
    -- Both gauged transports are in the abelian successive truncation kernel.
    have hX : f.bchGroupMap
        (D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).mapPath p)) *
          f.bchGroupMap (t P) = f.bchGroupMap (t Q) := by
      have hm := D.adapted_chamber_lift_path_mem_ker (Nat.le_succ k) hk b t ht
        ((D.adaptedPathPrefunctor (k + 1)).mapPath p) P Q
        (by simpa only [D.adaptedPathPrefunctor_obj_val] using hx)
        (by simpa only [D.adaptedPathPrefunctor_obj_val] using hy)
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_assoc] at hm
      exact (inv_mul_eq_one.mp hm).symm
    have hY : f.bchGroupMap
        (D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).map e).toPath) *
          f.bchGroupMap (t Q) = f.bchGroupMap (t S) := by
      have hm := D.adapted_chamber_lift_path_mem_ker (Nat.le_succ k) hk b t ht
        ((D.adaptedPathPrefunctor (k + 1)).map e).toPath Q S
        (by simpa only [D.adaptedPathPrefunctor_obj_val] using hy)
        (by simpa only [D.adaptedPathPrefunctor_obj_val] using hz)
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_assoc] at hm
      exact (inv_mul_eq_one.mp hm).symm
    have hadd := congrArg (fun a : f.ker => (a : d.truncatedLie ℒ (k + 1)))
      (f.logDefect_mul (t P) (t Q) (t S) _ _ hX hY)
    simp only [LieHom.coe_logDefect, LieSubmodule.coe_add] at hadd
    rw [Prefunctor.mapPath_cons, ← Quiver.Path.comp_toPath_eq_cons,
      D.levelPathProduct_comp, hadd, hlog, he,
      Quiver.Path.addWeightOfEPs_cons, LieSubmodule.coe_add]
    exact add_comm _ _

/-- Subdivide an actual adapted path into single-crossing segments. The logarithm
of its original gauged directed transport is the sum of the defect-presentation
pairings on the subdivision. No transport or pairing identity is assumed of that subdivision. -/
theorem exists_subdivision_log_levelPathProduct_eq_sum_intersectionPairing
    {x y : WallComplement (fun W : (D.adaptedComplex (k + 1)).walls => (W : Set V))}
    (p : AdmissiblePLPath x y)
    (P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) (hy : y.val ∈ interior (Q : Set V)) :
    ∃ q : AdmissiblePLPath x y, p.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (crossings u v).Subsingleton) ∧
      log ((t Q)⁻¹ *
        D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).mapPath p) * t P) =
        ((q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] (∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht))) :
            (d.truncationMap ℒ (Nat.le_succ k)).ker) : d.truncatedLie ℒ (k + 1)) := by
  obtain ⟨q, hpq, hq⟩ := p.exists_subdivision_subsingleton_crossings
  obtain ⟨Q', hy', hlog⟩ := sum_pairings_of_single_crossings σ hσ cross hk b t ht q hq P hx
  have hQ : Q' = Q := by
    apply Subtype.ext
    exact (D.adaptedComplex (k + 1)).eq_of_mem_intrinsicInterior
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp Q'.property).1
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp Q.property).1
      (interior_subset_intrinsicInterior hy') (interior_subset_intrinsicInterior hy)
  subst Q'
  refine ⟨q, hpq, hq, ?_⟩
  have hprod := (D.adaptedDiagram (k + 1) (fun W => h.realCharacter (cross W).normal)
    (fun W => by simpa only [hσ W] using (cross W).ker_normal)).pathProduct_eq_of_isSubdivision hpq
  rw [← D.levelPathProduct_eq_adaptedDiagram, ← D.levelPathProduct_eq_adaptedDiagram] at hprod
  rw [← hprod]
  exact hlog

/-- The actual loop obstruction is the kernel-valued sum of crossing-defect
pairings on a subdivision of that same loop. This is independent of endpoint
lifts, since the loop transport lies in the central truncation kernel. -/
theorem exists_subdivision_loopObstruction_eq_sum_intersectionPairing
    {x : WallComplement (fun W : (D.adaptedComplex (k + 1)).walls => (W : Set V))}
    (p : AdmissiblePLPath x x)
    (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) :
    ∃ q : AdmissiblePLPath x x, p.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (crossings u v).Subsingleton) ∧
      D.loopObstruction hk ((D.adaptedPathPrefunctor (k + 1)).mapPath p) =
        q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] (∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht))) := by
  obtain ⟨q, hpq, hq, hlog⟩ :=
    exists_subdivision_log_levelPathProduct_eq_sum_intersectionPairing
      σ hσ cross hk b t ht p P P hx hx
  refine ⟨q, hpq, hq, Subtype.ext ?_⟩
  have hm : D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).mapPath p) ∈
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap.ker := by
    rw [MonoidHom.mem_ker, D.truncation_levelPathProduct (Nat.le_succ k)]
    exact (D.levelConsistent_iff_loops k).mp hk _ _
  have hc := Subgroup.mem_center_iff.mp
    ((d.truncationMap ℒ (Nat.le_succ k)).ker_bchGroupMap_le_center
      (d.ker_truncationMap_succ_le_center ℒ k) hm) ((t P)⁻¹)
  rw [hc, mul_assoc, inv_mul_cancel, mul_one] at hlog
  simpa only [coe_loopObstruction] using hlog

end Mei.DirectedDiagram
