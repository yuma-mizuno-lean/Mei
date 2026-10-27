/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Traversal
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Realization
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Basic
public import Mei.Geometry.Convex.PolyhedralComplex.SingleCrossing
import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Crossing defects along a given polygonal path

The signed sum of central crossing defects computes the logarithm of the actual
path transport gauged by its endpoint chamber lifts. In particular, the negative
signed sum around any adapted loop is its central loop obstruction. The signs
come from the geometric crossing word; a positive crossing contributes the
positive defect, while the additive wall-crossing convention contributes its
negative.

The construction uses `AdaptedWallCrossing.mem_interiors_of_crossings_singleton`,
`Quiver.Path.exists_subdivision_subsingleton_crossings`, and the indexed transport
realization `DirectedDiagram.levelPathProduct_eq_adaptedDiagram`. Thus it applies
to the given path, without replacing it by a path realizing an abstract crossing
sequence. The auxiliary finite diagram stores the negative exponentials of the
crossing defects. Its products telescope the chamber lifts, and centrality turns
these products into additive sums using
`LieSubalgebra.log_wallPathProduct_sub_crossingSum_mem` and
`FiniteWallDiagram.pathProduct_eq_wallPathProduct`.

This is the pathwise central-defect calculation in Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, proof of Theorem 2.6.
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

/-- The central finite diagram of crossing defects. Its stored label is the
negative exponential because a positive crossing inverts the stored label. -/
def crossingDefectDiagram :
    FiniteWallDiagram (D.adaptedComplex (k + 1)) (d.truncatedGroup ℒ (k + 1)) where
  normal Q := h.realCharacter (cross Q).normal
  ker_normal Q := by simpa only [hσ Q] using (cross Q).ker_normal
  label Q := exp (-((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1)))

@[simp]
theorem crossingDefectDiagram_normal :
    (crossingDefectDiagram σ hσ cross hk b t ht).normal =
      fun Q => h.realCharacter (cross Q).normal := (rfl)

@[simp]
theorem crossingDefectDiagram_label (Q : (D.adaptedComplex (k + 1)).walls) :
    (crossingDefectDiagram σ hσ cross hk b t ht).label Q =
      exp (-((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))) := (rfl)

private theorem positive_segment_defect
    {x y : WallComplement (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V))}
    (e : x ⟶ y) (Q : (D.adaptedComplex (k + 1)).walls) (u : ℝ)
    (he : crossings x y = {(Q, u)})
    (hv : 0 < h.realCharacter (cross Q).normal (y.val - x.val)) :
    x.val ∈ interior ((cross Q).minus : Set V) ∧
    y.val ∈ interior ((cross Q).plus : Set V) ∧
    (crossingDefectDiagram σ hσ cross hk b t ht).pathProduct e.toPath =
      (t (cross Q).plus)⁻¹ *
        (D.adaptedDiagram (k + 1) (fun Q => h.realCharacter (cross Q).normal)
          (fun Q => by simpa only [hσ Q] using (cross Q).ker_normal)).pathProduct e.toPath *
        t (cross Q).minus := by
  have hQ : (⟨(σ Q).carrier, (hσ Q).symm ▸ Q.property⟩ :
      (D.adaptedComplex (k + 1)).walls) = Q := Subtype.ext (hσ Q)
  have he' : crossings x y = {(⟨(σ Q).carrier, (hσ Q).symm ▸ Q.property⟩, u)} := by
    rw [hQ]; exact he
  obtain ⟨hxm, hyp⟩ := (cross Q).mem_interiors_of_crossings_singleton e u he' hv
  have hl : (D.adaptedComplex (k + 1)).orderedCrossings e = [(Q, u)] := by
    symm
    apply ((D.adaptedComplex (k + 1)).orderedCrossings_eq_iff e _).mpr
    simp [he]
  refine ⟨hxm, hyp, ?_⟩
  simp only [FiniteWallDiagram.pathProduct_toPath, hl, List.reverse_singleton,
    List.map_singleton, List.prod_singleton, crossingDefectDiagram_normal,
    crossingDefectDiagram_label, adaptedDiagram_normal, adaptedDiagram_label, hv,
    ↓reduceIte, exp_neg, inv_inv]
  simpa only [exp_log, hQ] using congrArg exp ((cross Q).coe_defect hk b t ht)

private theorem segment_endpoint_defect
    {x y : WallComplement (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V))}
    (e : x ⟶ y) (hs : (crossings x y).Subsingleton)
    (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) :
    ∃ Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0,
      y.val ∈ interior (Q : Set V) ∧
      (crossingDefectDiagram σ hσ cross hk b t ht).pathProduct e.toPath =
        (t Q)⁻¹ *
          (D.adaptedDiagram (k + 1) (fun Q => h.realCharacter (cross Q).normal)
            (fun Q => by simpa only [hσ Q] using (cross Q).ker_normal)).pathProduct e.toPath *
          t P := by
  classical
  let C := D.adaptedComplex (k + 1)
  have heq {Q : C.cellsOfCodimension 0} (hxQ : x.val ∈ interior (Q : Set V)) : Q = P :=
    Subtype.ext (C.eq_of_mem_intrinsicInterior
      ((C.mem_cellsOfCodimension 0 _).mp Q.property).1
      ((C.mem_cellsOfCodimension 0 _).mp P.property).1
      (interior_subset_intrinsicInterior hxQ) (interior_subset_intrinsicInterior hx))
  rcases (crossings x y).eq_empty_or_nonempty with he | ⟨⟨Q, u⟩, hQu⟩
  · refine ⟨P, ?_, ?_⟩
    · simpa only [AffineMap.lineMap_apply_one] using
        C.lineMap_mem_interior_of_crossings_eq_empty P.property hx he 1 ⟨zero_le_one, le_rfl⟩
    · rw [FiniteWallDiagram.pathProduct_toPath_eq_one _ e he,
        FiniteWallDiagram.pathProduct_toPath_eq_one _ e he]
      simp
  · have he : crossings x y = {(Q, u)} := hs.eq_singleton_of_mem hQu
    have hn : h.realCharacter (cross Q).normal (y.val - x.val) ≠ 0 :=
      C.normal_velocity_ne_zero _ e ((C.mem_orderedCrossings e _).mpr hQu)
        (by simpa only [hσ Q] using (cross Q).ker_normal)
    rcases lt_or_gt_of_ne hn with hv | hv
    · have hr : crossings y x = {(Q, 1 - u)} := by
        simpa only [he, Set.image_singleton] using crossings_swap x y
      have hv' : 0 < h.realCharacter (cross Q).normal (x.val - y.val) := by
        simpa only [map_sub, neg_sub] using neg_pos.mpr hv
      obtain ⟨hym, hxp, hprod⟩ := positive_segment_defect σ hσ cross hk b t ht
        (Quiver.reverse e) Q (1 - u) hr hv'
      have hP := heq hxp
      refine ⟨(cross Q).minus, hym, ?_⟩
      rw [← Quiver.Path.reverse_toPath, FiniteWallDiagram.pathProduct_reverse,
        FiniteWallDiagram.pathProduct_reverse] at hprod
      have hi := congrArg Inv.inv hprod
      simpa only [inv_inv, mul_inv_rev, hP, mul_assoc] using hi
    · obtain ⟨hxm, hyp, hprod⟩ := positive_segment_defect σ hσ cross hk b t ht e Q u he hv
      exact ⟨(cross Q).plus, hyp, by simpa only [heq hxm] using hprod⟩

/-- Products of the finite defect diagram telescope the chamber lifts along the
actual path. Only the endpoints must be specified in full cell interiors. -/
theorem pathProduct_crossingDefectDiagram
    {x y : WallComplement (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V))}
    (p : AdmissiblePLPath x y)
    (P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) (hy : y.val ∈ interior (Q : Set V)) :
    (crossingDefectDiagram σ hσ cross hk b t ht).pathProduct p =
      (t Q)⁻¹ * D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).mapPath p) * t P := by
  let A := crossingDefectDiagram σ hσ cross hk b t ht
  let B := D.adaptedDiagram (k + 1) (fun Q => h.realCharacter (cross Q).normal)
    (fun Q => by simpa only [hσ Q] using (cross Q).ker_normal)
  obtain ⟨q, hpq, hs⟩ := p.exists_subdivision_subsingleton_crossings
  have hpath : ∀ {y} (q : AdmissiblePLPath x y),
      q.vertices.IsChain (fun u v => (crossings u v).Subsingleton) →
      ∃ Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0,
        y.val ∈ interior (Q : Set V) ∧ A.pathProduct q = (t Q)⁻¹ * B.pathProduct q * t P := by
    intro y q
    induction q with
    | nil => exact fun _ => ⟨P, hx, by simp⟩
    | @cons z y q e ih =>
      intro hs
      rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.isChain_vertices_comp] at hs
      obtain ⟨S, hz, hq⟩ := ih hs.1
      obtain ⟨T, hy, he⟩ := segment_endpoint_defect σ hσ cross hk b t ht e
        (by simpa only [Quiver.Path.vertices_toPath, List.isChain_pair] using hs.2) S hz
      refine ⟨T, hy, ?_⟩
      rw [FiniteWallDiagram.pathProduct_cons, FiniteWallDiagram.pathProduct_cons, hq, he]
      dsimp only [B]
      group
  obtain ⟨T, hyT, hq⟩ := hpath q hs
  have hT : T = Q := Subtype.ext ((D.adaptedComplex (k + 1)).eq_of_mem_intrinsicInterior
    (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp T.property).1
    (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp Q.property).1
    (interior_subset_intrinsicInterior hyT) (interior_subset_intrinsicInterior hy))
  rw [hT, A.pathProduct_eq_of_isSubdivision hpq, B.pathProduct_eq_of_isSubdivision hpq] at hq
  rw [D.levelPathProduct_eq_adaptedDiagram]
  exact hq

/-- The logarithm of gauged transport along the given adapted path is the
negative signed crossing sum of the actual central wall defects. No consistency
at the higher order or shortness of the segments is required. -/
theorem log_inv_mul_levelPathProduct_mul_eq_neg_wallCrossingSum_defect
    {x y : WallComplement (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V))}
    (p : AdmissiblePLPath x y)
    (P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) (hy : y.val ∈ interior (Q : Set V)) :
    log ((t Q)⁻¹ *
      D.levelPathProduct (k + 1) ((D.adaptedPathPrefunctor (k + 1)).mapPath p) * t P) =
        -p.wallCrossingSum (fun Q => h.realCharacter (cross Q).normal)
          (fun Q => ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))) := by
  let A := crossingDefectDiagram σ hσ cross hk b t ht
  let f := d.truncationMap ℒ (Nat.le_succ k)
  let K := f.ker.toLieSubalgebra
  have hlabel (Q : (D.adaptedComplex (k + 1)).walls) : log (A.label Q) ∈ f.ker := by
    rw [crossingDefectDiagram_label, log_exp]
    exact f.ker.neg_mem ((cross Q).defect hk b t ht).property
  have hcomm : ∀ a b : (D.adaptedComplex (k + 1)).walls,
      affineSpan ℝ (a : Set V) = affineSpan ℝ (b : Set V) →
        Commute (A.label a) (A.label b) := by
    intro a b _
    exact commute_of_lie_log_eq_zero _ _
      ((d.ker_truncationMap_succ_le_center ℒ k (hlabel b)) _)
  have he := K.log_wallPathProduct_sub_crossingSum_mem (⊥ : Submodule R _)
    (fun a _ b hb => by
      simpa only [Submodule.mem_bot] using (d.ker_truncationMap_succ_le_center ℒ k hb) a)
    A.normal A.label hcomm p
    (fun _ _ a _ => (K.mem_bchSubgroup _).mpr (hlabel a.1))
  rw [Submodule.mem_bot, sub_eq_zero, ← A.pathProduct_eq_wallPathProduct hcomm,
    pathProduct_crossingDefectDiagram σ hσ cross hk b t ht p P Q hx hy] at he
  rw [he]
  simp only [A, crossingDefectDiagram_normal, crossingDefectDiagram_label, log_exp]
  simp only [Quiver.Path.wallCrossingSum_def, zsmul_neg, Finset.sum_neg_distrib,
    List.sum_neg, List.map_map, Function.comp_def]

/-- Around an actual adapted loop the chamber lift disappears, and its central
obstruction is the negative signed sum of the crossing-defect coefficients. -/
theorem coe_loopObstruction_eq_neg_wallCrossingSum_defect
    {x : WallComplement (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V))}
    (p : AdmissiblePLPath x x)
    (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) :
    (D.loopObstruction hk ((D.adaptedPathPrefunctor (k + 1)).mapPath p) :
      d.truncatedLie ℒ (k + 1)) =
        -p.wallCrossingSum (fun Q => h.realCharacter (cross Q).normal)
          (fun Q => ((cross Q).defect hk b t ht : d.truncatedLie ℒ (k + 1))) := by
  let q := (D.adaptedPathPrefunctor (k + 1)).mapPath p
  have he := D.inv_mul_levelPathProduct_loop_mul hk q (t P)
  have hp := log_inv_mul_levelPathProduct_mul_eq_neg_wallCrossingSum_defect
    σ hσ cross hk b t ht p P P hx hx
  rw [coe_loopObstruction]
  exact (congrArg log he).symm.trans hp

end Mei.DirectedDiagram
