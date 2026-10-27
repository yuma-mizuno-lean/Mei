/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Traversal
public import Mei.Geometry.Convex.PolyhedralCochain.Crossing

/-!
# Central defect pairings on single-crossing segments

An admissible segment crossing one adapted wall pairs with the full central
crossing-defect presentation by extracting that wall's coefficient with its
crossing sign. In either direction this equals the logarithm of the actual
directed transport gauged by the chamber lifts at the original endpoints.
The segment need not be short. Every wall in the presentation is transverse
to the segment, so its pairing is invariant under cochain relations among
representatives whose cells are also transverse to the segment.

This combines `WallComplement.intersectionPairing_eq_of_crossings_singleton`
with `AdaptedWallCrossing.mem_interiors_of_crossings_singleton` and
`AdaptedWallCrossing.levelPathProduct_eq_label_of_crossings_singleton`.
It supplies the segment calculation used after subdividing a meridian into
single crossings in Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, proof of Theorem 2.6. Reversing the crossing negates
its central coefficient and exchanges the incident chambers.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

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
  {x y : WallComplement (fun Q : (D.adaptedComplex (k + 1)).walls => (Q : Set V))}

/-- A single adapted-wall crossing extracts the signed central coefficient
from the entire defect presentation. All its cells are transverse to the test,
including the cells the segment misses. -/
theorem intersectionPairing_crossingDefect_of_crossings_singleton
    (e : x ⟶ y) (Q : (D.adaptedComplex (k + 1)).walls) (s : ℝ)
    (he : crossings x y = {(Q, s)}) :
    (∀ P, (σ P).IsTransverse ![x.val, y.val]) ∧
    OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
        (∑ P, Finsupp.single (σ P) ((cross P).defect hk b t ht)) =
      (SignType.sign (h.realCharacter (cross Q).normal (y.val - x.val)) : ℤ) •
        (cross Q).defect hk b t ht := by
  classical
  let xσ : WallComplement (fun P => (σ P).carrier) :=
    ⟨x.val, fun P => by rw [hσ]; exact x.notMem P⟩
  let yσ : WallComplement (fun P => (σ P).carrier) :=
    ⟨y.val, fun P => by rw [hσ]; exact y.notMem P⟩
  have hfamily : (fun P => (σ P).carrier) =
      (fun P : (D.adaptedComplex (k + 1)).walls => (P : Set V)) := funext hσ
  have eσ : xσ ⟶ yσ := ⟨⟨fun P hp => by
    rw [hσ P] at hp ⊢
    exact e.down.transverse P hp, fun u hu => by
      simpa only [hfamily] using e.down.regular u hu⟩⟩
  have heσ : crossings xσ yσ = {(Q, s)} := by
    ext ⟨P, u⟩
    simpa only [mem_crossings, hσ] using
      Set.ext_iff.mp he (P, u)
  refine ⟨fun P => eσ.down.isTransverse_orientedCell P, ?_⟩
  rw [intersectionPairing_eq_of_crossings_singleton Q s heσ,
    ← (cross Q).sign_normal]

/-- On a positive single crossing, the pairing is the logarithm of transport
between the stored source and target chamber lifts, evaluated on the original
segment. Coincident indexed directed walls contribute their combined label. -/
theorem intersectionPairing_eq_log_defect_of_positive_crossing
    (e : x ⟶ y) (Q : (D.adaptedComplex (k + 1)).walls) (s : ℝ)
    (he : crossings x y = {(Q, s)})
    (hv : 0 < h.realCharacter (cross Q).normal (y.val - x.val)) :
    x.val ∈ interior ((cross Q).minus : Set V) ∧
    y.val ∈ interior ((cross Q).plus : Set V) ∧
    ((OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
      (∑ P, Finsupp.single (σ P) ((cross P).defect hk b t ht)) :
        (d.truncationMap ℒ (Nat.le_succ k)).ker) : d.truncatedLie ℒ (k + 1)) =
      BCHGroup.log ((t (cross Q).plus)⁻¹ *
        D.levelPathProduct (k + 1) (((D.adaptedPathPrefunctor (k + 1)).map e).toPath) *
        t (cross Q).minus) := by
  have he' : crossings x y = {(⟨(σ Q).carrier, (hσ Q).symm ▸ Q.property⟩, s)} := by
    simpa only [hσ] using he
  have hi := (cross Q).mem_interiors_of_crossings_singleton e s he' hv
  refine ⟨hi.1, hi.2, ?_⟩
  rw [(intersectionPairing_crossingDefect_of_crossings_singleton
    σ hσ cross hk b t ht e Q s he).2, sign_pos hv, SignType.coe_one, one_smul,
    AdaptedWallCrossing.coe_defect]
  rw [(cross Q).levelPathProduct_eq_label_of_crossings_singleton e s he' hv
    ((D.adaptedPathPrefunctor (k + 1)).map e)
    (D.adaptedPathPrefunctor_obj_val _ x) (D.adaptedPathPrefunctor_obj_val _ y)]

/-- On a negative single crossing, the chambers exchange and the extracted
central coefficient changes sign. The resulting pairing still equals the
logarithm of the actual directed transport gauged at its endpoints. -/
theorem intersectionPairing_eq_log_defect_of_negative_crossing
    (e : x ⟶ y) (Q : (D.adaptedComplex (k + 1)).walls) (s : ℝ)
    (he : crossings x y = {(Q, s)})
    (hv : h.realCharacter (cross Q).normal (y.val - x.val) < 0) :
    x.val ∈ interior ((cross Q).plus : Set V) ∧
    y.val ∈ interior ((cross Q).minus : Set V) ∧
    ((OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
      (∑ P, Finsupp.single (σ P) ((cross P).defect hk b t ht)) :
        (d.truncationMap ℒ (Nat.le_succ k)).ker) : d.truncatedLie ℒ (k + 1)) =
      BCHGroup.log ((t (cross Q).minus)⁻¹ *
        D.levelPathProduct (k + 1) (((D.adaptedPathPrefunctor (k + 1)).map e).toPath) *
        t (cross Q).plus) := by
  have he' : crossings x y =
      {(⟨(σ Q).reverse.carrier, by simpa only [OrientedCell.reverse_carrier, hσ]
        using Q.property⟩, s)} := by
    simpa only [OrientedCell.reverse_carrier, hσ] using he
  have hv' : 0 < h.realCharacter (cross Q).reverse.normal (y.val - x.val) := by
    simpa only [AdaptedWallCrossing.reverse_normal, map_neg, LinearMap.neg_apply,
      neg_pos] using hv
  have hi := (cross Q).reverse.mem_interiors_of_crossings_singleton e s he' hv'
  simp only [AdaptedWallCrossing.reverse_minus, AdaptedWallCrossing.reverse_plus] at hi
  refine ⟨hi.1, hi.2, ?_⟩
  rw [(intersectionPairing_crossingDefect_of_crossings_singleton
    σ hσ cross hk b t ht e Q s he).2, sign_neg hv, SignType.coe_neg_one, neg_one_zsmul,
    ← AdaptedWallCrossing.defect_reverse]
  rw [AdaptedWallCrossing.coe_defect]
  rw [(cross Q).reverse.levelPathProduct_eq_label_of_crossings_singleton e s he' hv'
    ((D.adaptedPathPrefunctor (k + 1)).map e)
    (D.adaptedPathPrefunctor_obj_val _ x) (D.adaptedPathPrefunctor_obj_val _ y)]
  simp only [AdaptedWallCrossing.reverse_minus, AdaptedWallCrossing.reverse_plus]

/-- A segment missing all adapted walls stays in its source chamber and has
zero defect pairing and identity directed transport. Stationary segments are
allowed. Together with the single-crossing formulas this covers every segment
of a subdivision with at most one crossing per segment. -/
theorem intersectionPairing_eq_zero_of_crossings_eq_empty
    (e : x ⟶ y) (he : crossings x y = ∅)
    (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) :
    y.val ∈ interior (P : Set V) ∧
    (∀ Q, (σ Q).IsTransverse ![x.val, y.val]) ∧
    OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
      (∑ Q, Finsupp.single (σ Q) ((cross Q).defect hk b t ht)) = 0 ∧
    D.levelPathProduct (k + 1) (((D.adaptedPathPrefunctor (k + 1)).map e).toPath) = 1 := by
  classical
  have hdisj (Q : (D.adaptedComplex (k + 1)).walls) :
      Disjoint (convexHull ℝ (range ![x.val, y.val])) (σ Q).carrier := by
    rw [Matrix.range_cons_cons_empty, convexHull_pair, segment_eq_image_lineMap]
    apply disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ hz
    have hm : (Q, u) ∈ crossings x y := (mem_crossings x y Q u).mpr ⟨hu, (hσ Q) ▸ hz⟩
    simp only [he, mem_empty_iff_false] at hm
  have hyP : y.val ∈ interior (P : Set V) := by
    simpa only [AffineMap.lineMap_apply_one] using
      (D.adaptedComplex (k + 1)).lineMap_mem_interior_of_crossings_eq_empty
        P.property hx he 1 (by simp)
  refine ⟨hyP, fun Q => (σ Q).isTransverse_of_disjoint (hdisj Q), ?_, ?_⟩
  · simp only [map_sum, OrientedCell.intersectionPairing_single,
      OrientedCell.intersectionIndex_of_disjoint (hdisj _), zero_smul, Finset.sum_const_zero]
  · obtain ⟨e', he'⟩ := D.exists_segment_levelPathProduct_eq_one_of_mem_interior_adapted
      P.property ((D.adaptedPathPrefunctor (k + 1)).obj x)
      ((D.adaptedPathPrefunctor (k + 1)).obj y)
      (by simpa only [D.adaptedPathPrefunctor_obj_val] using hx)
      (by simpa only [D.adaptedPathPrefunctor_obj_val] using hyP)
    have heq : e' = (D.adaptedPathPrefunctor (k + 1)).map e :=
      PLift.ext (Subsingleton.elim _ _)
    rwa [heq] at he'

/-- Every segment with at most one adapted crossing pairs with the central
defect presentation as the logarithm of its directed transport gauged by the
lifts of its endpoint chambers. This includes both crossing directions and
segments missing every wall, exactly the alternatives in a single-crossing
subdivision of an admissible path. -/
theorem intersectionPairing_eq_log_defect_of_subsingleton_crossings
    (e : x ⟶ y) (he : (crossings x y).Subsingleton)
    (P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) (hy : y.val ∈ interior (Q : Set V)) :
    ((OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
      (∑ W, Finsupp.single (σ W) ((cross W).defect hk b t ht)) :
        (d.truncationMap ℒ (Nat.le_succ k)).ker) : d.truncatedLie ℒ (k + 1)) =
      BCHGroup.log ((t Q)⁻¹ *
        D.levelPathProduct (k + 1) (((D.adaptedPathPrefunctor (k + 1)).map e).toPath) * t P) := by
  have hcell (A B : (D.adaptedComplex (k + 1)).cellsOfCodimension 0) {z : V}
      (ha : z ∈ interior (A : Set V)) (hb : z ∈ interior (B : Set V)) : A = B := by
    apply Subtype.ext
    exact (D.adaptedComplex (k + 1)).eq_of_mem_intrinsicInterior
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp A.property).1
      (((D.adaptedComplex (k + 1)).mem_cellsOfCodimension 0 _).mp B.property).1
      (interior_subset_intrinsicInterior ha) (interior_subset_intrinsicInterior hb)
  rcases (crossings x y).eq_empty_or_nonempty with hempty | ⟨⟨W, s⟩, hWs⟩
  · obtain ⟨hyP, -, hpair, hprod⟩ :=
      intersectionPairing_eq_zero_of_crossings_eq_empty σ hσ cross hk b t ht e hempty P hx
    have hPQ := hcell P Q hyP hy
    simp only [hpair, ZeroMemClass.coe_zero, hprod, mul_one, hPQ,
      inv_mul_cancel, BCHGroup.log_one]
  · have hsingle := he.eq_singleton_of_mem hWs
    have hν : h.realCharacter (cross W).normal (y.val - x.val) ≠ 0 := by
      intro hz
      have hdir : y.val - x.val ∈ (affineSpan ℝ (W : Set V)).direction := by
        rw [← hσ W, ← (cross W).ker_normal, LinearMap.mem_ker]
        exact hz
      exact e.down.transverse W ⟨s, (mem_crossings x y W s).mp hWs⟩ hdir
    rcases lt_or_gt_of_ne hν with hv | hv
    · obtain ⟨hxW, hyW, hpair⟩ :=
        intersectionPairing_eq_log_defect_of_negative_crossing
          σ hσ cross hk b t ht e W s hsingle hv
      rwa [← hcell P (cross W).plus hx hxW, ← hcell Q (cross W).minus hy hyW] at hpair
    · obtain ⟨hxW, hyW, hpair⟩ :=
        intersectionPairing_eq_log_defect_of_positive_crossing
          σ hσ cross hk b t ht e W s hsingle hv
      rwa [← hcell P (cross W).minus hx hxW, ← hcell Q (cross W).plus hy hyW] at hpair

end Mei.DirectedDiagram
