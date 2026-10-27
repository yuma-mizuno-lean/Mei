/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Path
import Mei.Geometry.Convex.PolyhedralCochain.Crossing
import Mei.Geometry.Convex.PolyhedralCochain.ParameterSubdivision

/-!
# Crossing defects along a given polygonal path

The signed sum of central crossing defects computes the logarithm of the actual
path transport gauged by its endpoint chamber lifts. In particular, the negative
signed sum around any adapted loop is its central loop obstruction. The signs
come from the geometric crossing word; a positive crossing contributes the
positive defect, while the additive wall-crossing convention contributes its
negative.

The construction combines the subdivided transport identity
`DirectedDiagram.exists_subdivision_log_levelPathProduct_eq_sum_intersectionPairing`
with `Quiver.Path.IsSubdivision.addWeightOfEPs_intersectionPairing_eq` and
`Quiver.Path.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum`.
Thus it computes transport along the given path using its original segment
pairings. The auxiliary finite diagram stores negative defect exponentials;
its group identity follows from the logarithmic identity and the central estimate
`LieSubalgebra.log_wallPathProduct_sub_crossingSum_mem`.

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
  classical
  obtain ⟨q, hpq, _, hlog⟩ :=
    exists_subdivision_log_levelPathProduct_eq_sum_intersectionPairing
      σ hσ cross hk b t ht p P Q hx hy
  let c := fun W => (cross W).defect hk b t ht
  have hsupport : ∀ τ ∈ (∑ W, Finsupp.single (σ W) (c W)).support, ∃ W, τ = σ W := by
    intro τ hτ
    obtain ⟨W, _, hW⟩ := Finsupp.mem_support_finsetSum τ hτ
    exact ⟨W, ((Finsupp.mem_support_single _ _ _).mp hW).1⟩
  -- State the pairing comparison over the oriented carriers, then rewrite them
  -- to the adapted wall family so the original paths can be used directly.
  have hpair : ∀ {x y : WallComplement (fun W => (σ W).carrier)}
      (p q : AdmissiblePLPath x y), p.IsSubdivision q →
      q.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] (∑ W, Finsupp.single (σ W) (c W))) =
      -p.wallCrossingSum (fun W => h.realCharacter (cross W).normal) c := by
    intro x y p q hpq
    rw [hpq.addWeightOfEPs_intersectionPairing_eq _ hsupport]
    exact p.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum
      (fun W => h.realCharacter (cross W).normal) c (fun W _ v => (cross W).sign_normal v)
  rw [show (fun W => (σ W).carrier) =
    (fun W : (D.adaptedComplex (k + 1)).walls => (W : Set V)) from funext hσ] at hpair
  rw [hlog]
  simpa only [map_neg, AddMonoidHom.map_wallCrossingSum, LinearMap.toAddMonoidHom_coe,
    LieHom.coe_toLinearMap, LieIdeal.incl_apply, c] using
    congrArg (d.truncationMap ℒ (Nat.le_succ k)).ker.incl.toLinearMap.toAddMonoidHom
      (hpair p q hpq)

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
  rw [Submodule.mem_bot, sub_eq_zero, ← A.pathProduct_eq_wallPathProduct hcomm] at he
  apply log_injective
  rw [he, log_inv_mul_levelPathProduct_mul_eq_neg_wallCrossingSum_defect
    σ hσ cross hk b t ht p P Q hx hy]
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
