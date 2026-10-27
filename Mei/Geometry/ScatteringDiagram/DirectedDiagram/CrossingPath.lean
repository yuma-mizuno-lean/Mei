/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Basic
public import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Realizing crossing paths and summing their central defects

A geometric adapted-wall crossing can be realized between any prescribed
interior points of its incident full cells. The extra segments stay inside the
cell interiors and have identity transport. Consequently every finite composable
sequence of such crossings has an actual admissible path realizing it.

The transport is the reverse-ordered product of the prescribed crossing labels.
For lower-order chamber lifts, the logarithm of the gauged transport is the sum
of the crossing defects. On a closed sequence it is the actual loop obstruction,
independently of the chosen interior points. The sequence is a `Quiver.Path` on
the full cells, with arrows assigned geometric crossings; `Quiver.Path.addWeight`
sums the coefficients with multiplicity. No higher-order consistency or
commutation of the individual wall labels is assumed.

The construction uses `AdaptedWallCrossing.realized`, convexity of full cell
interiors, and `LieHom.logDefect_mul`. It supplies the finite-path comparison in
the central obstruction argument of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, proof of Theorem 2.6. Identifying a geometric
meridian's signed incidences with the facets of a cochain is a separate statement.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι}

namespace AdaptedWallCrossing

/-- Realize a geometric crossing between any two interior points of its stored
incident chambers, with exactly the prescribed crossing label. -/
theorem exists_path_levelPathProduct_eq_label {l : ℕ} {σ : OrientedCell h 1}
    {hσ : σ.carrier ∈ (D.adaptedComplex l).walls}
    (c : D.AdaptedWallCrossing σ hσ)
    (x y : WallComplement (fun j : D.active l => (D.wall j).support))
    (hx : x.val ∈ interior (c.minus : Set V))
    (hy : y.val ∈ interior (c.plus : Set V)) :
    ∃ p : AdmissiblePLPath x y,
      D.levelPathProduct l p =
        D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal := by
  obtain ⟨_, _, _, _, _, _, a, b, e, _, _, ha, hb, he⟩ := c.realized
  obtain ⟨u, hu⟩ := D.exists_segment_levelPathProduct_eq_one_of_mem_interior_adapted
    c.minus.property x a hx ha
  obtain ⟨v, hv⟩ := D.exists_segment_levelPathProduct_eq_one_of_mem_interior_adapted
    c.plus.property b y hb hy
  exact ⟨(u.toPath.comp e.toPath).comp v.toPath, by simp [hu, hv, he]⟩

end AdaptedWallCrossing

variable {k : ℕ}
  [Quiver ((D.adaptedComplex (k + 1)).cellsOfCodimension 0)]
  (σ : ∀ {P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0},
    (P ⟶ Q) → OrientedCell h 1)
  (hσ : ∀ {P Q} (e : P ⟶ Q), (σ e).carrier ∈ (D.adaptedComplex (k + 1)).walls)
  (cross : ∀ {P Q} (e : P ⟶ Q), D.AdaptedWallCrossing (σ e) (hσ e))
  (hminus : ∀ {P Q} (e : P ⟶ Q), (cross e).minus = P)
  (hplus : ∀ {P Q} (e : P ⟶ Q), (cross e).plus = Q)
  (hk : D.LevelConsistent k)
  (b : WallComplement (fun j : D.active k => (D.wall j).support))
  (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
  (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)),
    x.val ∈ interior (P : Set V) →
    (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)
  (z : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 →
    WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
  (hz : ∀ P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0,
    (z P).val ∈ interior (P : Set V))

include hminus hplus hz in
/-- Realize any composable crossing sequence between prescribed chamber points.
Its transport is the ordered crossing product, and its gauged logarithm is the
sum of the actual kernel-valued crossing defects. -/
theorem exists_path_log_eq_addWeight_defect
    {P Q : (D.adaptedComplex (k + 1)).cellsOfCodimension 0} (q : Quiver.Path P Q) :
    ∃ p : AdmissiblePLPath (z P) (z Q),
      D.levelPathProduct (k + 1) p = MulOpposite.unop (q.weight (fun e =>
        MulOpposite.op (D.wallCrossingLabel ⟨(σ e).carrier, hσ e⟩
          (h.realCharacter (cross e).normal) (cross e).ker_normal))) ∧
      log ((t Q)⁻¹ * D.levelPathProduct (k + 1) p * t P) =
        (↑(q.addWeight (fun e => (cross e).defect hk b t ht)) :
          d.truncatedLie ℒ (k + 1)) := by
  induction q with
  | nil => exact ⟨Quiver.Path.nil, by simp, by simp⟩
  | @cons Q S q e ih =>
    obtain ⟨p, hprod, hp⟩ := ih
    obtain ⟨r, hr⟩ := (cross e).exists_path_levelPathProduct_eq_label
      (z Q) (z S) (by rw [hminus]; exact hz Q) (by rw [hplus]; exact hz S)
    refine ⟨p.comp r, ?_, ?_⟩
    · simp only [D.levelPathProduct_comp, hprod, hr, Quiver.Path.weight_cons,
        MulOpposite.unop_mul, MulOpposite.unop_op]
    let f := d.truncationMap ℒ (Nat.le_succ k)
    have hX : f.bchGroupMap (D.levelPathProduct (k + 1) p) *
        f.bchGroupMap (t P) = f.bchGroupMap (t Q) := by
      have hm := D.adapted_chamber_lift_path_mem_ker (Nat.le_succ k) hk b t ht
        p P Q (hz P) (hz Q)
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_assoc] at hm
      exact (inv_mul_eq_one.mp hm).symm
    have hY : f.bchGroupMap (D.levelPathProduct (k + 1) r) *
        f.bchGroupMap (t Q) = f.bchGroupMap (t S) := by
      simpa only [hr, hminus, hplus] using (cross e).truncation_label_mul hk b t ht
    have he := congrArg (fun a : f.ker => (a : d.truncatedLie ℒ (k + 1)))
      (f.logDefect_mul (t P) (t Q) (t S)
        (D.levelPathProduct (k + 1) p) (D.levelPathProduct (k + 1) r) hX hY)
    simp only [LieHom.coe_logDefect, LieSubmodule.coe_add] at he
    rw [D.levelPathProduct_comp, he, hp, hr]
    simp only [Quiver.Path.addWeight_cons, LieSubmodule.coe_add]
    have hd := (cross e).coe_defect hk b t ht
    simp only [hminus, hplus] at hd
    rw [← hd]
    exact add_comm _ _

include hminus hplus hz in
/-- A closed crossing sequence has an actual admissible loop whose obstruction
is the sum of its crossing defects. The initial chamber lift disappears because
the successive truncation kernel is central. -/
theorem exists_loopObstruction_eq_addWeight_defect
    {P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0} (q : Quiver.Path P P) :
    ∃ p : AdmissiblePLPath (z P) (z P),
      D.levelPathProduct (k + 1) p = MulOpposite.unop (q.weight (fun e =>
        MulOpposite.op (D.wallCrossingLabel ⟨(σ e).carrier, hσ e⟩
          (h.realCharacter (cross e).normal) (cross e).ker_normal))) ∧
      D.loopObstruction hk p = q.addWeight (fun e => (cross e).defect hk b t ht) := by
  obtain ⟨p, hprod, hp⟩ := exists_path_log_eq_addWeight_defect
    σ hσ cross hminus hplus hk b t ht z hz q
  refine ⟨p, hprod, Subtype.ext ?_⟩
  have hm : D.levelPathProduct (k + 1) p ∈
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap.ker := by
    rw [MonoidHom.mem_ker, D.truncation_levelPathProduct (Nat.le_succ k)]
    exact (D.levelConsistent_iff_loops k).mp hk _ _
  have hc := Subgroup.mem_center_iff.mp
    ((d.truncationMap ℒ (Nat.le_succ k)).ker_bchGroupMap_le_center
      (d.ker_truncationMap_succ_le_center ℒ k) hm) ((t P)⁻¹)
  have he : (t P)⁻¹ * D.levelPathProduct (k + 1) p * t P =
      D.levelPathProduct (k + 1) p := by
    rw [hc, mul_assoc, inv_mul_cancel, mul_one]
  simpa only [he, coe_loopObstruction] using hp

end Mei.DirectedDiagram
