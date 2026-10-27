/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Independence
public import Mei.Geometry.Convex.PolyhedralCochain.LocalCrossing

/-!
# Pairing central crossing defects with actual segments

The finite crossing-defect presentation evaluates on a sufficiently short
positive crossing as the logarithm of the actual directed transport, gauged by
the two incident chamber lifts. The segment is transverse to every wall in the
presentation, including artificial walls. No consistency at the higher cutoff
is assumed, and repeated indexed directed walls retain their combined label.

The geometric input is `PolyhedralCochain.exists_ball_intersectionPairing_eq`;
the transport input is `AdaptedWallCrossing.eventually_exists_log_defect_eq`.
Their comparison supplies the local crossing calculation for the central
obstruction argument in Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, proof of Theorem 2.6. Passing from local
crossings to a whole meridian still requires subdivision and the signed
boundary comparison.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι} {k : ℕ}

/-- At every adapted wall interior point, every sufficiently short positive
crossing realizes the pairing of the entire central defect presentation as the
gauged transport logarithm. Its endpoints lie in the stored incident chamber
interiors, and its affine test is transverse to every cell of the presentation. -/
theorem eventually_exists_intersectionPairing_eq_log_defect
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
    (Q : (D.adaptedComplex (k + 1)).walls) {q v : V}
    (hq : q ∈ intrinsicInterior ℝ (Q : Set V))
    (hv : 0 < h.realCharacter (cross Q).normal v) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
        (e : x ⟶ y),
        x.val = q - a • v ∧ y.val = q + a • v ∧
        x.val ∈ interior ((cross Q).minus : Set V) ∧
        y.val ∈ interior ((cross Q).plus : Set V) ∧
        (∀ P, (σ P).IsTransverse ![x.val, y.val]) ∧
        ((OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
          (∑ P, Finsupp.single (σ P) ((cross P).defect hk b t ht)) :
            (d.truncationMap ℒ (Nat.le_succ k)).ker) : d.truncatedLie ℒ (k + 1)) =
          BCHGroup.log ((t (cross Q).plus)⁻¹ *
            D.levelPathProduct (k + 1) e.toPath * t (cross Q).minus) := by
  classical
  obtain ⟨ε, hε, hpair⟩ := PolyhedralCochain.exists_ball_intersectionPairing_eq
    (R := R) (E := (d.truncationMap ℒ (Nat.le_succ k)).ker)
    (D.adaptedComplex (k + 1)) σ hσ Q hq
  have hnear : ∀ᶠ a : ℝ in 𝓝[>] 0,
      q - a • v ∈ Metric.ball q ε ∧ q + a • v ∈ Metric.ball q ε := by
    have hc : Continuous (fun a : ℝ => (q - a • v, q + a • v)) := by fun_prop
    have htend : Tendsto (fun a : ℝ => (q - a • v, q + a • v))
        (𝓝 0) (𝓝 (q, q)) := by simpa using hc.tendsto 0
    exact (htend.eventually (prod_mem_nhds (Metric.ball_mem_nhds q hε)
      (Metric.ball_mem_nhds q hε))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, (cross Q).eventually_exists_log_defect_eq hk b t ht
    (by rwa [hσ Q]) hv, self_mem_nhdsWithin] with a ha he ha0
  obtain ⟨x, y, e, hx, hy, hxm, hyp, he⟩ := he
  have ha0 : 0 < a := ha0
  have hdiff : y.val - x.val = (2 * a) • v := by rw [hx, hy]; module
  have hsign : (σ Q).orientation.evalSign (fun _ : Fin 1 => y.val - x.val) = 1 := by
    rw [← (cross Q).sign_normal, hdiff, map_smul, smul_eq_mul]
    exact sign_pos (mul_pos (by positivity) hv)
  have hmid : q ∈ segment ℝ x.val y.val := by
    rw [segment_eq_image_lineMap]
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    rw [AffineMap.lineMap_apply_module', hx, hy]
    module
  obtain ⟨htrans, hvalue⟩ := hpair (hx ▸ ha.1) (hy ▸ ha.2) hmid (by rw [hsign]; decide)
  refine ⟨x, y, e, hx, hy, hxm, hyp, htrans, ?_⟩
  rw [hvalue, hsign, SignType.coe_one, one_smul, he]

end Mei.DirectedDiagram
