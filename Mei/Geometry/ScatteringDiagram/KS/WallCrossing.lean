/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.Basic
public import Mei.Geometry.ScatteringDiagram.KS.LocalSigns
public import Mei.Geometry.Convex.PolyhedralComplex.LocalCrossing
public import Mei.Algebra.Lie.BCH.Sign.WallCrossing

/-!
# Geometric transport across a reconstructed wall

Near any regular point of a finite reconstructed wall, the actual path product
of an admissible segment crossing that wall is the negative sign factor at its
target times the inverse negative factor at its source. Both crossing directions
obey this formula, with the wall label inverted for positive normal velocity.
The radius is independent of the group element being reconstructed.

This is the single-crossing step of Tom Bridgeland's reconstruction argument,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4
([arXiv:1603.00416](https://arxiv.org/abs/1603.00416)). It combines the geometric
local sign theorem `eventually_sign_eq_of_mem_intrinsicInterior_wall`,
`FinitePolyhedralComplex.eventually_orderedCrossings_eq_singleton`, and
`signFactorizationEquiv_neg_mul_inv_eq_middle`. Global consistency requires
assembling these local formulas along an entire path.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.PositiveDegrees

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {k : ℕ} {P : (d.arrangementComplex h k).walls} {θ : V →L[ℝ] ℝ}

private theorem pathProduct_reconstructFinite_toPath_of_signs
    (hθP : θ ∈ intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ)))
    (g : d.truncatedGroup ℒ k)
    {x y : WallComplement (fun Q : (d.arrangementComplex h k).walls => (Q : Set (V →L[ℝ] ℝ)))}
    (e : x ⟶ y) {t : ℝ}
    (he : (d.arrangementComplex h k).orderedCrossings e = [(P, t)])
    (hx : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (x.val (i n)) =
      if θ (i n) = 0 then
        SignType.sign (x.val (i ((d.reconstructFinite h ℒ g).degree P)))
      else SignType.sign (θ (i n)))
    (hy : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (y.val (i n)) =
      if θ (i n) = 0 then
        SignType.sign (y.val (i ((d.reconstructFinite h ℒ g).degree P)))
      else SignType.sign (θ (i n))) :
    (d.reconstructFinite h ℒ g).toFiniteWallDiagram.pathProduct e.toPath =
      ((signFactorizationEquiv ℒ (y.val.toAddMonoidHom.comp i) d k).symm g .neg :
        d.truncatedGroup ℒ k) *
      ((signFactorizationEquiv ℒ (x.val.toAddMonoidHom.comp i) d k).symm g .neg :
        d.truncatedGroup ℒ k)⁻¹ := by
  let D := d.reconstructFinite h ℒ g
  have ht : (P, t) ∈ WallComplement.crossings x y :=
    ((d.arrangementComplex h k).mem_orderedCrossings e _).mp (by simp [he])
  obtain ⟨htI, htP⟩ := (WallComplement.mem_crossings x y P t).mp ht
  have htO := (e.down.crossing_mem_intrinsicInterior htI htP).1
  have hz : t * (y.val (i (D.degree P)) - x.val (i (D.degree P))) +
      x.val (i (D.degree P)) = 0 := by
    simpa only [KSSpace.continuousDual_evaluation, AffineMap.lineMap_apply_module',
      add_apply, smul_apply, sub_apply, smul_eq_mul] using D.evaluation_eq_zero P _ htP
  simp only [FiniteWallDiagram.pathProduct_toPath, he, List.reverse_singleton,
    List.map_singleton, List.prod_singleton]
  rw [KSComplex.toFiniteWallDiagram_normal, KSSpace.normal_apply,
    KSSpace.continuousDual_evaluation, sub_apply,
    KSComplex.toFiniteWallDiagram_label, d.reconstructFinite_label h ℒ g P hθP]
  -- Split the geometric zero condition before rewriting composed evaluations:
  -- the conditional's decidability argument otherwise retains the opaque composition.
  have hsign (φ : V →L[ℝ] ℝ)
      (hφ : ∀ n ∈ d.cutoff k \ {0}, SignType.sign (φ (i n)) =
        if θ (i n) = 0 then SignType.sign (φ (i (D.degree P)))
        else SignType.sign (θ (i n))) (s : SignType)
      (hside : SignType.sign (φ (i (D.degree P))) = s) :
      ∀ n ∈ d.cutoff k \ {0},
        SignType.sign ((φ.toAddMonoidHom.comp i) n) =
          if (θ.toAddMonoidHom.comp i) n = 0 then s
          else SignType.sign ((θ.toAddMonoidHom.comp i) n) := by
    intro n hn
    by_cases hzero : θ (i n) = 0
    · have hzero' : (θ.toAddMonoidHom.comp i) n = 0 := by simpa using hzero
      rw [ite_eq_left hzero']
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        ContinuousLinearMap.coe_coe] using (hφ n hn).trans (by rw [ite_eq_left hzero, hside])
    · have hzero' : (θ.toAddMonoidHom.comp i) n ≠ 0 := by simpa using hzero
      rw [ite_eq_right hzero']
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        ContinuousLinearMap.coe_coe] using (hφ n hn).trans (ite_eq_right hzero)
  split_ifs with hv
  · have hxneg : x.val (i (D.degree P)) < 0 := by nlinarith [htO.1]
    have hypos : 0 < y.val (i (D.degree P)) := by nlinarith [htO.2]
    dsimp only [D] at hxneg hypos
    have hr := d.signFactorizationEquiv_neg_mul_inv_eq_middle ℒ
      (θ.toAddMonoidHom.comp i) (y.val.toAddMonoidHom.comp i) k
      (x.val.toAddMonoidHom.comp i)
      (hsign y.val hy .pos (by simpa only [SignType.pos_eq_one] using sign_pos hypos))
      (hsign x.val hx .neg (by simpa only [SignType.neg_eq_neg_one] using sign_neg hxneg)) g
    simpa using congrArg Inv.inv hr.symm
  · have hvne := (d.arrangementComplex h k).normal_velocity_ne_zero
      ((KSSpace.continuousDual h).normal (D.degree P)) e
      (a := (P, t)) (by simp [he]) (D.ker_normal P)
    have hvneg : y.val (i (D.degree P)) - x.val (i (D.degree P)) < 0 := by
      have hvne' : y.val (i (D.degree P)) - x.val (i (D.degree P)) ≠ 0 := by
        simpa only [KSComplex.toFiniteWallDiagram_normal, KSSpace.normal_apply,
          KSSpace.continuousDual_evaluation, sub_apply] using hvne
      exact lt_of_le_of_ne (not_lt.mp hv) hvne'
    have hxpos : 0 < x.val (i (D.degree P)) := by nlinarith [htO.1]
    have hyneg : y.val (i (D.degree P)) < 0 := by nlinarith [htO.2]
    dsimp only [D] at hxpos hyneg
    exact (d.signFactorizationEquiv_neg_mul_inv_eq_middle ℒ
      (θ.toAddMonoidHom.comp i) (x.val.toAddMonoidHom.comp i) k
      (y.val.toAddMonoidHom.comp i)
      (hsign x.val hx .pos (by simpa only [SignType.pos_eq_one] using sign_pos hxpos))
      (hsign y.val hy .neg (by simpa only [SignType.neg_eq_neg_one] using sign_neg hyneg)) g).symm

/-- A regular reconstructed wall has a neighborhood where every admissible
segment crossing it computes the quotient of the endpoint negative factors.
The same neighborhood works for every truncated group element and both directions. -/
theorem exists_radius_pathProduct_reconstructFinite_toPath
    (hθP : θ ∈ (P : Set (V →L[ℝ] ℝ)))
    (hθ : θ ∉ singularSupport
      (fun Q : (d.arrangementComplex h k).walls => (Q : Set (V →L[ℝ] ℝ)))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : d.truncatedGroup ℒ k)
      (x y : WallComplement
        (fun Q : (d.arrangementComplex h k).walls => (Q : Set (V →L[ℝ] ℝ))))
      (e : x ⟶ y), dist x.val θ < ε → dist y.val θ < ε →
      (∃ t, (P, t) ∈ WallComplement.crossings x y) →
      (d.reconstructFinite h ℒ g).toFiniteWallDiagram.pathProduct e.toPath =
        ((signFactorizationEquiv ℒ (y.val.toAddMonoidHom.comp i) d k).symm g .neg :
          d.truncatedGroup ℒ k) *
        ((signFactorizationEquiv ℒ (x.val.toAddMonoidHom.comp i) d k).symm g .neg :
          d.truncatedGroup ℒ k)⁻¹ := by
  have hθint := mem_intrinsicInterior_of_notMem_singularSupport hθP hθ
  let D := d.reconstructFinite h ℒ (1 : d.truncatedGroup ℒ k)
  have hs := d.eventually_sign_eq_of_mem_intrinsicInterior_wall h P.property
    (D.degree_mem P) (D.degree_ne_zero P)
    (fun φ hφ => by simpa only [KSSpace.continuousDual_evaluation] using
      D.evaluation_eq_zero P φ hφ) hθint
  have hc := (d.arrangementComplex h k).eventually_orderedCrossings_eq_singleton hθP hθ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ((hs.prod_nhds hs).and hc)
  refine ⟨ε, hε, fun g x y e hx hy ⟨t, ht⟩ => ?_⟩
  have hp : (x.val, y.val) ∈ Metric.ball (θ, θ) ε := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using (And.intro hx hy)
  have hq := hball hp
  apply d.pathProduct_reconstructFinite_toPath_of_signs h ℒ hθint g e
    (hq.2 x y e rfl rfl t ht)
  · simpa only [D, ← d.reconstructFinite_degree_eq h ℒ g 1] using hq.1.1
  · simpa only [D, ← d.reconstructFinite_degree_eq h ℒ g 1] using hq.1.2

end Mei.PositiveDegrees
