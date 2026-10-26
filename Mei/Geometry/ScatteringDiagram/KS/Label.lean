/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Transport
public import Mei.Geometry.Convex.PolyhedralComplex.LocalCrossing
public import Mei.Algebra.Lie.BCH.Sign.WallCrossing

/-!
# Recovering wall labels from chamber transport

At every regular point of a wall of a consistent completed KS diagram, its
finite-order label is the middle sign factor of the positive-to-negative
chamber transport. The complexes may vary arbitrarily with the cutoff. No
finite generation, saturation or genericity with respect to the degree
hyperplanes is required.

A short segment through the wall in the degree direction crosses only that
wall. Its product is the wall label in the positive-to-negative direction.
The endpoint formula `CompletedDiagram.pathProduct_eq_signFactorizationEquiv_symm_neg_mul_inv`
and the algebraic identity
`PositiveDegrees.signFactorizationEquiv_neg_mul_inv_eq_middle` identify that
product with the middle factor. The geometric input is
`FinitePolyhedralComplex.eventually_exists_orderedCrossings_eq_singleton`.
This is the local label recovery in Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416).
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CompletedDiagram

open PositiveDegrees

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C : ℕ → FinitePolyhedralComplex h} (D : CompletedDiagram s d ℒ C)

/-- The finite label at a regular wall point is the middle sign factor of the
transport from the positive degree point to the negative one. -/
theorem label_eq_signFactorizationEquiv_symm_zero (hD : D.Consistent) (k : ℕ)
    (P : (C k).walls) {θ : V} (hθP : θ ∈ (P : Set V))
    (hθ : θ ∉ singularSupport (fun Q : (C k).walls => (Q : Set V))) :
    (D.diagram k).label P =
      ((signFactorizationEquiv ℒ (s.evaluation θ) d k).symm
        (CompletedGroup.projection k (D.transport hD D.degreePoint D.negDegreePoint)) .zero :
          d.truncatedGroup ℒ k) := by
  have hp := s.evaluation_degreePoint_pos d
    ((D.diagram k).degree_mem P) ((D.diagram k).degree_ne_zero P)
  have hv : s.degreePoint d ∉ (affineSpan ℝ (P : Set V)).direction := by
    rw [← (D.diagram k).ker_normal P, LinearMap.mem_ker, KSSpace.normal_apply]
    exact hp.ne'
  have hs := s.eventually_sign_evaluation_add_smul_degreePoint d k θ
  have hn : Tendsto (fun a : ℝ => -a) (𝓝 0) (𝓝 0) := by
    simpa using continuous_neg.tendsto (0 : ℝ)
  have hshort := (C k).eventually_exists_orderedCrossings_eq_singleton hθP hθ hv
  have hapos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, ⟨x, y, e, hx, hy, he⟩, hpos, hneg⟩ :=
    (hapos.and
      (hshort.and ((hs.filter_mono nhdsWithin_le_nhds).and
        ((hn.eventually hs).filter_mono nhdsWithin_le_nhds)))).exists
  have hd : y.val - x.val = (-2 * a) • s.degreePoint d := by rw [hx, hy]; module
  have hvel : (D.diagram k).toFiniteWallDiagram.normal P (y.val - x.val) < 0 := by
    rw [KSComplex.toFiniteWallDiagram_normal, hd, map_smul, KSSpace.normal_apply]
    exact mul_neg_of_neg_of_pos (by linarith) hp
  have hlabel : (D.diagram k).toFiniteWallDiagram.pathProduct e.toPath =
      (D.diagram k).label P := by
    rw [FiniteWallDiagram.pathProduct_toPath, he]
    simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton,
      ite_eq_right hvel.not_gt, KSComplex.toFiniteWallDiagram_label]
  rw [← hlabel, D.pathProduct_eq_signFactorizationEquiv_symm_neg_mul_inv hD k e.toPath]
  apply d.signFactorizationEquiv_neg_mul_inv_eq_middle ℒ (s.evaluation θ)
    (s.evaluation x.val) k (s.evaluation y.val)
  · intro n hn
    simpa [hx, sign_pos ha] using hpos n hn
  · intro n hn
    simpa [hy, sub_eq_add_neg, sign_neg (neg_neg_of_pos ha)] using hneg n hn

end Mei.CompletedDiagram
