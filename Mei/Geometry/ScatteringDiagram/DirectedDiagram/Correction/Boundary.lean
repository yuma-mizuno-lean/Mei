/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Family
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Family
public import Mei.Geometry.Convex.PolyhedralCochain.Differential
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Cochain

/-!
# Signed boundaries of mixed-degree joint corrections

The nonzero homogeneous components of local joint loop logarithms give one
finite family of outgoing walls. Each integral normal represents the contracted
orientation of its swept joint. If the kernel-valued obstruction cochain is
closed, the signed boundary of the logarithmic correction presentation is the
entire joint obstruction cochain, with its original orientations and coefficients.
Thus the different geometric sweeping directions can be used simultaneously.

The construction combines `DirectedDiagram.exists_pos_joint_loop_obstruction`,
`DirectedWall.exists_cooriented_sweep`, and the componentwise sweep homotopy
formula. The source is reconstructed with `DirectSum.sum_support_decompose`;
coefficient projections from `DirectSum.decomposeLinearEquiv` commute with the
coboundary by `PolyhedralCochain.map_coboundary`. Thus closedness of the total
obstruction implies closedness of every homogeneous component. No relation
between distinct homogeneous sweeping directions is required.
This is the signed homogeneous assembly in Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, proof of Theorem 2.6.
Closedness of the obstruction and consistency of the corrected diagram remain
separate statements.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Construct all nonzero homogeneous joint corrections with the signs of the
cochain sweep. Each wall is outgoing, has a pure birth logarithm at the correction
order, and has the contracted coorientation. If the kernel-valued source
cochain is closed, their combined logarithmic presentation has signed
boundary equal to the full source obstruction cochain. The loops need only lie
in the indicated neighborhoods; they need not already be consistent at the new
order. Joint orientations are arbitrary and fixed independently of the loops. -/
theorem exists_joint_sweep_correction_family {k : ℕ}
    (hk : D.LevelConsistent k)
    (σ : (D.adaptedComplex (k + 1)).joints → OrientedCell h 2)
    (hσ : ∀ J, (σ J).carrier = (J : Set V))
    (q : (D.adaptedComplex (k + 1)).joints → V)
    (hq : ∀ J : (D.adaptedComplex (k + 1)).joints,
      q J ∈ intrinsicInterior ℝ (J : Set V))
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k + 1 ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ r : (D.adaptedComplex (k + 1)).joints → ℝ, (∀ J, 0 < r J) ∧
      ∀ (x : (D.adaptedComplex (k + 1)).joints →
          WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
        (p : ∀ J, AdmissiblePLPath (x J) (x J)),
        (∀ J z, z ∈ (p J).vertices → z.val ∈ Metric.ball (q J) (r J)) →
        letI := Fintype.ofFinite (D.adaptedComplex (k + 1)).joints
        let c := fun a : D.JointCorrectionIndex x p =>
          (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
            (log (D.levelPathProduct (k + 1) (p a.1))) a.2.val : d.truncatedLie ℒ (k + 1))
        ∃ (htrans : ∀ a : D.JointCorrectionIndex x p,
            i (ρ a.2.val) ∉ (affineSpan ℝ (σ a.1).carrier).direction)
          (E : DirectedDiagram (d := d) h H (D.JointCorrectionIndex x p)),
          (∀ a : D.JointCorrectionIndex x p,
            (E.wall a).support = ((σ a.1).sweep (ρ a.2.val) (htrans a)).carrier ∧
            (∀ v : V, SignType.sign (h.realCharacter (E.wall a).normal v) =
              ((σ a.1).sweep (ρ a.2.val) (htrans a)).orientation.evalSign
                (fun _ : Fin 1 => v)) ∧
            a.2.val ∈ (E.wall a).ray.rayDegrees ∧
            (∃ b ∈ ℒ a.2.val, (E.wall a).label = d.expToCompletion ℒ (-b)) ∧
            (E.wall a).Outgoing ∧ log (CompletedGroup.projection (k + 1) (E.wall a).label) = -c a ∧
            ∀ l : ℕ, a ∈ E.active l ↔ k + 1 ≤ l) ∧
          (PolyhedralCochain.coboundary
              (D.jointObstructionCochain σ x p hσ hk) = 0 →
            PolyhedralCochain.coboundaryOfFinsupp (R := R)
              (∑ a : D.JointCorrectionIndex x p,
                Finsupp.single ((σ a.1).sweep (ρ a.2.val) (htrans a))
                  (log (CompletedGroup.projection (k + 1) (E.wall a).label))) =
              ∑ J : (D.adaptedComplex (k + 1)).joints,
                PolyhedralCochain.mk (σ J) (log (D.levelPathProduct (k + 1) (p J)))) := by
  classical
  choose r hr hlocal using fun J : (D.adaptedComplex (k + 1)).joints =>
    D.exists_pos_joint_loop_obstruction J.property (hq J) initial hfull hpure
  refine ⟨r, hr, fun x p hp => ?_⟩
  dsimp only
  let := Fintype.ofFinite (D.adaptedComplex (k + 1)).joints
  let c := fun a : D.JointCorrectionIndex x p =>
    (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
      (log (D.levelPathProduct (k + 1) (p a.1))) a.2.val : d.truncatedLie ℒ (k + 1))
  -- Only nonzero components occur, and consistency fixes their common birth order.
  have hc (a : D.JointCorrectionIndex x p) : c a ≠ 0 :=
    fun hz => (DFinsupp.mem_support_toFun _ _).mp a.2.property (Subtype.ext hz)
  have hd (a : D.JointCorrectionIndex x p) : d.degree a.2.val = (k : ℤ) + 1 :=
    D.degree_jointCorrectionIndex x p hk a
  have htrans (a : D.JointCorrectionIndex x p) :
      i (ρ a.2.val) ∉ (affineSpan ℝ (σ a.1).carrier).direction := by
    rw [hσ]
    exact fun ht => hc a ((hlocal a.1 (x a.1) (p a.1) (hp a.1) a.2.val (by
      exact_mod_cast hd a)).1 ht)
  -- Choose each integral normal with the contracted orientation before assembling the family.
  have hex (a : D.JointCorrectionIndex x p) :
      ∃ W : DirectedWall (d := d) h H,
        W.support = ((σ a.1).sweep (ρ a.2.val) (htrans a)).carrier ∧
        (∀ v : V, SignType.sign (h.realCharacter W.normal v) =
          ((σ a.1).sweep (ρ a.2.val) (htrans a)).orientation.evalSign (fun _ : Fin 1 => v)) ∧
        a.2.val ∈ W.ray.rayDegrees ∧
        (∃ b ∈ ℒ a.2.val, W.label = d.expToCompletion ℒ (-b)) ∧ W.Outgoing ∧
        log (CompletedGroup.projection (k + 1) W.label) = -c a ∧
        ∀ l : ℕ, CompletedGroup.projection l W.label = 1 ↔
          c a = 0 ∨ (l : ℤ) < d.degree a.2.val := by
    obtain ⟨m, _, hmker, hmem⟩ :=
      (hlocal a.1 (x a.1) (p a.1) (hp a.1) a.2.val (by exact_mod_cast hd a)).2
        (by simpa only [hσ] using htrans a)
    have hpiece : d.truncatedGrading ℒ (k + 1) a.2.val ≠ ⊥ := by
      intro he
      have hm := (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
        (log (D.levelPathProduct (k + 1) (p a.1))) a.2.val).property
      exact hc a (by simpa only [he, Submodule.mem_bot] using hm)
    exact DirectedWall.exists_cooriented_sweep (σ a.1)
      (d.mem_cutoff.mp (d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hpiece).1).1
      (htrans a) m (by simpa only [hσ] using hmker) (k + 1) (by rw [hd a]; omega) (c a) hmem
  choose W hs hsign hray hpureW hout hlog hborn using hex
  refine ⟨htrans, ofFinite W, ?_, ?_⟩
  · intro a
    simp only [ofFinite_wall]
    refine ⟨hs a, hsign a, hray a, hpureW a, hout a, hlog a, fun l => ?_⟩
    rw [mem_active, ofFinite_wall]
    have he := not_congr (hborn a l)
    simp only [hc a, false_or, not_lt, hd a] at he
    exact he.trans (by omega)
  · intro hclosed
    -- Coefficient projections commute with the coboundary on the cochain quotient.
    have hcomponent (n : Γ) : PolyhedralCochain.coboundaryOfFinsupp (R := R)
        (∑ J : (D.adaptedComplex (k + 1)).joints, Finsupp.single (σ J)
          (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
            (log (D.levelPathProduct (k + 1) (p J))) n : d.truncatedLie ℒ (k + 1))) = 0 := by
      let f := (d.truncatedGrading ℒ (k + 1) n).subtype ∘ₗ
        DirectSum.component R Γ (d.truncatedGrading ℒ (k + 1) ·) n ∘ₗ
        (DirectSum.decomposeLinearEquiv (d.truncatedGrading ℒ (k + 1))).toLinearMap ∘ₗ
        (d.truncationMap ℒ (Nat.le_succ k)).ker.subtype
      have hf (J : (D.adaptedComplex (k + 1)).joints) :
          f (D.loopObstruction hk (p J)) =
            (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
              (log (D.levelPathProduct (k + 1) (p J))) n : d.truncatedLie ℒ (k + 1)) := by
        simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
          DirectSum.decomposeLinearEquiv_apply, ← DirectSum.apply_eq_component,
          Submodule.subtype_apply, D.coe_loopObstruction]
      have hm := congrArg (PolyhedralCochain.map f) hclosed
      rw [PolyhedralCochain.map_coboundary, D.jointObstructionCochain_def, map_sum] at hm
      simp only [PolyhedralCochain.map_mk, hf, map_zero] at hm
      simpa only [← PolyhedralCochain.coboundary_ofFinsupp, map_sum,
        PolyhedralCochain.ofFinsupp_single] using hm
    -- Discarding zero components does not alter any homogeneous source presentation.
    have hfiber (n : Γ) :
        (∑ a ∈ Finset.univ.filter (fun a : D.JointCorrectionIndex x p => a.2.val = n),
          Finsupp.single (σ a.1) (c a)) =
        ∑ J : (D.adaptedComplex (k + 1)).joints, Finsupp.single (σ J)
          (DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
            (log (D.levelPathProduct (k + 1) (p J))) n : d.truncatedLie ℒ (k + 1)) := by
      rw [Finset.sum_filter, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro J _
      dsimp only [c]
      let f := DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
        (log (D.levelPathProduct (k + 1) (p J)))
      rw [Finset.sum_coe_sort f.support (fun m =>
        if m = n then Finsupp.single (σ J) (f m : d.truncatedLie ℒ (k + 1)) else 0)]
      by_cases hn : n ∈ f.support
      · simp only [Finset.sum_ite_eq', ite_eq_left hn]
        rfl
      · have hz := DFinsupp.notMem_support_iff.mp hn
        dsimp only [f] at hz
        simp only [Finset.sum_ite_eq', ite_eq_right hn, hz, ZeroMemClass.coe_zero,
          Finsupp.single_zero]
    have hboundary := PolyhedralCochain.coboundaryOfFinsupp_sum_sweep_of_fiberwise_closed (R := R)
      (fun a : D.JointCorrectionIndex x p => a.2.val) ρ (fun a => σ a.1) htrans c
      (fun n => by rw [hfiber]; exact hcomponent n)
    -- Sum the actual homogeneous components back to each original loop logarithm.
    have hsource : (∑ a : D.JointCorrectionIndex x p, PolyhedralCochain.mk (R := R) (σ a.1) (c a)) =
        ∑ J : (D.adaptedComplex (k + 1)).joints,
          PolyhedralCochain.mk (σ J) (log (D.levelPathProduct (k + 1) (p J))) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro J _
      dsimp only [c]
      rw [← map_sum]
      congr 1
      let f := DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
        (log (D.levelPathProduct (k + 1) (p J)))
      exact (Finset.sum_coe_sort f.support
        (fun n => (f n : d.truncatedLie ℒ (k + 1)))).trans
          (DirectSum.sum_support_decompose (d.truncatedGrading ℒ (k + 1))
            (log (D.levelPathProduct (k + 1) (p J))))
    simp only [ofFinite_wall, hlog, Finsupp.single_neg]
    rw [Finset.sum_neg_distrib, map_neg, hboundary, neg_neg, hsource]

end Mei.DirectedDiagram
