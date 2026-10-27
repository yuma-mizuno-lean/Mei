/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Localization
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Sweep

/-!
# Outgoing walls for nonzero joint obstruction components

Every nonzero correction-degree component of a sufficiently local joint loop
product determines an actual outgoing directed wall. Its support is the joint
swept in the negative geometric degree direction. Lift the component to its
original homogeneous wall space and use the negative completed exponential as
label. The label is trivial below the correction order and nontrivial at that
order, with logarithm equal to the negative obstruction component.

The normal and transversality come from
`DirectedDiagram.exists_pos_joint_loop_obstruction`; positive-degree support
comes from the truncated grading. `DirectedWall.exists_outgoing_sweep` supplies
the wall. This implements the individual homogeneous-wall construction in
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6. The result does not yet assemble the walls into a consistent
correction diagram or identify the orientation sign of a joint cochain.
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

/-- Near an adapted joint, every nonzero component in the correction degree
has an outgoing swept wall with a pure homogeneous negative-exponential label.
The radius is uniform in the loop and degree. The label is born exactly at the
correction order. No lower-order consistency hypothesis is needed for this
individual-wall construction. -/
theorem exists_outgoingWall_joint_obstruction {k : ℕ} {J : Set V}
    (hJ : J ∈ (D.adaptedComplex k).joints) {q : V}
    (hq : q ∈ intrinsicInterior ℝ J) (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ r > 0, ∀ (x : WallComplement (fun j : D.active k => (D.wall j).support))
      (p : AdmissiblePLPath x x), (∀ z ∈ p.vertices, z.val ∈ Metric.ball q r) →
      ∀ n : Γ, d.degree n = k →
        let c := (DirectSum.decompose (d.truncatedGrading ℒ k)
          (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k)
        c ≠ 0 → ∃ (W : DirectedWall (d := d) h H) (a : L),
          W.Outgoing ∧ W.support = Convex.sweep J (i (ρ n)) ∧ n ∈ W.ray.rayDegrees ∧
          (h.realCharacter W.normal).ker = (affineSpan ℝ J).direction ⊔ ℝ ∙ i (ρ n) ∧
          a ∈ H.wall n W.normal ∧ W.label = d.expToCompletion ℒ (-a) ∧
          (d.degreeIdeal ℒ k).mkQ a = c ∧
          (∀ l : ℕ, l < k → CompletedGroup.projection l W.label = 1) ∧
          log (CompletedGroup.projection k W.label) = -c ∧
          CompletedGroup.projection k W.label ≠ 1 := by
  obtain ⟨r, hr, hlocal⟩ := D.exists_pos_joint_loop_obstruction hJ hq initial hfull hpure
  refine ⟨r, hr, fun x p hp n hn => ?_⟩
  dsimp only
  intro hc
  let c := (DirectSum.decompose (d.truncatedGrading ℒ k)
    (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k)
  have htrans : i (ρ n) ∉ (affineSpan ℝ J).direction :=
    fun ht => hc ((hlocal x p hp n hn).1 ht)
  obtain ⟨m, hm, hker, hmem⟩ := (hlocal x p hp n hn).2 htrans
  rw [H.truncated_wall] at hmem
  obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp hmem
  have hpiece : d.truncatedGrading ℒ k n ≠ ⊥ := by
    intro heq
    have hz : c ∈ d.truncatedGrading ℒ k n := (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n).property
    rw [heq, Submodule.mem_bot] at hz
    exact hc hz
  have hcut := d.mem_cutoff_of_truncatedGrading_ne_bot ℒ hpiece
  obtain ⟨w, hw⟩ := d.exists_supportedRay (d.mem_cutoff.mp hcut.1).1 hcut.2
  have hcell := ((D.adaptedComplex k).mem_cellsOfCodimension 2 J).mp hJ
  obtain ⟨W, hnormal, hray, hsupp, hlabel, hout, hborn⟩ :=
    DirectedWall.exists_outgoing_sweep ((D.adaptedComplex k).rational J hcell.1)
      ((D.adaptedComplex k).nonempty J hcell.1) hw htrans hm hker ((H.wall n m).neg_mem ha)
  have hlog : log (CompletedGroup.projection k W.label) = -c := by
    rw [hlabel, PositiveDegrees.projection_expToCompletion, log_exp, map_neg]
    exact congrArg Neg.neg he
  refine ⟨W, a, hout, hsupp, hray ▸ hw, hnormal ▸ hker, hnormal ▸ ha,
    hlabel, he, fun l hl => hborn l (by omega), hlog, ?_⟩
  intro hzero
  have hz : -c = 0 := hlog.symm.trans (hzero ▸ (log_one (L := d.truncatedLie ℒ k)))
  exact hc (neg_eq_zero.mp hz)

end Mei.DirectedDiagram
