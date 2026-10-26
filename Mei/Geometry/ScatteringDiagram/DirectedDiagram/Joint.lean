/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Joint
public import Mei.Geometry.Convex.Polyhedron.Path.Logarithm

/-!
# Tangent-degree vanishing for directed loop products

Consider a closed admissible path whose crossed normals annihilate a submonoid
`W` of tangent lattice vectors. The nonlinear part of its logarithmic transport
has no homogeneous component in a degree whose geometric direction lies in `W`.
If every wall with a nonzero component in that degree is a full affine hyperplane,
its linear part cancels as well. Thus that component of the actual loop product
vanishes, without assuming that different wall labels commute.

In particular this applies at a correction order when initial walls are full
hyperplanes and all other active wall logarithms are homogeneous of lower order.
Zero spatial directions are included, since every submonoid contains zero.
Only the normals of walls actually crossed by the loop must annihilate `W`;
remote walls impose no condition.

The proof combines `DirectedWallSpaces.lie_mem_transverseJointSubmodule` and
`projection_mem_bchSubgroup_jointSubalgebra` with the signed crossing sum's
full-hyperplane cancellation. This is the tangent-component argument in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix C.3.
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
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  {k : ℕ} {W : AddSubmonoid Λ}
  {x y : WallComplement (fun j : D.active k => (D.wall j).support)}

/-- The nonlinear logarithmic contribution of a directed path is transverse to
any lattice submonoid annihilated by every crossed wall normal. -/
theorem log_levelPathProduct_sub_wallCrossingSum_mem (p : AdmissiblePLPath x y)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0) :
    log (D.levelPathProduct k p) -
      p.wallCrossingSum (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => log (CompletedGroup.projection k (D.wall j).label)) ∈
      (H.truncated d k).transverseJointSubmodule W := by
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
  exact p.log_wallPathProduct_sub_wallCrossingSum_mem _ _ _
    ((H.truncated d k).jointSubalgebra W) _
    (fun _ hu _ hv => (H.truncated d k).lie_mem_transverseJointSubmodule hu hv)
    (fun S hS a ha => H.projection_mem_bchSubgroup_jointSubalgebra
      (D.wall a.1).label_mem (hnormal S hS a ha) k)

/-- In a tangent degree, the logarithm of a directed loop product vanishes when
every wall with a surviving linear component is a full affine hyperplane.
This includes every zero spatial degree. -/
theorem decompose_log_levelPathProduct_loop_eq_zero (p : AdmissiblePLPath x x)
    (n : Γ) (hn : ρ n ∈ W)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0)
    (b : D.active k → ℝ)
    (hfull : ∀ j : D.active k,
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (log (CompletedGroup.projection k (D.wall j).label)) n : d.truncatedLie ℒ k) ≠ 0 →
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b j}) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) = 0 := by
  have htrans := (H.truncated d k).decompose_eq_zero_of_mem_transverseJointSubmodule
    (D.log_levelPathProduct_sub_wallCrossingSum_mem p hnormal) hn
  rw [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub, sub_eq_zero] at htrans
  rw [htrans]
  let f : d.truncatedLie ℒ k →+ d.truncatedGrading ℒ k n :=
    (DFinsupp.evalAddMonoidHom n).comp
      (DirectSum.decomposeAddEquiv (d.truncatedGrading ℒ k)).toAddMonoidHom
  have hf (u : d.truncatedLie ℒ k) :
      f u = DirectSum.decompose (d.truncatedGrading ℒ k) u n := (rfl)
  have hzero := p.wallCrossingSum_loop_eq_zero
    (fun j : D.active k => h.realCharacter (D.wall j).normal) b
    (fun j => f (log (CompletedGroup.projection k (D.wall j).label)))
    (fun j hj => hfull j (fun he => hj (by
      apply Subtype.ext
      simpa only [hf, ZeroMemClass.coe_zero] using he)))
  rw [← AddMonoidHom.map_wallCrossingSum] at hzero
  simpa only [hf, ZeroMemClass.coe_zero] using congrArg Subtype.val hzero

/-- Full initial hyperplanes and homogeneous wall logarithms born below order
`k` have no tangent-degree loop obstruction at order `k`. The birth logarithms
are required to be homogeneous in the actual truncated grading. -/
theorem decompose_log_levelPathProduct_loop_eq_zero_of_lower_birth
    (p : AdmissiblePLPath x x) (n : Γ) (hn : ρ n ∈ W) (hdegree : d.degree n = k)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0)
    (hbirth : ∀ j : D.active k,
      (∃ b : ℝ, (D.wall j).support =
        {v | h.realCharacter (D.wall j).normal v = b}) ∨
      ∃ m : Γ, d.degree m < k ∧
        log (CompletedGroup.projection k (D.wall j).label) ∈ d.truncatedGrading ℒ k m) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) = 0 := by
  classical
  have hex (j : D.active k) : ∃ b : ℝ,
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (log (CompletedGroup.projection k (D.wall j).label)) n : d.truncatedLie ℒ k) ≠ 0 →
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b} := by
    rcases hbirth j with ⟨b, hb⟩ | ⟨m, hm, hlog⟩
    · exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun hj => (hj (DirectSum.decompose_of_mem_ne
        (d.truncatedGrading ℒ k) hlog (by rintro rfl; omega))).elim⟩
  choose b hb using hex
  exact D.decompose_log_levelPathProduct_loop_eq_zero p n hn hnormal b hb

end Mei.DirectedDiagram
