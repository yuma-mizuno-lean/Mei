/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.Convex.Polyhedron.Path.Log

/-!
# Initial hyperplanes at abelian cutoffs

At any cutoff where the Lie quotient is abelian, the transport of full affine
hyperplanes is the exponential of an endpoint potential difference. In particular,
the order-one quotient of any positively graded Lie algebra is abelian, so a family
of incoming full hyperplanes is consistent through order one. The labels in the
completed group may be noncommutative: no higher-order consistency is asserted.

The endpoint formula combines `LieSubalgebra.log_wallPathProduct_sub_crossingSum_mem`
with `Quiver.Path.wallCrossingSum_eq_sum_side_sub`. It retains every indexed wall,
including coincident supports. Only the finite active family at the specified cutoff
must consist of full hyperplanes; there is no finiteness assumption on the whole
initial diagram, nor any condition on zero spatial directions.
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

/-- At an abelian cutoff, the logarithm of transport across full hyperplanes is
the signed sum of their endpoint-side differences. -/
theorem log_levelPathProduct_eq_sum_side_sub (k : ℕ)
    [IsLieAbelian (d.truncatedLie ℒ k)] (b : D.active k → ℝ)
    (hfull : ∀ j : D.active k,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b j})
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    let _ := Fintype.ofFinite (D.active k)
    log (D.levelPathProduct k p) = ∑ j : D.active k,
      ((if b j < h.realCharacter (D.wall j).normal x.val then 1 else 0 : ℤ) -
        (if b j < h.realCharacter (D.wall j).normal y.val then 1 else 0)) •
          log (CompletedGroup.projection k (D.wall j).label) := by
  let K : LieSubalgebra R (d.truncatedLie ℒ k) := ⊤
  have hlog := K.log_wallPathProduct_sub_crossingSum_mem (⊥ : Submodule R (d.truncatedLie ℒ k))
    (fun a _ z _ => by simp [trivial_lie_zero])
    (fun j : D.active k => h.realCharacter (D.wall j).normal)
    (fun j => CompletedGroup.projection k (D.wall j).label)
    (D.activeLabels_commute k) p (fun _ _ _ _ =>
      (K.mem_bchSubgroup _).mpr (by simp [K]))
  rw [Submodule.mem_bot, sub_eq_zero] at hlog
  calc
    _ = p.wallCrossingSum (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => log (CompletedGroup.projection k (D.wall j).label)) := by
      rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
      exact hlog
    _ = _ := p.wallCrossingSum_eq_sum_side_sub
      (fun j : D.active k => h.realCharacter (D.wall j).normal) b _ (fun j _ => hfull j)

/-- Full affine hyperplanes are consistent at every abelian Lie cutoff. The
completed labels need not commute at higher orders. -/
theorem levelConsistent_of_isLieAbelian_of_full (k : ℕ)
    [IsLieAbelian (d.truncatedLie ℒ k)]
    (hfull : ∀ j : D.active k, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}) :
    D.LevelConsistent k := by
  choose b hb using hfull
  apply (D.levelConsistent_def k).mpr
  intro x y p q
  apply log_injective
  rw [D.log_levelPathProduct_eq_sum_side_sub k b hb p,
    D.log_levelPathProduct_eq_sum_side_sub k b hb q]

/-- Initial full affine hyperplanes are consistent through order one for every
positive grading. No commutativity of their completed labels is required. -/
theorem levelConsistent_one_of_full
    (hfull : ∀ j : D.active 1, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}) :
    D.LevelConsistent 1 :=
  D.levelConsistent_of_isLieAbelian_of_full 1 hfull

end Mei.DirectedDiagram
