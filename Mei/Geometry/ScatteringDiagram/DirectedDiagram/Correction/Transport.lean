/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction
public import Mei.Geometry.Convex.Polyhedron.Path.Sum
import Mei.Geometry.Convex.Polyhedron.Path.CentralDifference
import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Transport after adding central correction walls

Retain a set of walls containing every wall active at order `k`. At order
`k + 1`, the omitted labels are central. The transport of the full diagram is
therefore the transport of the retained diagram multiplied by the exponential
of the signed crossing sum of the omitted logarithms. The logarithms themselves
add, even when the retained transport is noncentral. Consequently the corrected
diagram is consistent precisely when these crossing sums cancel the retained
loop logarithms.

This supplies the transport calculation for adjoining walls of a new birth
order. It does not assume that the retained diagram is already consistent at
that new order. Lower-order consistency is preserved by
`DirectedDiagram.levelConsistent_restrict_iff`. Repeated walls and simultaneous
crossings retain their indexed multiplicities.

The calculation specializes
`Quiver.Path.log_wallPathProduct_mul_inv_eq_wallCrossingSum` using
`DirectedDiagram.levelPathProduct_restrictPathPrefunctor` and the central
successive truncation kernel. It is the algebraic correction step in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6.
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
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  {k : ℕ} (s : Set ι) [DecidablePred (· ∈ s)] (hs : D.active k ⊆ s)

include hs

/-- The logarithmic change in transport upon adding walls invisible at the
previous order is exactly their signed crossing sum. Only walls outside the
retained index set contribute. -/
theorem log_levelPathProduct_mul_inv_restrict_eq_crossingSum
    {x y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    log (D.levelPathProduct (k + 1) p *
      ((D.restrict s).levelPathProduct (k + 1)
        ((D.restrictPathPrefunctor s (k + 1)).mapPath p))⁻¹) =
      p.wallCrossingSum (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal)
        (fun j => if j.val ∈ s then 0 else
          log (CompletedGroup.projection (k + 1) (D.wall j).label)) := by
  let a : D.active (k + 1) → BCHGroup (d.truncatedLie ℒ (k + 1)) := fun j =>
    (CompletedGroup.projection (k + 1) (D.wall j).label : d.truncatedGroup ℒ (k + 1))
  let b := fun j : D.active (k + 1) => if j.val ∈ s then a j else 1
  have hb : ∀ j j' : D.active (k + 1),
      affineSpan ℝ (D.wall j).support = affineSpan ℝ (D.wall j').support →
        Commute (b j) (b j') := by
    intro j j' he
    dsimp only [b]
    split_ifs <;> first
      | exact D.activeLabels_commute (k + 1) j j' he
      | exact Commute.one_right _
      | exact Commute.one_left _
  have hab (j : D.active (k + 1)) :
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (a j) =
        (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (b j) := by
    dsimp only [b]
    split_ifs with hj
    · rfl
    · have hz : CompletedGroup.projection k (D.wall j).label = 1 := by
        by_contra hne
        exact hj (hs ((D.mem_active k j.val).mpr hne))
      have he : (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (a j) =
          CompletedGroup.projection k (D.wall j).label :=
        CompletedGroup.map_projection k (k + 1) (Nat.le_succ k) (D.wall j).label
      rw [he, hz, map_one]
      -- The tower identity and the identity in its concrete BCH group coincide.
      rfl
  rw [D.levelPathProduct_restrictPathPrefunctor s (k + 1) hb p,
    D.levelPathProduct_eq_wallPathProduct (k + 1) p (D.activeLabels_commute (k + 1))]
  have he := p.log_wallPathProduct_mul_inv_eq_wallCrossingSum
    (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal) a b
    (D.activeLabels_commute (k + 1)) hb (d.truncationMap ℒ (Nat.le_succ k))
    (d.ker_truncationMap_succ_le_center ℒ k) (fun _ _ j _ => hab j.1)
  have hcoeff : (fun j => log (a j * (b j)⁻¹)) =
      fun j => if j.val ∈ s then 0 else log (a j) := by
    funext j
    dsimp only [b]
    split_ifs <;> simp
  rw [hcoeff] at he
  exact he

/-- At the correction order, adjoining new walls multiplies transport by the
exponential of their signed logarithmic crossing sum. The original labels may
be noncommutative. -/
theorem levelPathProduct_eq_exp_crossingSum_mul_restrict
    {x y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct (k + 1) p =
      exp (p.wallCrossingSum
        (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal)
        (fun j => if j.val ∈ s then 0 else
          log (CompletedGroup.projection (k + 1) (D.wall j).label))) *
      (D.restrict s).levelPathProduct (k + 1)
        ((D.restrictPathPrefunctor s (k + 1)).mapPath p) := by
  have he := congrArg exp (D.log_levelPathProduct_mul_inv_restrict_eq_crossingSum s hs p)
  rw [exp_log] at he
  exact (mul_inv_eq_iff_eq_mul).mp he

/-- Logarithms of the corrected and retained transports differ by the signed
sum of the new wall logarithms. No consistency assumption on either diagram
is needed. -/
theorem log_levelPathProduct_eq_crossingSum_add_restrict
    {x y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    log (D.levelPathProduct (k + 1) p) =
      p.wallCrossingSum (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal)
        (fun j => if j.val ∈ s then 0 else
          log (CompletedGroup.projection (k + 1) (D.wall j).label)) +
      log ((D.restrict s).levelPathProduct (k + 1)
        ((D.restrictPathPrefunctor s (k + 1)).mapPath p)) := by
  let f := d.truncationMap ℒ (Nat.le_succ k)
  let A := D.levelPathProduct (k + 1) p
  let B := (D.restrict s).levelPathProduct (k + 1)
    ((D.restrictPathPrefunctor s (k + 1)).mapPath p)
  have hcoeff (j : D.active (k + 1)) :
      (if j.val ∈ s then 0 else log (CompletedGroup.projection (k + 1) (D.wall j).label)) ∈
        f.ker := by
    split_ifs with hj
    · exact f.ker.zero_mem
    · rw [LieHom.mem_ker]
      have hz : CompletedGroup.projection k (D.wall j).label = 1 := by
        by_contra hne
        exact hj (hs ((D.mem_active k j.val).mpr hne))
      have he : f.bchGroupMap (CompletedGroup.projection (k + 1) (D.wall j).label) =
          CompletedGroup.projection k (D.wall j).label :=
        CompletedGroup.map_projection k (k + 1) (Nat.le_succ k) (D.wall j).label
      have he' : f (log (CompletedGroup.projection (k + 1) (D.wall j).label)) =
          log (CompletedGroup.projection k (D.wall j).label) :=
        (f.log_bchGroupMap _).symm.trans (congrArg log he)
      rw [hz] at he'
      exact he'.trans (log_one (L := d.truncatedLie ℒ k))
  have hmem : log (A * B⁻¹) ∈ f.ker := by
    rw [D.log_levelPathProduct_mul_inv_restrict_eq_crossingSum s hs p,
      Quiver.Path.wallCrossingSum_def]
    apply f.ker.toSubmodule.toAddSubgroup.list_sum_mem
    intro c hc
    obtain ⟨S, _, rfl⟩ := List.mem_map.mp hc
    exact f.ker.sum_mem fun j _ =>
      f.ker.toSubmodule.toAddSubgroup.zsmul_mem (hcoeff j.1) j.2
  have hlie : ⁅log (A * B⁻¹), log B⁆ = 0 := by
    rw [← lie_skew, (d.ker_truncationMap_succ_le_center ℒ k hmem) (log B), neg_zero]
  have he : log A = log (A * B⁻¹) + log B := by
    rw [← bch_eq_add_of_lie_eq_zero _ _ hlie, ← log_mul, inv_mul_cancel_right]
  rw [D.log_levelPathProduct_mul_inv_restrict_eq_crossingSum s hs p] at he
  exact he

/-- Consistency after adding a new birth family is equivalent to cancellation
of the old loop logarithms by the new walls' signed crossing sums. This tests
actual loops of the combined active family, including the new supports. -/
theorem levelConsistent_succ_iff_crossingSum_eq_neg_restrict :
    D.LevelConsistent (k + 1) ↔
      ∀ (x : WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
        (p : AdmissiblePLPath x x),
        p.wallCrossingSum (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal)
          (fun j => if j.val ∈ s then 0 else
            log (CompletedGroup.projection (k + 1) (D.wall j).label)) =
          -log ((D.restrict s).levelPathProduct (k + 1)
            ((D.restrictPathPrefunctor s (k + 1)).mapPath p)) := by
  rw [D.levelConsistent_iff_loops]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro p
  rw [← log_injective.eq_iff, log_one,
    D.log_levelPathProduct_eq_crossingSum_add_restrict s hs p, add_eq_zero_iff_eq_neg]

end Mei.DirectedDiagram
