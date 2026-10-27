/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Algebra.Lie.Graded.Truncation.Transition
import Mei.Geometry.ScatteringDiagram.DirectedWall.Escape
import Mei.Geometry.Convex.Polyhedron.Path.Log

/-!
# Vanishing of abelian outgoing directed transport

A consistent finite-order directed diagram whose active labels lie in an abelian
Lie subalgebra and whose active walls are outgoing has trivial path products.
Different walls may have different geometric directions. Homogeneous projection
reduces each degree to walls on its supported ray, which escape along that degree's
positive geometric direction. The signed crossing sum then vanishes by
`DirectedWall.wallCrossingSum_eq_zero_of_outgoing`.

In particular, the conclusion applies when every active label becomes the identity
at the preceding cutoff: the successive truncation kernel is abelian. This is the
abelian vanishing step in the first-differing-order argument for uniqueness of
outgoing completions. It does not assert that individual indexed labels vanish:
coincident walls can cancel.

The argument uses `LieSubalgebra.log_wallPathProduct_sub_crossingSum_mem`,
the homogeneous support of completed wall groups, and the escape argument above.
It follows the uniqueness argument in Travis Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, proof of Theorem 2.6.
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

/-- Consistent outgoing transport with logarithms in an abelian Lie subalgebra
vanishes. The walls may have different degrees and geometric directions. -/
theorem levelPathProduct_eq_one_of_outgoing {k : ℕ} (hD : D.LevelConsistent k)
    (K : LieSubalgebra R (d.truncatedLie ℒ k)) [IsLieAbelian K]
    (hlabel : ∀ j : D.active k, log (CompletedGroup.projection k (D.wall j).label) ∈ K)
    (hout : ∀ j : D.active k, (D.wall j).Outgoing)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) : D.levelPathProduct k p = 1 := by
  classical
  let ν := fun j : D.active k => h.realCharacter (D.wall j).normal
  let a := fun j : D.active k => log (CompletedGroup.projection k (D.wall j).label)
  have hlinear {u v : WallComplement (fun j : D.active k => (D.wall j).support)}
      (q : AdmissiblePLPath u v) :
      log (D.levelPathProduct k q) = q.wallCrossingSum ν a := by
    have he := K.log_wallPathProduct_sub_crossingSum_mem
      (⊥ : Submodule R (d.truncatedLie ℒ k)) (fun b hb c hc => by
        have hz := congrArg (fun z : K => (z : d.truncatedLie ℒ k))
          (trivial_lie_zero K K ⟨b, hb⟩ ⟨c, hc⟩)
        exact (Submodule.mem_bot R).mpr hz)
      ν (fun j => CompletedGroup.projection k (D.wall j).label)
      (D.activeLabels_commute k) q
      (fun _ _ j _ => (K.mem_bchSubgroup _).mpr (hlabel j.1))
    rw [D.levelPathProduct_eq_wallPathProduct k q (D.activeLabels_commute k)]
    exact sub_eq_zero.mp ((Submodule.mem_bot R).mp he)
  have hsum : p.wallCrossingSum ν a = 0 := by
    rw [← DirectSum.sum_support_decompose (d.truncatedGrading ℒ k)
      (p.wallCrossingSum ν a)]
    apply Finset.sum_eq_zero
    intro n _
    let f := ((d.truncatedGrading ℒ k n).subtype.comp
      ((DirectSum.component R Γ (fun m => d.truncatedGrading ℒ k m) n).comp
        (DirectSum.decomposeLinearEquiv (d.truncatedGrading ℒ k)).toLinearMap)).toAddMonoidHom
    -- A nonzero coefficient forces this degree to lie on the wall's actual ray.
    have hdegree (j : D.active k) (hj : f (a j) ≠ 0) : n ∈ (D.wall j).ray.rayDegrees := by
      by_contra hn
      exact hj (H.decompose_log_projection_eq_zero_of_notMem_rayDegrees
        (D.wall j).label_mem k hn)
    have hloop (q : AdmissiblePLPath x x) : q.wallCrossingSum ν (fun j => f (a j)) = 0 := by
      rw [← f.map_wallCrossingSum q ν a, ← hlinear q,
        (D.levelConsistent_iff_loops k).mp hD x q, log_one, map_zero]
    have he := DirectedWall.wallCrossingSum_eq_zero_of_outgoing
      (fun j : D.active k => D.wall j) (fun j => f (a j))
      (fun j hj => ⟨hout j, hdegree j hj⟩) hloop p
    rw [← f.map_wallCrossingSum p ν a] at he
    exact he
  apply log_injective
  rw [hlinear p, hsum, log_one]

/-- At the first nontrivial cutoff, a consistent outgoing diagram has trivial
transport: its labels lie in the abelian kernel of the preceding truncation. -/
theorem levelPathProduct_eq_one_of_outgoing_of_projection_eq_one {k : ℕ}
    (hD : D.LevelConsistent (k + 1))
    (hlabel : ∀ j : D.active (k + 1), CompletedGroup.projection k (D.wall j).label = 1)
    (hout : ∀ j : D.active (k + 1), (D.wall j).Outgoing)
    {x y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (p : AdmissiblePLPath x y) : D.levelPathProduct (k + 1) p = 1 := by
  let : IsLieAbelian (d.truncationMap ℒ (Nat.le_succ k)).ker.toLieSubalgebra :=
    inferInstanceAs (IsLieAbelian (d.truncationMap ℒ (Nat.le_succ k)).ker)
  apply D.levelPathProduct_eq_one_of_outgoing hD
    (d.truncationMap ℒ (Nat.le_succ k)).ker.toLieSubalgebra ?_ hout p
  intro j
  rw [LieIdeal.mem_toLieSubalgebra, LieHom.mem_ker]
  have he : (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
      (CompletedGroup.projection (k + 1) (D.wall j).label) =
        CompletedGroup.projection k (D.wall j).label :=
    CompletedGroup.map_projection k (k + 1) (Nat.le_succ k) (D.wall j).label
  have he' := congrArg (log (L := d.truncatedLie ℒ k)) (he.trans (hlabel j))
  exact ((d.truncationMap ℒ (Nat.le_succ k)).log_bchGroupMap _).symm.trans
    (he'.trans log_one)

end Mei.DirectedDiagram
