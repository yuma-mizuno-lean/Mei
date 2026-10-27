/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Transport
public import Mei.Geometry.Convex.PolyhedralCochain.Crossing

/-!
# Replacing central correction cochains

At the next order, walls invisible at the preceding cutoff are central. Their
contribution to transport depends only on their logarithmic polyhedral cochain.
Consequently equal correction cochains can be substituted into equivalent retained
diagrams without changing any common path product. This permits subdivision,
orientation reversal and cancellation of the correction presentation, including
refinements introducing new intersections. The retained wall labels may be
noncommutative, and neither diagram needs to be consistent at the new order.

The comparison combines
`DirectedDiagram.log_levelPathProduct_eq_crossingSum_add_restrict` with
`Quiver.Path.wallCrossingSum_eq_of_cochain_eq`. The latter uses invariance of
intersection pairings under the actual cochain relations, rather than assuming
a matching of individual walls. This is the presentation comparison for central
corrections in Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, proof of Theorem 2.6.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι) (E : DirectedDiagram (d := d) h H κ)
  {k : ℕ} (s : Set ι) (t : Set κ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
  (hs : D.active k ⊆ s) (ht : E.active k ⊆ t)
  (σ : D.active (k + 1) → OrientedCell h 1)
  (τ : E.active (k + 1) → OrientedCell h 1)
  (hσ : ∀ j, (σ j).carrier = (D.wall j).support)
  (hτ : ∀ j, (τ j).carrier = (E.wall j).support)
  (hν : ∀ j : D.active (k + 1), j.val ∉ s → ∀ v : V,
    SignType.sign (h.realCharacter (D.wall j).normal v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
  (hμ : ∀ j : E.active (k + 1), j.val ∉ t → ∀ v : V,
    SignType.sign (h.realCharacter (E.wall j).normal v) =
      (τ j).orientation.evalSign (fun _ : Fin 1 => v))

include hs ht hσ hτ hν hμ in
/-- Replacing the walls of a new birth order by an equal logarithmic cochain
preserves finite-order equivalence, provided the retained diagrams are equivalent.
Only the newly added walls need their normals to induce the displayed cell
orientations. Equality is in polyhedral cochains, so it allows subdivisions and
cancellation, not only a bijection of the correction indices. -/
theorem levelEquivalent_of_correction_cochain_eq
    (hretained : (D.restrict s).LevelEquivalent (E.restrict t) (k + 1))
    (hc :
      let _ := Fintype.ofFinite (D.active (k + 1))
      let _ := Fintype.ofFinite (E.active (k + 1))
      (∑ j : D.active (k + 1), PolyhedralCochain.mk (R := R) (σ j)
        (if j.val ∈ s then 0 else log (CompletedGroup.projection (k + 1) (D.wall j).label) :
          d.truncatedLie ℒ (k + 1))) =
      ∑ j : E.active (k + 1), PolyhedralCochain.mk (τ j)
        (if j.val ∈ t then 0 else log (CompletedGroup.projection (k + 1) (E.wall j).label) :
          d.truncatedLie ℒ (k + 1))) :
    D.LevelEquivalent E (k + 1) := by
  classical
  let := Fintype.ofFinite (D.active (k + 1))
  let := Fintype.ofFinite (E.active (k + 1))
  apply (D.levelEquivalent_def E (k + 1)).mpr
  intro x y x' y' p q hpq
  have hsum := p.wallCrossingSum_eq_of_cochain_eq (R := R) q
    (fun j : D.active (k + 1) => h.realCharacter (D.wall j).normal)
    (fun j : E.active (k + 1) => h.realCharacter (E.wall j).normal)
    (fun j => if j.val ∈ s then 0 else log (CompletedGroup.projection (k + 1) (D.wall j).label))
    (fun j => if j.val ∈ t then 0 else log (CompletedGroup.projection (k + 1) (E.wall j).label))
    (fun j hj => hν j (by intro hjs; simp only [hjs, ite_true, ne_self_iff_false] at hj))
    (fun j hj => hμ j (by intro hjt; simp only [hjt, ite_true, ne_self_iff_false] at hj))
    hc hσ hτ hpq
  have hprod := ((D.restrict s).levelEquivalent_def (E.restrict t) (k + 1)).mp hretained
    ((D.restrictPathPrefunctor s (k + 1)).mapPath p)
    ((E.restrictPathPrefunctor t (k + 1)).mapPath q)
    ((D.vertices_restrictPathPrefunctor s (k + 1) p).trans
      (hpq.trans (E.vertices_restrictPathPrefunctor t (k + 1) q).symm))
  apply log_injective
  rw [D.log_levelPathProduct_eq_crossingSum_add_restrict s hs p,
    E.log_levelPathProduct_eq_crossingSum_add_restrict t ht q, hsum, hprod]

end Mei.DirectedDiagram
