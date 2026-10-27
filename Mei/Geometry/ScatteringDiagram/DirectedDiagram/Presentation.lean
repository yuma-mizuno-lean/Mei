/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness

/-!
# Outgoing completions of equivalent inputs

The finite-order class of an outgoing completion depends only on the finite-order
class of its initial diagram. Initial presentations may have unrelated index types,
coincident walls, cancelling labels and different completed labels above the chosen
cutoff. Only consistency and outgoingness of active additional walls at that cutoff
are needed. In particular, outgoing completions of equivalent initial diagrams are
equivalent at every order.

The central formal inputs are `DirectedDiagram.LevelEquivalent.append` and
`DirectedDiagram.outgoingCompletion_levelEquivalent`. The comparison extends
the uniqueness theorem of Travis Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Theorem 2.6,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), to equivalent initial
presentations. No full-hyperplane or pure-birth assumption is used in this comparison.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι₀ κ₀ ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  {D₀ : DirectedDiagram (d := d) h H ι₀} {E₀ : DirectedDiagram (d := d) h H κ₀}
  {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι)}
  {E : DirectedDiagram (d := d) h H (κ₀ ⊕ κ)}

/-- Completions consistent at order `k` of order-`k` equivalent initial diagrams
agree at order `k`. Only active additional walls must be outgoing; no agreement
of indices or of individual initial walls is assumed. -/
theorem outgoingCompletion_levelEquivalent_of_initial_levelEquivalent {k : ℕ}
    (h₀ : D₀.LevelEquivalent E₀ k)
    (hinitialD : ∀ j, D.wall (.inl j) = D₀.wall j)
    (hinitialE : ∀ j, E.wall (.inl j) = E₀.wall j)
    (hD : D.LevelConsistent k) (hE : E.LevelConsistent k)
    (houtD : ∀ j, Sum.inr j ∈ D.active k → (D.wall (.inr j)).Outgoing)
    (houtE : ∀ j, Sum.inr j ∈ E.active k → (E.wall (.inr j)).Outgoing) :
    D.LevelEquivalent E k := by
  let C : DirectedDiagram (d := d) h H ι :=
    { wall := fun j => D.wall (.inr j)
      finite_active l := (D.finite_active l).preimage Sum.inr_injective.injOn }
  have hDC : D₀.append C = D := by
    apply DirectedDiagram.ext
    funext j
    cases j with
    | inl j => simpa only [append_wall_inl] using (hinitialD j).symm
    | inr j => exact append_wall_inr D₀ C j
  have hDF : D.LevelEquivalent (E₀.append C) k := by
    simpa only [hDC] using h₀.append C
  refine hDF.trans (outgoingCompletion_levelEquivalent
    (fun j => by simpa only [append_wall_inl] using (hinitialE j).symm)
    (hDF.consistent hD) hE ?_ houtE)
  intro j hj
  rw [append_wall_inr]
  exact houtD j (by simpa only [mem_active, append_wall_inr] using hj)

/-- Outgoing completions of equivalent initial diagrams are equivalent, even
when their initial indexed wall presentations differ. -/
theorem IsOutgoingCompletion.equivalent_of_initial_equivalent
    (hD : IsOutgoingCompletion D₀.wall D) (hE : IsOutgoingCompletion E₀.wall E)
    (h₀ : D₀.Equivalent E₀) : D.Equivalent E := by
  exact (equivalent_iff _ _).mpr fun k =>
    outgoingCompletion_levelEquivalent_of_initial_levelEquivalent
      ((equivalent_iff _ _).mp h₀ k) hD.wall_inl hE.wall_inl
      ((consistent_iff _).mp hD.consistent k) ((consistent_iff _).mp hE.consistent k)
      (fun j _ => hD.outgoing_inr j) (fun j _ => hE.outgoing_inr j)

end Mei.DirectedDiagram
