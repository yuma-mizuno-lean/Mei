/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append

/-!
# Replacing equivalent initial wall presentations

Adjoining the same disjoint indexed walls to equivalent subdiagrams preserves
finite-order equivalence. Each crossing event can be isolated, so replacement
holds even though factors from different events need not commute.

Consequently consistent outgoing extensions of equivalent initial inputs have
the same finite-order transport. Only consistency and input equivalence at the
specified cutoff are needed; no condition is imposed on later cutoffs.

The replacement uses `DirectedDiagram.LevelEquivalent.restrict_union`.
The comparison of outgoing extensions uses the first-differing-order uniqueness
argument `DirectedDiagram.levelEquivalent_restrict_of_outgoing`, following
Travis Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Theorem 2.6, arXiv:1503.06183v5.
-/

public section

noncomputable section

open Set Mei.Convex
open scoped symmDiff

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

section Completion

variable {ι₀ κ₀ ι' κ' : Type*}

/-- Consistent outgoing extensions of equivalent initial diagrams agree at the
same cutoff, even when the initial index types and wall supports differ.
Only active added walls need to be outgoing. -/
theorem outgoingCompletion_levelEquivalent_of_input
    (D₀ : DirectedDiagram (d := d) h H ι₀) (E₀ : DirectedDiagram (d := d) h H κ₀)
    {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    {E : DirectedDiagram (d := d) h H (κ₀ ⊕ κ')} {k : ℕ}
    (hinput : D₀.LevelEquivalent E₀ k)
    (hD₀ : ∀ j, D.wall (.inl j) = D₀.wall j)
    (hE₀ : ∀ j, E.wall (.inl j) = E₀.wall j)
    (hD : D.LevelConsistent k) (hE : E.LevelConsistent k)
    (houtD : ∀ j, Sum.inr j ∈ D.active k → (D.wall (.inr j)).Outgoing)
    (houtE : ∀ j, Sum.inr j ∈ E.active k → (E.wall (.inr j)).Outgoing) :
    D.LevelEquivalent E k := by
  classical
  let F := D.append E
  let s : Set ((ι₀ ⊕ ι') ⊕ (κ₀ ⊕ κ')) := range (fun j : ι₀ => Sum.inl (Sum.inl j))
  let t : Set ((ι₀ ⊕ ι') ⊕ (κ₀ ⊕ κ')) := range (fun j : κ₀ => Sum.inr (Sum.inl j))
  let u : Set ((ι₀ ⊕ ι') ⊕ (κ₀ ⊕ κ')) := range (fun j : ι' => Sum.inl (Sum.inr j))
  let v : Set ((ι₀ ⊕ ι') ⊕ (κ₀ ⊕ κ')) := range (fun j : κ' => Sum.inr (Sum.inr j))
  -- Reindex the two initial restrictions using the existing refinement API.
  have hs : (F.restrict s).LevelEquivalent D₀ k :=
    (Refinement.ofEquiv
      (Equiv.ofInjective (fun j : ι₀ => Sum.inl (Sum.inl j))
        (Sum.inl_injective.comp Sum.inl_injective)) (fun j => by
          rw [restrict_wall, Equiv.ofInjective_apply]
          simpa only [F, append_wall_inl] using (hD₀ j).symm)).levelEquivalent k
  have ht : (F.restrict t).LevelEquivalent E₀ k :=
    (Refinement.ofEquiv
      (Equiv.ofInjective (fun j : κ₀ => Sum.inr (Sum.inl j))
        (Sum.inr_injective.comp Sum.inl_injective)) (fun j => by
          rw [restrict_wall, Equiv.ofInjective_apply]
          simpa only [F, append_wall_inr] using (hE₀ j).symm)).levelEquivalent k
  have hsu : s ∪ u = range (Sum.inl : (ι₀ ⊕ ι') → (ι₀ ⊕ ι') ⊕ (κ₀ ⊕ κ')) := by
    ext j
    rcases j with ((j | j) | (j | j)) <;> simp [s, u]
  have htv : t ∪ v = range (Sum.inr : (κ₀ ⊕ κ') → (ι₀ ⊕ ι') ⊕ (κ₀ ⊕ κ')) := by
    ext j
    rcases j with ((j | j) | (j | j)) <;> simp [t, v]
  have hleft : (F.restrict (s ∪ u)).LevelEquivalent D k := by
    rw [hsu]
    exact (equivalent_iff _ _).mp (D.restrict_append_left_equivalent E) k
  have hright : (F.restrict (t ∪ v)).LevelEquivalent E k := by
    rw [htv]
    exact (Refinement.ofEquiv (Equiv.ofInjective _ Sum.inr_injective) (fun j => by
      simp only [restrict_wall, Equiv.ofInjective_apply, F, append_wall_inr])).levelEquivalent k
  have hreplace : (F.restrict (s ∪ u)).LevelEquivalent (F.restrict (t ∪ u)) k :=
    (hs.trans (hinput.trans ht.symm)).restrict_union
      (by simp [s, u, Set.disjoint_left]) (by simp [t, u, Set.disjoint_left])
  have hout : ∀ j ∈ F.active k, j ∈ (t ∪ u) ∆ (t ∪ v) → (F.wall j).Outgoing := by
    rintro ((j | j) | (j | j)) hj hmem
    · simp [t, u, v, Set.mem_symmDiff] at hmem
    · simpa only [F, append_wall_inl] using houtD j (by
        simpa only [F, mem_active, append_wall_inl] using hj)
    · simp [t, u, v, Set.mem_symmDiff] at hmem
    · simpa only [F, append_wall_inr] using houtE j (by
        simpa only [F, mem_active, append_wall_inr] using hj)
  exact hleft.symm.trans (hreplace.trans
    ((F.levelEquivalent_restrict_of_outgoing
      (hreplace.consistent (hleft.symm.consistent hD))
      (hright.symm.consistent hE) hout).trans hright))

/-- Outgoing completion depends only on the equivalence class of the initial
diagram. The two input presentations need not share indices or supports. -/
theorem IsOutgoingCompletion.equivalent_of_input
    {D₀ : DirectedDiagram (d := d) h H ι₀} {E₀ : DirectedDiagram (d := d) h H κ₀}
    {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    {E : DirectedDiagram (d := d) h H (κ₀ ⊕ κ')}
    (hD : IsOutgoingCompletion D₀.wall D) (hE : IsOutgoingCompletion E₀.wall E)
    (hinput : D₀.Equivalent E₀) : D.Equivalent E := by
  exact (equivalent_iff D E).mpr fun k => outgoingCompletion_levelEquivalent_of_input D₀ E₀
    ((equivalent_iff D₀ E₀).mp hinput k) hD.wall_inl hE.wall_inl
    ((consistent_iff D).mp hD.consistent k) ((consistent_iff E).mp hE.consistent k)
    (fun j _ => hD.outgoing_inr j) (fun j _ => hE.outgoing_inr j)

end Completion

end Mei.DirectedDiagram
