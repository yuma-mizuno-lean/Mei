/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Invariance
public import Mei.Geometry.Convex.Polyhedron.Path.Refinement

/-!
# Restricting indexed directed diagrams

Restrict a directed diagram to a set of wall indices. At any cutoff where the set
retains every active wall, restriction preserves all common path products and hence
consistency. Walls invisible at that cutoff impose no additional path conditions.

The comparison uses `Quiver.Path.wallPathProduct_eq_of_refines` on the active
families, whose indices are in bijection. Consistency then follows from
`DirectedDiagram.LevelEquivalent.consistent_iff`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Retain the indexed walls in `s`, with their original supports and labels. -/
def restrict (s : Set ι) : DirectedDiagram (d := d) h H s where
  wall j := D.wall j.val
  finite_active k := (D.finite_active k).preimage Subtype.val_injective.injOn

@[simp]
theorem restrict_wall (s : Set ι) (j : s) : (D.restrict s).wall j = D.wall j.val := (rfl)

/-- Deleting only walls invisible at order `k` preserves order-`k` equivalence.
No condition is imposed on the deleted walls at higher orders. -/
theorem levelEquivalent_restrict {k : ℕ} {s : Set ι} (hs : D.active k ⊆ s) :
    D.LevelEquivalent (D.restrict s) k := by
  let E := D.restrict s
  let f : E.active k → D.active k := fun j =>
    ⟨j.val.val, by simpa only [mem_active, E, restrict_wall] using j.property⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : D.active k => z.val) hab))
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨⟨⟨a.val, hs a.property⟩, ?_⟩, Subtype.ext rfl⟩
    simpa only [mem_active, E, restrict_wall] using a.property
  apply (D.levelEquivalent_def E k).mpr
  intro x y x' y' p q hpq
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k),
    E.levelPathProduct_eq_wallPathProduct k q (E.activeLabels_commute k)]
  symm
  refine Quiver.Path.wallPathProduct_eq_of_refines
    (fun j : D.active k => h.realCharacter (D.wall j).normal) _ (D.activeLabels_commute k)
    (fun j : E.active k => h.realCharacter (E.wall j).normal) _
    (E.activeLabels_commute k) (f := f) (fun _ => subset_rfl)
    (fun a => ?_) (fun a => ?_) (fun _ => rfl) (fun _ => rfl) p q hpq.symm
  · obtain ⟨j, rfl⟩ := hsurj a
    exact fun z hz => mem_iUnion₂.mpr ⟨j, rfl, hz⟩
  · intro a₁ ha₁ a₂ ha₂ hne
    exact (hne (hf (ha₁.trans ha₂.symm))).elim

/-- At a cutoff retaining all active walls, a restriction is consistent exactly
when the original diagram is. -/
theorem levelConsistent_restrict_iff {k : ℕ} {s : Set ι} (hs : D.active k ⊆ s) :
    (D.restrict s).LevelConsistent k ↔ D.LevelConsistent k :=
  (D.levelEquivalent_restrict hs).consistent_iff.symm

end Mei.DirectedDiagram
