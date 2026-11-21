/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane

/-!
# Unions of finitely many commuting wall families

For a finite type `β` and directed diagrams `D b`, `b : β`, with the same positive degrees, wall
spaces and spatial lattice, `DirectedDiagram.sigma D` is their union, indexed by the dependent
pairs `(b, j)`; repeated walls keep their indices. For a diagram indexed by dependent pairs
`(j, w)` and a set `s`, `DirectedDiagram.restrictSigma` keeps the walls with `j ∈ s`, indexed by
the pairs over `s`.

* Restricting a diagram to the range of an injective reindexing gives a diagram equivalent to the
  reindexed one (`DirectedDiagram.restrict_range_equivalent`).
* **Commuting partitions.** Let `f : ι → β` map the walls of `D` to a finite type of parts. If the
  restriction of `D` to every fibre of `f` is consistent and the labels of walls in distinct
  parts commute, then `D` is consistent (`DirectedDiagram.consistent_of_restrict_preimage`). For
  two parts this is `DirectedDiagram.consistent_of_restrict_of_restrict_compl`, from which the
  general case follows by induction on the parts.
* **Commuting unions.** If every `D b` is consistent and the labels of `D b` and `D b'` commute
  for `b ≠ b'`, then the union `DirectedDiagram.sigma D` is consistent
  (`DirectedDiagram.Consistent.sigma`). The walls of distinct families may cross, overlap or
  coincide. This generalizes `DirectedDiagram.Consistent.append` from two families to finitely
  many.
-/

public section

noncomputable section

open Set

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ β : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

section Sigma

variable {ι : β → Type*}

/-- The union of finitely many indexed wall families, indexed by the pairs `(b, j)` of a family
`b` and an index `j` of its walls. -/
def sigma [Finite β] (D : ∀ b, DirectedDiagram (d := d) h H (ι b)) :
    DirectedDiagram (d := d) h H (Σ b, ι b) where
  wall x := (D x.1).wall x.2
  finite_active k :=
    (Set.finite_univ.sigma fun b _ => (D b).finite_active k).subset fun _ hx => ⟨mem_univ _, hx⟩

@[simp]
theorem sigma_wall [Finite β] (D : ∀ b, DirectedDiagram (d := d) h H (ι b)) (b : β) (j : ι b) :
    (sigma D).wall ⟨b, j⟩ = (D b).wall j := (rfl)

end Sigma

section Restrict

variable {κ : ι → Type*}

/-- The walls of a diagram indexed by dependent pairs `(j, w)` whose first component `j` lies in
the set `s`. -/
def restrictSigma (D : DirectedDiagram (d := d) h H (Σ j, κ j)) (s : Set ι) :
    DirectedDiagram (d := d) h H (Σ j : s, κ j) where
  wall x := D.wall ⟨x.1, x.2⟩
  finite_active k := (D.finite_active k).preimage
    ((Subtype.val_injective.sigma_map fun _ => Function.injective_id).injOn)

@[simp]
theorem restrictSigma_wall (D : DirectedDiagram (d := d) h H (Σ j, κ j)) (s : Set ι) (j : s)
    (w : κ j) : (D.restrictSigma s).wall ⟨j, w⟩ = D.wall ⟨j, w⟩ := (rfl)

end Restrict

variable (D : DirectedDiagram (d := d) h H ι)

/-- Restricting a diagram to the range of an injective map `e : κ → ι` gives a diagram equivalent
to any diagram whose wall `j` is the wall `e j`. -/
theorem restrict_range_equivalent {E : DirectedDiagram (d := d) h H κ} {e : κ → ι}
    (he : Function.Injective e) (hE : ∀ j, E.wall j = D.wall (e j)) :
    (D.restrict (range e)).Equivalent E :=
  (Refinement.ofEquiv (Equiv.ofInjective e he) fun j => by
    rw [restrict_wall, Equiv.ofInjective_apply, hE]).equivalent

variable {D}

/-- The restriction of `D` to the indices whose part lies in a finite set `s` of parts is
consistent, if the restriction to every fibre is consistent and the labels of walls in distinct
parts commute. -/
theorem consistent_restrict_preimage_finset (f : ι → β)
    (hD : ∀ b, (D.restrict (f ⁻¹' {b})).Consistent)
    (hcomm : ∀ a c, f a ≠ f c → Commute (D.wall a).label (D.wall c).label) (s : Finset β) :
    (D.restrict (f ⁻¹' s)).Consistent := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : IsEmpty (f ⁻¹' ↑(∅ : Finset β)) := ⟨fun j => by simpa using j.property⟩
    exact consistent_of_isEmpty _
  | insert b s hb ih =>
    -- Split the restriction to `f ⁻¹' (insert b s)` into the fibre over `b` and the rest.
    have h₁ : f ⁻¹' {b} ⊆ f ⁻¹' ↑(insert b s) := fun j hj => by simp_all
    have h₂ : f ⁻¹' ↑s ⊆ f ⁻¹' ↑(insert b s) := fun j hj => by simp_all
    have hc : (range (inclusion h₁))ᶜ = range (inclusion h₂) := by
      ext ⟨j, hj⟩
      simp only [Finset.coe_insert, mem_preimage, mem_insert_iff, Finset.mem_coe] at hj
      simp only [range_inclusion, mem_compl_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
        Finset.mem_coe]
      exact ⟨hj.resolve_left, fun hjs hjb => hb (hjb ▸ hjs)⟩
    refine consistent_of_restrict_of_restrict_compl (s := range (inclusion h₁)) ?_ ?_ ?_
    · exact ((D.restrict _).restrict_range_equivalent (inclusion_injective h₁)
        fun _ => by simp).consistent_iff.mpr (hD b)
    · rw [hc]
      exact ((D.restrict _).restrict_range_equivalent (inclusion_injective h₂)
        fun _ => by simp).consistent_iff.mpr ih
    · rintro _ ⟨a, rfl⟩ c hc'
      rw [restrict_wall, restrict_wall]
      refine hcomm _ _ fun he => hc' ⟨⟨c.val, ?_⟩, rfl⟩
      rw [coe_inclusion] at he
      exact mem_preimage.mpr (mem_singleton_iff.mpr
        (he.symm.trans (mem_singleton_iff.mp (mem_preimage.mp a.property))))

/-- **Commuting partitions.** Let `f : ι → β` map the walls of `D` to a finite type of parts. If the
restriction of `D` to every fibre of `f` is consistent and the label of every wall commutes with
the label of every wall in a different part, then `D` is consistent. For two parts this is
`consistent_of_restrict_of_restrict_compl`. -/
theorem consistent_of_restrict_preimage [Finite β] (f : ι → β)
    (hD : ∀ b, (D.restrict (f ⁻¹' {b})).Consistent)
    (hcomm : ∀ a c, f a ≠ f c → Commute (D.wall a).label (D.wall c).label) : D.Consistent := by
  have := Fintype.ofFinite β
  have hu := consistent_restrict_preimage_finset f hD hcomm Finset.univ
  rw [Finset.coe_univ, preimage_univ, ← range_id] at hu
  exact (D.restrict_range_equivalent Function.injective_id fun _ => rfl).consistent_iff.mp hu

/-- **Commuting unions.** If finitely many diagrams `D b` are consistent and every label of `D b`
commutes with every label of `D b'` for `b ≠ b'`, then their union `sigma D` is consistent. The
walls of distinct families may cross, overlap or coincide. -/
theorem Consistent.sigma [Finite β] {ι : β → Type*} {D : ∀ b, DirectedDiagram (d := d) h H (ι b)}
    (hD : ∀ b, (D b).Consistent)
    (hcomm : ∀ b b', b ≠ b' → ∀ j j', Commute ((D b).wall j).label ((D b').wall j').label) :
    (DirectedDiagram.sigma D).Consistent := by
  refine consistent_of_restrict_preimage Sigma.fst (fun b => ?_) fun ⟨b, j⟩ ⟨b', j'⟩ hne => ?_
  · rw [← range_sigmaMk]
    exact ((DirectedDiagram.sigma D).restrict_range_equivalent sigma_mk_injective
      fun j => (sigma_wall D b j).symm).consistent_iff.mpr (hD b)
  · rw [sigma_wall, sigma_wall]
    exact hcomm b b' hne j j'

end Mei.DirectedDiagram
