/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Germ

/-!
# Group labels and wall functions of equivalent diagrams

A function-wall grouping of a directed diagram `D` has a *crossing germ* for the group `g` at
order `k`, a point `θ` and a direction `v` (`FunctionWallGrouping.IsCrossingGerm`) when `θ` is
a regular point of the walls active at order `k`, the active walls through `θ` are exactly the
active walls of `g`, and `v` pairs negatively with their normals. The combined crossing label
of `D` at `θ` in direction `v` is then the group label of `g`
(`FunctionWallGrouping.IsCrossingGerm.combinedLabel_eq`). A crossing germ at some order is one
at every lower order (`FunctionWallGrouping.IsCrossingGerm.mono`).

Equivalent diagrams have equal combined labels at common regular points
(`DirectedDiagram.LevelEquivalent.combinedLabel_eq`). Hence, if `D` and `E` are equivalent at
order `k` and groupings `G` of `D` and `G'` of `E` have crossing germs for groups `g` and `g'`
at the same `θ` and `v`, then `g` and `g'` have the same group label at order `k`
(`FunctionWallGrouping.IsCrossingGerm.groupLabel_eq`). If `D` and `E` are equivalent and the two
groups have common crossing germs at every order, their completed group labels agree
(`FunctionWallGrouping.label_eq_of_equivalent`). If moreover a wall of `g` and a wall of `g'`
have the same normal, the wall functions of the two groups agree
(`FunctionWallGrouping.IsWallFunction.eq_of_equivalent`), and a wall function of `g'` is positive
when `g` belongs to a positive grouping
(`FunctionWallGrouping.IsWallFunction.isPositive_of_equivalent`).

The common crossing germs and the common normal are hypotheses of these statements. This file
does not prove that they exist, for instance that a generic point of a ray of a completion is
regular at every order, or that some grouping of a given representative exhausts the walls
through it. Under these hypotheses, the statements compare the grouped wall functions of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), between two representatives of one completed class, as needed for the
wall functions on rays in Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, Theorem 9.5 (arXiv:2503.03719v1). The comparison of combined labels is
`DirectedDiagram.LevelEquivalent.combinedLabel_eq`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram.FunctionWallGrouping

variable {Γ Λ R L V M M' : Type*} {ι ι' κ κ' : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup M] [AddCommGroup M']
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h H ι} {E : DirectedDiagram (d := d) h H ι'}
  {π : Γ →+ M} {π' : Γ →+ M'}

variable (G : D.FunctionWallGrouping π κ) in
/-- The group `g` has a crossing germ at order `k`, the point `θ` and the direction `v`: the
point `θ` is regular for the walls active at order `k`, it lies exactly on the active walls of
`g`, and `v` pairs negatively with their normals. -/
structure IsCrossingGerm (g : κ) (k : ℕ) (θ v : V) : Prop where
  /-- The point is regular for the walls active at order `k`. -/
  notMem_singularSupport : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)
  /-- The active walls through the point are exactly the active walls of the group. -/
  mem_support_iff (j : D.active k) : θ ∈ (D.wall j).support ↔ G.group j = g
  /-- The direction pairs negatively with the normals of the active walls of the group. -/
  realCharacter_normal_neg (j : D.active k) :
    G.group j = g → h.realCharacter (D.wall j).normal v < 0

variable {G : D.FunctionWallGrouping π κ} {G' : E.FunctionWallGrouping π' κ'}
  {g : κ} {g' : κ'} {k : ℕ} {θ v : V}

/-- The defining conditions of a crossing germ. -/
theorem isCrossingGerm_iff : G.IsCrossingGerm g k θ v ↔
    θ ∉ singularSupport (fun j : D.active k => (D.wall j).support) ∧
      (∀ j : D.active k, θ ∈ (D.wall j).support ↔ G.group j = g) ∧
      ∀ j : D.active k, G.group j = g → h.realCharacter (D.wall j).normal v < 0 :=
  ⟨fun hG => ⟨hG.1, hG.2, hG.3⟩, fun hG => ⟨hG.1, hG.2.1, hG.2.2⟩⟩

/-- At a crossing germ, the direction is transverse to every active wall through the point. -/
theorem IsCrossingGerm.realCharacter_normal_ne_zero (hG : G.IsCrossingGerm g k θ v)
    (j : D.active k) (hj : θ ∈ (D.wall j).support) : h.realCharacter (D.wall j).normal v ≠ 0 :=
  (hG.realCharacter_normal_neg j ((hG.mem_support_iff j).mp hj)).ne

/-- At a crossing germ, the combined crossing label is the group label. -/
theorem IsCrossingGerm.combinedLabel_eq (hG : G.IsCrossingGerm g k θ v) :
    D.combinedLabel k θ v hG.notMem_singularSupport = G.groupLabel g k :=
  G.combinedLabel_eq_groupLabel hG.notMem_singularSupport hG.mem_support_iff
    hG.realCharacter_normal_neg

/-- A crossing germ at order `l` is a crossing germ at every lower order `k`: fewer walls are
active, and restricting a wall family adds no singular points. -/
theorem IsCrossingGerm.mono {l : ℕ} (hG : G.IsCrossingGerm g l θ v) (hkl : k ≤ l) :
    G.IsCrossingGerm g k θ v where
  notMem_singularSupport hθ := hG.notMem_singularSupport
    (singularSupport_comp_subset (fun j : D.active l => (D.wall j).support)
      (Set.inclusion (D.active_mono hkl)) hθ)
  mem_support_iff j := hG.mem_support_iff (Set.inclusion (D.active_mono hkl) j)
  realCharacter_normal_neg j := hG.realCharacter_normal_neg (Set.inclusion (D.active_mono hkl) j)

/-- **Group labels of equivalent diagrams.** If `D` and `E` are equivalent at order `k` and the
groups `g` of `G` and `g'` of `G'` have crossing germs at order `k`, the same point and the same
direction, then they have the same group label at order `k`. -/
theorem IsCrossingGerm.groupLabel_eq (hDE : D.LevelEquivalent E k)
    (hG : G.IsCrossingGerm g k θ v) (hG' : G'.IsCrossingGerm g' k θ v) :
    G.groupLabel g k = G'.groupLabel g' k := by
  rw [← hG.combinedLabel_eq, ← hG'.combinedLabel_eq]
  exact hDE.combinedLabel_eq θ v _ _ hG.realCharacter_normal_ne_zero
    hG'.realCharacter_normal_ne_zero

/-- **Completed group labels of equivalent diagrams.** If `D` and `E` are equivalent and, at
every order, the groups `g` of `G` and `g'` of `G'` have crossing germs at a common point and
direction, then they have the same completed label. By `IsCrossingGerm.mono`, crossing germs at
arbitrarily large orders suffice. -/
theorem label_eq_of_equivalent (hDE : D.Equivalent E)
    (hgerm : ∀ k, ∃ θ v, G.IsCrossingGerm g k θ v ∧ G'.IsCrossingGerm g' k θ v) :
    G.label g = G'.label g' :=
  CompletedGroup.ext fun k => by
    obtain ⟨θ, v, hG, hG'⟩ := hgerm k
    rw [projection_label, projection_label]
    exact hG.groupLabel_eq ((equivalent_iff D E).mp hDE k) hG'

section WallFunction

variable {A : Type*} [CommRing A] [Algebra R A]
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}

/-- **Wall functions of equivalent diagrams.** Let `D` and `E` be equivalent, and suppose that at
every order the groups `g` of `G` and `g'` of `G'` have crossing germs at a common point and
direction. If some wall of `g` and some wall of `g'` have the same normal, then wall functions
of `g` and `g'` for the same action are equal. -/
theorem IsWallFunction.eq_of_equivalent {f f' : F.completionˣ} (hDE : D.Equivalent E)
    (hgerm : ∀ k, ∃ θ v, G.IsCrossingGerm g k θ v ∧ G'.IsCrossingGerm g' k θ v)
    (hf : G.IsWallFunction σ g f) (hf' : G'.IsWallFunction σ g' f') {j : ι} {j' : ι'}
    (hj : G.group j = g) (hj' : G'.group j' = g')
    (hν : (D.wall j).normal = (E.wall j').normal) : f = f' :=
  hf.eq_of_label_eq hf' (label_eq_of_equivalent hDE hgerm) hj hj' hν

/-- **Positivity of matched wall functions.** Let `G` be a positive grouping of `D`, and let `E`
be equivalent to `D`. Suppose that at every order the groups `g` of `G` and `g'` of a grouping
`G'` of `E` have crossing germs at a common point and direction, and that some wall of `g` and
some wall of `g'` have the same normal. Then every wall function of `g'` is positive. -/
theorem IsWallFunction.isPositive_of_equivalent {P : Subsemiring (AddMonoidAlgebra A Q)}
    {f' : F.completionˣ} (hf' : G'.IsWallFunction σ g' f') (hG : G.IsPositive σ P)
    (hDE : D.Equivalent E)
    (hgerm : ∀ k, ∃ θ v, G.IsCrossingGerm g k θ v ∧ G'.IsCrossingGerm g' k θ v)
    {j : ι} {j' : ι'} (hj : G.group j = g) (hj' : G'.group j' = g')
    (hν : (D.wall j).normal = (E.wall j').normal) : F.IsPositive P f' := by
  obtain ⟨f, hf, hpos⟩ := (G.isPositive_iff σ P).mp hG g
  rwa [← hf.eq_of_equivalent hDE hgerm hf' hj hj' hν]

end WallFunction

end Mei.DirectedDiagram.FunctionWallGrouping
