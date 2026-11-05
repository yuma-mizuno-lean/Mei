/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Germ
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing.Completed

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
does not prove that some grouping of a given representative exhausts the walls through a point.
Under these hypotheses, the statements compare the grouped wall functions of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), between two representatives of one completed class, as needed for the
wall functions on rays in Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, Theorem 9.5 (arXiv:2503.03719v1). The comparison of combined labels is
`DirectedDiagram.LevelEquivalent.combinedLabel_eq`.

## Wall functions at generic points

Groupings of the second diagram are not needed. A unit `f` is a *germ wall function* of `D` at a
regular point `θ`, in the direction `v` and for the normal `ν`
(`DirectedDiagram.IsGermWallFunction`), when the germ label `DirectedDiagram.germLabel` of `D` at
`θ` in the direction `v` acts on every monomial `z^p` by multiplication by `f^(ν(ρ p))`. Germ wall
functions are unique when some invertible monomial has weight one for `ν`
(`DirectedDiagram.IsGermWallFunction.unique`), and they are shared by equivalent diagrams at
common generic points of an affine subspace `A`, for directions outside the direction of `A`
(`DirectedDiagram.IsGermWallFunction.of_equivalent`). Crossing germs of a group at every order
make the point generic for the affine span of the group's support
(`FunctionWallGrouping.isGenericPoint_of_isCrossingGerm`), with the group label as germ label
(`FunctionWallGrouping.germLabel_eq_label`). So a wall function of a group with crossing germs at
`θ` and `v` at every order is the germ wall function, at `θ` and `v`, of every equivalent diagram
for which `θ` is a generic point of that affine span
(`FunctionWallGrouping.IsWallFunction.isGermWallFunction_of_equivalent`,
`FunctionWallGrouping.IsWallFunction.eq_of_isGermWallFunction`). By
`DirectedDiagram.exists_isGenericPoint`, every nonempty relatively open subset of a hyperplane
contains points that are generic for the second diagram, so the second diagram needs neither a
grouping nor matched crossing germs. The crossing germs of the first diagram's group at `θ` and
`v` at every order remain hypotheses of these bridge results.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V M M' : Type*} {ι ι' κ κ' : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup M] [AddCommGroup M']
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h H ι} {E : DirectedDiagram (d := d) h H ι'}
  {π : Γ →+ M} {π' : Γ →+ M'}

namespace FunctionWallGrouping

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

/-- Crossing germs at every order make the point regular. -/
theorem isRegular_of_isCrossingGerm (hgerm : ∀ k, G.IsCrossingGerm g k θ v) : D.IsRegular θ :=
  (D.isRegular_iff θ).mpr fun k => (hgerm k).notMem_singularSupport

/-- With crossing germs at every order, the germ label is the completed group label. -/
theorem germLabel_eq_label (hgerm : ∀ k, G.IsCrossingGerm g k θ v) :
    D.germLabel θ v (isRegular_of_isCrossingGerm hgerm) = G.label g :=
  ((G.eq_label_iff g _).mpr fun k => by
    rw [projection_germLabel, (hgerm k).combinedLabel_eq])

/-- If the group `g` has crossing germs at `θ` and `v` at every order and `θ` lies on a wall `j`
of `g`, then `θ` is a generic point of the affine span of the support of `j`. -/
theorem isGenericPoint_of_isCrossingGerm (hgerm : ∀ k, G.IsCrossingGerm g k θ v) {j : ι}
    (hj : G.group j = g) (hθ : θ ∈ (D.wall j).support) :
    D.IsGenericPoint (affineSpan ℝ (D.wall j).support) θ where
  mem := subset_affineSpan ℝ _ hθ
  isRegular := isRegular_of_isCrossingGerm hgerm
  affineSpan_eq {k} j' hj' := by
    rw [G.support_eq ((((hgerm k).mem_support_iff j').mp hj').trans hj.symm)]

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

end FunctionWallGrouping

section GermWallFunction

open _root_.AddMonoidAlgebra

variable {A : Type*} [CommRing A] [Algebra R A]
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))

variable (D) in
/-- A unit `f` is a *germ wall function* of `D` at the regular point `θ`, in the direction `v`
and for the normal `ν`, when the germ label of `D` at `θ` in the direction `v` acts on every
monomial `z^p` by multiplication by `f^(ν(ρ p))`. In the intended use, `ν` is the common
primitive normal of the walls through `θ` and `v` pairs negatively with it, so that the germ label
is the product of the labels of these walls. -/
def IsGermWallFunction (θ v : V) (hθ : D.IsRegular θ) (ν : Λ →+ ℤ) (f : F.completionˣ) : Prop :=
  ∀ (p : Q) (c : A), σ (D.germLabel θ v hθ) (F.toCompletion (single p c)) =
    ((f ^ ν (ρ p) : F.completionˣ) : F.completion) * F.toCompletion (single p c)

variable (D) in
/-- The defining monomial action of a germ wall function. -/
theorem isGermWallFunction_iff (θ v : V) (hθ : D.IsRegular θ) (ν : Λ →+ ℤ) (f : F.completionˣ) :
    D.IsGermWallFunction σ θ v hθ ν f ↔ ∀ (p : Q) (c : A),
      σ (D.germLabel θ v hθ) (F.toCompletion (single p c)) =
        ((f ^ ν (ρ p) : F.completionˣ) : F.completion) * F.toCompletion (single p c) :=
  Iff.rfl

variable {σ} {θ v : V} {ν : Λ →+ ℤ}

/-- Germ wall functions for a normal `ν` are unique when some monomial of weight one for `ν` is
invertible in the completion. -/
theorem IsGermWallFunction.unique {hθ : D.IsRegular θ} {f f' : F.completionˣ}
    (hf : D.IsGermWallFunction σ θ v hθ ν f) (hf' : D.IsGermWallFunction σ θ v hθ ν f')
    (hp : ∃ p : Q, ν (ρ p) = 1 ∧ IsUnit (F.toCompletion (single p (1 : A)))) : f = f' := by
  obtain ⟨p, hp, hu⟩ := hp
  have he := ((D.isGermWallFunction_iff σ θ v hθ ν f).mp hf p 1).symm.trans
    ((D.isGermWallFunction_iff σ θ v hθ ν f').mp hf' p 1)
  exact Units.ext (hu.mul_right_cancel (by simpa only [hp, zpow_one] using he))

/-- **Germ wall functions of equivalent diagrams.** Equivalent diagrams have the same germ wall
functions at a common generic point of an affine subspace `B`, for every direction outside the
direction of `B` and every normal. -/
theorem IsGermWallFunction.of_equivalent (hDE : D.Equivalent E) {B : AffineSubspace ℝ V}
    (hD : D.IsGenericPoint B θ) (hE : E.IsGenericPoint B θ) (hv : v ∉ B.direction)
    {f : F.completionˣ} (hf : D.IsGermWallFunction σ θ v hD.isRegular ν f) :
    E.IsGermWallFunction σ θ v hE.isRegular ν f := by
  rw [isGermWallFunction_iff, ← hDE.germLabel_eq hD hE hv]
  exact hf

end GermWallFunction

namespace FunctionWallGrouping

section GermWallFunction

open _root_.AddMonoidAlgebra

variable {G : D.FunctionWallGrouping π κ} {g : κ} {θ v : V}

variable {A : Type*} [CommRing A] [Algebra R A]
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}

/-- With crossing germs at every order, a wall function of a group is the germ wall function for
the normal of any wall of the group. -/
theorem IsWallFunction.isGermWallFunction {f : F.completionˣ} (hf : G.IsWallFunction σ g f)
    (hgerm : ∀ k, G.IsCrossingGerm g k θ v) {j : ι} (hj : G.group j = g) :
    D.IsGermWallFunction σ θ v (isRegular_of_isCrossingGerm hgerm) (D.wall j).normal f := by
  rw [isGermWallFunction_iff, germLabel_eq_label hgerm]
  exact ((G.isWallFunction_iff σ g f).mp hf j hj).2

/-- **Wall functions in every representative.** Let the group `g` of `G` have crossing germs at
`θ` and `v` at every order, let `j` be a wall of `g` through `θ`, and let `v` be transverse to
it. Let `E` be equivalent to `D`, with `θ` a generic point of the affine span of the support of
`j` for `E`. Then a wall function of `g` is a germ wall function of `E` at `θ` and `v` for the
normal of `j`. No grouping of `E` is involved. -/
theorem IsWallFunction.isGermWallFunction_of_equivalent {f : F.completionˣ}
    (hf : G.IsWallFunction σ g f) (hgerm : ∀ k, G.IsCrossingGerm g k θ v) {j : ι}
    (hj : G.group j = g) (hθ : θ ∈ (D.wall j).support)
    (hv : v ∉ (affineSpan ℝ (D.wall j).support).direction) (hDE : D.Equivalent E)
    (hE : E.IsGenericPoint (affineSpan ℝ (D.wall j).support) θ) :
    E.IsGermWallFunction σ θ v hE.isRegular (D.wall j).normal f :=
  (hf.isGermWallFunction hgerm hj).of_equivalent hDE
    (isGenericPoint_of_isCrossingGerm hgerm hj hθ) hE hv

/-- **Uniqueness of wall functions in every representative.** Under the hypotheses of
`FunctionWallGrouping.IsWallFunction.isGermWallFunction_of_equivalent`, every germ wall function
of `E` at `θ` and `v` for the normal of `j` is the wall function of `g`. -/
theorem IsWallFunction.eq_of_isGermWallFunction {f f' : F.completionˣ}
    (hf : G.IsWallFunction σ g f) (hgerm : ∀ k, G.IsCrossingGerm g k θ v) {j : ι}
    (hj : G.group j = g) (hθ : θ ∈ (D.wall j).support)
    (hv : v ∉ (affineSpan ℝ (D.wall j).support).direction) (hDE : D.Equivalent E)
    (hE : E.IsGenericPoint (affineSpan ℝ (D.wall j).support) θ)
    (hf' : E.IsGermWallFunction σ θ v hE.isRegular (D.wall j).normal f') : f' = f :=
  hf'.unique (hf.isGermWallFunction_of_equivalent hgerm hj hθ hv hDE hE)
    ((G.isWallFunction_iff σ g f).mp hf j hj).1

end GermWallFunction

end FunctionWallGrouping

end Mei.DirectedDiagram
