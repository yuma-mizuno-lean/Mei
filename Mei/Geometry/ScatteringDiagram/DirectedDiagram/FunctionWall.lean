/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.RingTheory.FilteredAlgebra.Positive.Basic

/-!
# Function-wall groupings and positive wall representatives

A directed diagram presents its walls one supported ray at a time. Positivity statements
for scattering diagrams are instead stated for *function walls*: commuting ray walls on a
common support with a common primitive coorientation and projected monomial direction
are grouped. The group acts on coefficient monomials by a single wall function `f`,
as `z^p ↦ f^(ν(ρ p)) z^p`.

A `DirectedDiagram.FunctionWallGrouping` assigns each wall to a group, such that walls in
one group have the same support and the same primitive normal. Their nontrivial labels
also have a common monomial direction under a fixed spatial projection `π`. Their labels
then commute.
At each cutoff the *group label* is the product of the projected labels of the active
walls of the group (`FunctionWallGrouping.groupLabel`). These are compatible under
truncation, and their limit is the completed *label* of the group
(`FunctionWallGrouping.label`), the convergent product of the labels of its walls. The
grouping does not change the diagram, so the path products are those of the ray
presentation. At a regular point lying exactly on the active walls of one group, the
combined crossing label is the group label, or its inverse for the opposite crossing
direction. Hence a segment crossing only that germ has the projection of the group label as
its path product (`FunctionWallGrouping.levelPathProduct_toPath_eq_projection_label`).

For an action `σ` of the completed group on the completion of a filtered monoid algebra
`A[Q]`, a unit `f` is a *wall function* of a group when its label acts on every
monomial `z^p` by multiplication by `f^(ν(ρ p))`, where `ν` is the group's normal
(`FunctionWallGrouping.IsWallFunction`). The coefficient ring `A` is any algebra over the
scalars `R` of the Lie algebra; for instance `R = ℚ` when tropical vertex coefficients are
compared along a change of coefficient ring. We require an invertible monomial of normal
weight one for each nonempty group, so that this action uniquely determines `f`
(`FunctionWallGrouping.IsWallFunction.unique`). More generally, groups of groupings of two
diagrams with the same completed label and a common normal have the same wall function
(`FunctionWallGrouping.IsWallFunction.eq_of_label_eq`). For a chosen
positive subsemiring `P ⊆ A[Q]`,
a grouping is positive if every group has a wall function that is positive in the sense
of `AlgFiltration.IsPositive`, and a diagram is a *positive wall representative* if it
admits a positive grouping (`DirectedDiagram.IsPositiveWallRepresentative`). A ring map of
completed coefficients that sends monomials onto monomials, intertwines the actions of two
group labels, preserves the normal pairings and whose target label fixes constants carries
wall functions to wall functions (`FunctionWallGrouping.IsWallFunction.of_intertwining`). A
positive specialization doing so for every group carries positive groupings to positive
groupings (`FunctionWallGrouping.IsPositive.of_isWallFunction_completionMap`). Walls in
one group may have different degree rays, but their nontrivial labels must have positively
proportional projected generators. Identity labels impose no direction constraint. For
instance, the full cylinder over a polynomial in a single spatial monomial splits into
ray walls of different directions in the lattice of independent coefficient variables,
which reassemble into one function wall under projection to the spatial lattice.

These definitions follow the grouped wall functions of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 and Theorem 1.13 (arXiv:1411.1394v2), and
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §8.1 and
Theorem 9.9 (arXiv:2503.03719v1). The local crossing comparison uses
`DirectedDiagram.combinedLabel_eq_noncommProd` and
`DirectedDiagram.levelPathProduct_toPath_eq_combinedLabel`.
-/

public section

noncomputable section

open Set Mei.Convex CategoryTheory

namespace Mei

namespace DirectedDiagram

universe u

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {ι : Type u}
  (D : DirectedDiagram (d := d) h H ι)
  {M : Type*} [AddCommGroup M]

/-- A grouping of the walls of a directed diagram into function walls, indexed by `κ`.
Walls in one group have the same support and the same normal, and every normal is
primitive. The nontrivial walls in a group have positively proportional monomial
directions under the spatial projection `π`. Distinct groups may share a support. -/
@[ext]
structure FunctionWallGrouping (π : Γ →+ M) (κ : Type*) where
  /-- The function wall containing each indexed ray wall. -/
  group : ι → κ
  /-- Walls in one group have the same support. -/
  support_eq {j j' : ι} : group j = group j' → (D.wall j).support = (D.wall j').support
  /-- Walls in one group have the same coorientation. -/
  normal_eq {j j' : ι} : group j = group j' → (D.wall j).normal = (D.wall j').normal
  /-- Nontrivial walls in a group have the same projected monomial direction.
  Positive integer multiples express equality of rational rays, including zero directions. -/
  projectedDirection_eq {j j' : ι} : group j = group j' →
    (D.wall j).label ≠ 1 → (D.wall j').label ≠ 1 →
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      a • π (D.wall j).ray.generator = b • π (D.wall j').ray.generator
  /-- The coorientations are primitive, so that wall functions are normalized. -/
  isPrimitive_normal (j : ι) : TauCeti.IsPrimitive (D.wall j).normal

namespace FunctionWallGrouping

variable {D} {π : Γ →+ M} {κ : Type*} (G : D.FunctionWallGrouping π κ)

/-- Walls in one group have commuting completed labels. -/
theorem commute_label {j j' : ι} (hj : G.group j = G.group j') :
    Commute (D.wall j).label (D.wall j').label :=
  (D.wall j).commute_label_of_direction_eq (D.wall j') (by rw [G.support_eq hj])

/-- The order-`k` label of the group `g`: the product of the projected labels of the
walls of `g` active at order `k`. -/
def groupLabel (g : κ) (k : ℕ) : d.truncatedGroup ℒ k :=
  (Set.toFinite {j : D.active k | G.group j = g}).toFinset.noncommProd
    (fun j => CompletedGroup.projection k (D.wall j).label) (by
      intro a ha b hb _
      have ha : G.group a = g := by simpa using ha
      have hb : G.group b = g := by simpa using hb
      exact (G.commute_label (ha.trans hb.symm)).map _)

/-- Any finite set of walls of the group containing its active walls computes the group
label: the projected labels of the remaining walls are trivial. -/
theorem groupLabel_eq_noncommProd (g : κ) (k : ℕ) (s : Finset ι)
    (hs : ∀ j ∈ s, G.group j = g) (hact : ∀ j ∈ D.active k, G.group j = g → j ∈ s) :
    G.groupLabel g k = s.noncommProd (fun j => CompletedGroup.projection k (D.wall j).label)
      (fun a ha b hb _ => (G.commute_label ((hs a ha).trans (hs b hb).symm)).map _) := by
  classical
  let T := (Set.toFinite {j : D.active k | G.group j = g}).toFinset
  let e : D.active k ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have hTs : T.map e ⊆ s := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    exact hact a a.property (by simpa [T] using ha)
  unfold groupLabel
  refine (Finset.noncommProd_map T e (fun j => CompletedGroup.projection k (D.wall j).label)
    (fun a ha b hb _ => (G.commute_label ((hs a (hTs ha)).trans
      (hs b (hTs hb)).symm)).map _)).symm.trans
    (Finset.noncommProd_subset hTs _ _ fun j hj hjT => ?_)
  by_contra hne
  exact hjT (Finset.mem_map.mpr ⟨⟨j, (D.mem_active k j).mpr hne⟩, by simpa [T] using hs j hj, rfl⟩)

/-- At a regular point lying exactly on the active walls of the group `g`, the combined
label in a direction pairing negatively with the common normal is the group label. -/
theorem combinedLabel_eq_groupLabel {k : ℕ} {θ v : V}
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) {g : κ}
    (hg : ∀ j : D.active k, θ ∈ (D.wall j).support ↔ G.group j = g)
    (hv : ∀ j : D.active k, G.group j = g → h.realCharacter (D.wall j).normal v < 0) :
    D.combinedLabel k θ v hθ = G.groupLabel g k := by
  unfold groupLabel
  rw [D.combinedLabel_eq_noncommProd k θ v hθ
    (Set.toFinite {j : D.active k | G.group j = g}).toFinset
    (fun j => by simpa using (hg j).symm) (by
      intro a ha b hb _
      have ha : G.group a = g := by simpa using ha
      have hb : G.group b = g := by simpa using hb
      exact ((G.commute_label (ha.trans hb.symm)).map _).zpow_zpow _ _)]
  refine Finset.noncommProd_congr rfl (fun j hj => ?_) _
  have hj : G.group j = g := by simpa using hj
  rw [ite_eq_right (not_lt.mpr (hv j hj).le), zpow_one]

/-- At a regular point lying exactly on the active walls of the group `g`, the combined
label in a direction pairing positively with the common normal is the inverse group
label. -/
theorem combinedLabel_eq_groupLabel_inv {k : ℕ} {θ v : V}
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) {g : κ}
    (hg : ∀ j : D.active k, θ ∈ (D.wall j).support ↔ G.group j = g)
    (hv : ∀ j : D.active k, G.group j = g → 0 < h.realCharacter (D.wall j).normal v) :
    D.combinedLabel k θ v hθ = (G.groupLabel g k)⁻¹ := by
  have hneg : D.combinedLabel k θ (-v) hθ = G.groupLabel g k :=
    G.combinedLabel_eq_groupLabel hθ hg fun j hj => by
      rw [map_neg, neg_lt_zero]
      exact hv j hj
  rw [← hneg, D.combinedLabel_neg k θ v hθ fun j hj => (hv j ((hg j).mp hj)).ne', inv_inv]

/-- The group labels are compatible with the truncation maps of the BCH tower. -/
@[simp]
theorem map_groupLabel (g : κ) {k l : ℕ} (hkl : k ≤ l) :
    (d.truncationMap ℒ hkl).bchGroupMap (G.groupLabel g l) = G.groupLabel g k := by
  classical
  let s := (Set.toFinite (D.active l)).toFinset.filter fun j => G.group j = g
  have hs : ∀ j ∈ s, G.group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hl : ∀ j ∈ D.active l, G.group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite _).mem_toFinset.mpr hj, hg⟩
  rw [G.groupLabel_eq_noncommProd g l s hs hl,
    G.groupLabel_eq_noncommProd g k s hs fun j hj hg => hl j (D.active_mono hkl hj) hg]
  refine (Finset.map_noncommProd s _ _ _).trans (Finset.noncommProd_congr rfl ?_ _)
  intro j _
  exact CompletedGroup.map_projection k l hkl (D.wall j).label

/-- The completed label of the group `g`: the convergent product of the commuting labels
of its walls, whose order-`k` projection is the group label. -/
def label (g : κ) : d.completedBCHGroup ℒ :=
  ⟨fun k => G.groupLabel g k,
    (mem_completedGroup_iff _ _).mpr fun _ _ hkl => G.map_groupLabel g hkl⟩

/-- The finite-order projections of the completed group label are the group labels. -/
@[simp]
theorem projection_label (g : κ) (k : ℕ) :
    CompletedGroup.projection k (G.label g) = G.groupLabel g k :=
  CompletedGroup.projection_apply k _

/-- The completed group label is the unique element with the group labels as projections. -/
theorem eq_label_iff (g : κ) (l : d.completedBCHGroup ℒ) :
    l = G.label g ↔ ∀ k, CompletedGroup.projection k l = G.groupLabel g k :=
  ⟨by rintro rfl k; exact G.projection_label g k,
    fun hl => CompletedGroup.ext fun k => (hl k).trans (G.projection_label g k).symm⟩

/-- A segment crossing exactly the active walls of the group `g`, at one regular point and
negatively against their common normal, has the projection of the group label as its
finite-order path product. -/
theorem levelPathProduct_toPath_eq_projection_label {g : κ} {k : ℕ}
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)} (e : x ⟶ y)
    (θ : V) (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (t : ℝ) (hcross : ∀ j s, (j, s) ∈ WallComplement.crossings x y ↔
      θ ∈ (D.wall j).support ∧ s = t)
    (hg : ∀ j : D.active k, θ ∈ (D.wall j).support ↔ G.group j = g)
    (hv : ∀ j : D.active k, G.group j = g →
      h.realCharacter (D.wall j).normal (y.val - x.val) < 0) :
    D.levelPathProduct k e.toPath = CompletedGroup.projection k (G.label g) := by
  rw [D.levelPathProduct_toPath_eq_combinedLabel k e θ hθ t hcross,
    G.combinedLabel_eq_groupLabel hθ hg hv, G.projection_label g k]

/-- Two groups with the same walls have the same group label. -/
theorem groupLabel_congr {M' : Type*} [AddCommGroup M'] {π' : Γ →+ M'} {κ' : Type*}
    (G' : D.FunctionWallGrouping π' κ') {g : κ} {g' : κ'}
    (hgg' : ∀ j, G.group j = g ↔ G'.group j = g') (k : ℕ) :
    G.groupLabel g k = G'.groupLabel g' k :=
  Finset.noncommProd_congr (by ext j; simp [hgg']) (fun _ _ => rfl) _

/-- An empty group has trivial group label. -/
theorem groupLabel_eq_one {g : κ} (hg : ∀ j, G.group j ≠ g) (k : ℕ) : G.groupLabel g k = 1 :=
  (G.groupLabel_eq_noncommProd g k ∅ (by simp) fun j _ hj => (hg j hj).elim).trans
    (Finset.noncommProd_empty _ _)

/-- The same grouping, with each group indexed by its set of walls. -/
def toSet : D.FunctionWallGrouping π (Set ι) where
  group j := {j' | G.group j' = G.group j}
  support_eq {j _} hj := G.support_eq ((Set.ext_iff.mp hj j).mp rfl)
  normal_eq {j _} hj := G.normal_eq ((Set.ext_iff.mp hj j).mp rfl)
  projectedDirection_eq {j _} hj :=
    G.projectedDirection_eq ((Set.ext_iff.mp hj j).mp rfl)
  isPrimitive_normal := G.isPrimitive_normal

@[simp]
theorem toSet_group (j : ι) : G.toSet.group j = {j' | G.group j' = G.group j} := (rfl)

/-- A wall lies in the set-indexed group of the walls of `g` exactly when it lies in `g`. -/
theorem toSet_group_eq_iff (j : ι) (g : κ) :
    G.toSet.group j = {j' | G.group j' = g} ↔ G.group j = g := by
  constructor
  · intro hj
    have hmem : j ∈ G.toSet.group j := rfl
    rw [hj] at hmem
    exact hmem
  · intro hj
    rw [toSet_group, hj]

/-- The set-indexed group of the walls of `g` has the label of `g`. -/
@[simp]
theorem toSet_label (g : κ) : G.toSet.label {j | G.group j = g} = G.label g :=
  ((G.toSet.eq_label_iff _ _).mpr fun k => by
    rw [G.projection_label g k]
    exact G.groupLabel_congr G.toSet (fun j => (G.toSet_group_eq_iff j g).symm) k).symm

/-- A group without walls has the identity label. -/
theorem label_eq_one {g : κ} (hg : ∀ j, G.group j ≠ g) : G.label g = 1 :=
  ((G.eq_label_iff g 1).mpr fun k => (map_one _).trans (G.groupLabel_eq_one hg k).symm).symm

section WallFunction

open AddMonoidAlgebra

variable {A : Type*} [CommRing A] [Algebra R A]
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))

/-- A unit `f` is a wall function of the group `g` for the action `σ` when the label of `g`
acts on every monomial `z^p` by multiplication by `f^(ν(ρ p))`, where `ν` is the common
normal of the walls of `g`. Each such normal must admit a monomial of weight one
whose image in the completion is invertible; this lets the action recover `f`. -/
def IsWallFunction (g : κ) (f : F.completionˣ) : Prop :=
  ∀ j, G.group j = g →
    (∃ p : Q, (D.wall j).normal (ρ p) = 1 ∧ IsUnit (F.toCompletion (single p (1 : A)))) ∧
    ∀ (p : Q) (c : A),
    σ (G.label g) (F.toCompletion (single p c)) =
      ((f ^ (D.wall j).normal (ρ p) : F.completionˣ) : F.completion) *
        F.toCompletion (single p c)

/-- The defining monomial action of a wall function. -/
theorem isWallFunction_iff (g : κ) (f : F.completionˣ) :
    G.IsWallFunction σ g f ↔ ∀ j, G.group j = g →
      (∃ p : Q, (D.wall j).normal (ρ p) = 1 ∧ IsUnit (F.toCompletion (single p (1 : A)))) ∧
      ∀ (p : Q) (c : A),
      σ (G.label g) (F.toCompletion (single p c)) =
        ((f ^ (D.wall j).normal (ρ p) : F.completionˣ) : F.completion) *
          F.toCompletion (single p c) := Iff.rfl

variable {G σ} in
/-- Wall functions of groups with the same completed label are equal, provided some wall of the
first group has the same normal as some wall of the second group. The groups may belong to
groupings of two different diagrams, with different spatial projections. The proof cancels an
invertible monomial of normal weight one. -/
theorem IsWallFunction.eq_of_label_eq {ι' κ' M' : Type*} [AddCommGroup M'] {π' : Γ →+ M'}
    {E : DirectedDiagram (d := d) h H ι'} {G' : E.FunctionWallGrouping π' κ'} {g : κ} {g' : κ'}
    {f f' : F.completionˣ} (hf : G.IsWallFunction σ g f) (hf' : G'.IsWallFunction σ g' f')
    (hl : G.label g = G'.label g') {j : ι} {j' : ι'} (hj : G.group j = g)
    (hj' : G'.group j' = g') (hν : (D.wall j).normal = (E.wall j').normal) : f = f' := by
  obtain ⟨p, hp, hu⟩ := ((G.isWallFunction_iff σ g f).mp hf j hj).1
  have he := (((G.isWallFunction_iff σ g f).mp hf j hj).2 p 1).symm.trans
    (hl ▸ ((G'.isWallFunction_iff σ g' f').mp hf' j' hj').2 p 1)
  exact Units.ext (hu.mul_right_cancel (by simpa only [← hν, hp, zpow_one] using he))

variable {G σ} in
/-- The action determines the wall function of a nonempty group uniquely, by cancellation
of an invertible monomial of normal weight one. -/
theorem IsWallFunction.unique {g : κ} {f f' : F.completionˣ}
    (hf : G.IsWallFunction σ g f) (hf' : G.IsWallFunction σ g f')
    {j : ι} (hj : G.group j = g) : f = f' :=
  hf.eq_of_label_eq hf' rfl hj hj rfl

variable (P : Subsemiring (AddMonoidAlgebra A Q))

/-- A grouping is positive when every group has a wall function positive for `P`. -/
def IsPositive : Prop :=
  ∀ g : κ, ∃ f : F.completionˣ, G.IsWallFunction σ g f ∧ F.IsPositive P f

/-- The defining condition of a positive grouping. -/
theorem isPositive_iff :
    G.IsPositive σ P ↔ ∀ g : κ, ∃ f : F.completionˣ, G.IsWallFunction σ g f ∧ F.IsPositive P f :=
  Iff.rfl

variable {G σ P} in
/-- Indexing the groups by their sets of walls preserves positivity. Sets of walls that do
not form a group are empty groups, with the trivial wall function. -/
theorem IsPositive.toSet (hG : G.IsPositive σ P) : G.toSet.IsPositive σ P := by
  refine (G.toSet.isPositive_iff σ P).mpr fun S => ?_
  by_cases hS : ∃ g, S = {j | G.group j = g} ∧ ∃ j, G.group j = g
  · obtain ⟨g, rfl, -⟩ := hS
    obtain ⟨f, hact, hf⟩ := (G.isPositive_iff σ P).mp hG g
    refine ⟨f, (G.toSet.isWallFunction_iff σ _ f).mpr fun j hj => ?_, hf⟩
    rw [G.toSet_label g]
    exact (G.isWallFunction_iff σ g f).mp hact j ((G.toSet_group_eq_iff j g).mp hj)
  · have hne : ∀ j, G.toSet.group j ≠ S := fun j hj => hS ⟨G.group j, hj.symm, j, rfl⟩
    exact ⟨1, (G.toSet.isWallFunction_iff σ S 1).mpr fun j hj => (hne j hj).elim,
      AlgFiltration.isPositive_one⟩

end WallFunction

section Transfer

open AddMonoidAlgebra

variable {Γ' Λ' L' V' M' : Type*} [AddCommGroup Γ'] [AddCommGroup Λ']
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] [DecidableEq Γ']
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [AddCommGroup M']
  {ρ' : Γ' →+ Λ'} {ℳ : Γ' → Submodule R L'} {d' : PositiveDegrees Γ'}
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i' : Λ' →+ V'} {h' : TauCeti.Toric.IsIntegralLattice i'} {H' : DirectedWallSpaces ρ' ℳ}
  {ι' : Type*} {D' : DirectedDiagram (d := d') h' H' ι'} {π' : Γ' →+ M'} {κ' : Type*}
  {A A' : Type*} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
  {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  {F : AlgFiltration (AddMonoidAlgebra A Q)} {F' : AlgFiltration (AddMonoidAlgebra A' Q')}
  {σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion)}
  {σ' : d'.completedBCHGroup ℳ →* (F'.completion ≃ₐ[R] F'.completion)}

variable {G} in
/-- **Transfer of wall functions.** Let `Φ` be a ring map of completed coefficient algebras
sending each monomial `z^p` to `z^{τ p}` for a surjection `τ : Q → Q'` of exponents, and
intertwining the action of the label of a group `g` of `D` with the action of the label of a
group `g'` of another diagram `D'`. Assume that the label of `g'` fixes the constants of `A'`,
and that every wall of `g'` has a wall of `g` whose normal `ν` satisfies
`ν'(ρ'(τ p)) = ν(ρ p)` for all `p ∈ Q`, where `ν'` is the normal of the wall of `g'`. Then the
image `Φ(u)` of a wall function `u` of `g` is a wall function of `g'`. -/
theorem IsWallFunction.of_intertwining {g : κ} {u : F.completionˣ}
    (hu : G.IsWallFunction σ g u) (G' : D'.FunctionWallGrouping π' κ') (g' : κ')
    (Φ : F.completion →+* F'.completion) (τ : Q → Q') (hτ : Function.Surjective τ)
    (hmono : ∀ p : Q, Φ (F.toCompletion (single p 1)) = F'.toCompletion (single (τ p) 1))
    (hΦ : ∀ x, Φ (σ (G.label g) x) = σ' (G'.label g') (Φ x))
    (hconst : ∀ c : A',
      σ' (G'.label g') (F'.toCompletion (single 0 c)) = F'.toCompletion (single 0 c))
    (hwall : ∀ j', G'.group j' = g' → ∃ j, G.group j = g ∧
      ∀ p : Q, (D'.wall j').normal (ρ' (τ p)) = (D.wall j).normal (ρ p)) :
    G'.IsWallFunction σ' g' (Units.map Φ.toMonoidHom u) := by
  refine (G'.isWallFunction_iff σ' g' _).mpr fun j' hj' => ?_
  obtain ⟨j, hj, hν⟩ := hwall j' hj'
  obtain ⟨⟨p, hp, hunit⟩, hact⟩ := (G.isWallFunction_iff σ g u).mp hu j hj
  refine ⟨⟨τ p, by rw [hν, hp], ?_⟩, fun p' c => ?_⟩
  · rw [← hmono]
    exact hunit.map Φ
  · obtain ⟨q, rfl⟩ := hτ p'
    rw [AlgFiltration.toCompletion_single_eq_mul, map_mul, hconst, ← hmono, ← hΦ, hact q 1, hν,
      ← map_zpow, Units.coe_map]
    simp [mul_assoc]

variable {G} {S : Subsemiring (AddMonoidAlgebra A Q)} {S' : Subsemiring (AddMonoidAlgebra A' Q')}

/-- **Transfer of positivity.** Let `G'` be a grouping of another diagram `D'` with the same
index type of groups, and `φ` a positive specialization of completed coefficients. If the
completion map of `φ` sends every wall function of a group `g` of `G` to a wall function of the
group `g` of `G'`, then `G'` is positive for `S'` whenever `G` is positive for `S`. -/
theorem IsPositive.of_isWallFunction_completionMap (G' : D'.FunctionWallGrouping π' κ)
    (φ : PositiveSpecialization F F' S S')
    (hwf : ∀ (g : κ) (u : F.completionˣ), G.IsWallFunction σ g u →
      G'.IsWallFunction σ' g (Units.map φ.completionMap.toMonoidHom u))
    (hG : G.IsPositive σ S) : G'.IsPositive σ' S' := by
  refine (G'.isPositive_iff σ' S').mpr fun g => ?_
  obtain ⟨u, hu, hpos⟩ := (G.isPositive_iff σ S).mp hG g
  exact ⟨_, hwf g u hu, φ.map_isPositive hpos⟩

end Transfer

end FunctionWallGrouping

section WallFunction

variable {A : Type*} [CommRing A] [Algebra R A]
  {Q : AddSubmonoid Γ} {F : AlgFiltration (AddMonoidAlgebra A Q)}
  (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))
  (P : Subsemiring (AddMonoidAlgebra A Q)) (π : Γ →+ M)

/-- A positive wall representative: a directed diagram admitting a function-wall grouping
all of whose wall functions are positive for `P`, for the coefficient action `σ` and
fixed spatial projection `π`. -/
def IsPositiveWallRepresentative : Prop :=
  ∃ (κ : Type u) (G : D.FunctionWallGrouping π κ), G.IsPositive σ P

/-- The defining condition of a positive wall representative. -/
theorem isPositiveWallRepresentative_iff :
    D.IsPositiveWallRepresentative σ P π ↔
      ∃ (κ : Type u) (G : D.FunctionWallGrouping π κ), G.IsPositive σ P :=
  Iff.rfl

/-- A positive grouping, indexed by a type in any universe, makes the diagram a positive
wall representative. -/
theorem FunctionWallGrouping.IsPositive.isPositiveWallRepresentative {κ : Type*}
    {G : D.FunctionWallGrouping π κ} (hG : G.IsPositive σ P) :
    D.IsPositiveWallRepresentative σ P π :=
  ⟨Set ι, G.toSet, hG.toSet⟩

end WallFunction

end DirectedDiagram

end Mei
