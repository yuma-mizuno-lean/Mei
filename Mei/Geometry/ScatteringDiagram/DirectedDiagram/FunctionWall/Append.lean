/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall

/-!
# Function-wall groupings of adjoined wall families

Let `D` and `E` be directed diagrams with the same positive degrees, wall spaces and spatial
lattice, and let `G₁` and `G₂` be groupings of their walls into function walls for one
spatial projection `π`. The union `D.append E` (`DirectedDiagram.append`) has the grouping
`G₁.append G₂`, indexed by the disjoint union of the two index types of groups
(`DirectedDiagram.FunctionWallGrouping.append`): a wall of `D` stays in its group of `G₁`, and a
wall of `E` stays in its group of `G₂`. Distinct groups may share a support, so no condition on
the supports of the two families is needed.

The completed label of a group is unchanged (`FunctionWallGrouping.label_append_inl`,
`FunctionWallGrouping.label_append_inr`), hence so are its wall functions
(`FunctionWallGrouping.isWallFunction_append_inl_iff`,
`FunctionWallGrouping.isWallFunction_append_inr_iff`), and the union of positive groupings is
positive (`FunctionWallGrouping.IsPositive.append`).
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

open _root_.AddMonoidAlgebra

universe w

variable {Γ Λ R V M ι κ : Type*} {L : Type w} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup M]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h H ι} {E : DirectedDiagram (d := d) h H κ}
  {π : Γ →+ M} {κ₁ κ₂ : Type*}

namespace FunctionWallGrouping

variable (G₁ : D.FunctionWallGrouping π κ₁) (G₂ : E.FunctionWallGrouping π κ₂)

/-- The grouping of the union of two families: each wall keeps its group, and the groups of the
two families are distinct. -/
def append : (D.append E).FunctionWallGrouping π (κ₁ ⊕ κ₂) where
  group := Sum.map G₁.group G₂.group
  support_eq {j j'} hj := by
    rcases j with j | j <;> rcases j' with j' | j' <;> simp only [Sum.map_inl, Sum.map_inr,
      reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at hj
    exacts [by simpa only [append_wall_inl] using G₁.support_eq hj,
      by simpa only [append_wall_inr] using G₂.support_eq hj]
  normal_eq {j j'} hj := by
    rcases j with j | j <;> rcases j' with j' | j' <;> simp only [Sum.map_inl, Sum.map_inr,
      reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at hj
    exacts [by simpa only [append_wall_inl] using G₁.normal_eq hj,
      by simpa only [append_wall_inr] using G₂.normal_eq hj]
  projectedDirection_eq {j j'} hj hl hl' := by
    rcases j with j | j <;> rcases j' with j' | j' <;> simp only [Sum.map_inl, Sum.map_inr,
      reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at hj
    · simp only [append_wall_inl] at hl hl' ⊢
      exact G₁.projectedDirection_eq hj hl hl'
    · simp only [append_wall_inr] at hl hl' ⊢
      exact G₂.projectedDirection_eq hj hl hl'
  isPrimitive_normal j := by
    rcases j with j | j
    exacts [by simpa only [append_wall_inl] using G₁.isPrimitive_normal j,
      by simpa only [append_wall_inr] using G₂.isPrimitive_normal j]

@[simp]
theorem append_group_inl (j : ι) : (G₁.append G₂).group (.inl j) = .inl (G₁.group j) := (rfl)

@[simp]
theorem append_group_inr (j : κ) : (G₁.append G₂).group (.inr j) = .inr (G₂.group j) := (rfl)

/-- The order-`k` label of a group of the first family is unchanged in the union. -/
@[simp]
theorem groupLabel_append_inl (g : κ₁) (k : ℕ) :
    (G₁.append G₂).groupLabel (.inl g) k = G₁.groupLabel g k := by
  classical
  let s : Finset ι := (Set.toFinite (D.active k)).toFinset.filter fun j => G₁.group j = g
  have hs : ∀ j ∈ s, G₁.group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hact : ∀ j ∈ D.active k, G₁.group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite (D.active k)).mem_toFinset.mpr hj, hg⟩
  rw [G₁.groupLabel_eq_noncommProd g k s hs hact,
    (G₁.append G₂).groupLabel_eq_noncommProd (.inl g) k (s.map Function.Embedding.inl)
      (fun j hj => by
        obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
        simp [hs j' hj'])
      (fun j hj hg => by
        rcases j with j | j
        · rw [active_append] at hj
          simp only [Set.mem_union, Set.mem_image, reduceCtorEq, and_false, exists_false,
            or_false, Sum.inl.injEq, exists_eq_right] at hj
          exact Finset.mem_map.mpr ⟨j, hact j hj (by simpa using hg), rfl⟩
        · simp at hg)]
  exact (Finset.noncommProd_map s Function.Embedding.inl _ _).trans
    (Finset.noncommProd_congr rfl (fun j _ => congrArg (fun W => CompletedGroup.projection k
      W.label) (append_wall_inl D E j)) _)

/-- The order-`k` label of a group of the second family is unchanged in the union. -/
@[simp]
theorem groupLabel_append_inr (g : κ₂) (k : ℕ) :
    (G₁.append G₂).groupLabel (.inr g) k = G₂.groupLabel g k := by
  classical
  let s : Finset κ := (Set.toFinite (E.active k)).toFinset.filter fun j => G₂.group j = g
  have hs : ∀ j ∈ s, G₂.group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hact : ∀ j ∈ E.active k, G₂.group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite (E.active k)).mem_toFinset.mpr hj, hg⟩
  rw [G₂.groupLabel_eq_noncommProd g k s hs hact,
    (G₁.append G₂).groupLabel_eq_noncommProd (.inr g) k (s.map Function.Embedding.inr)
      (fun j hj => by
        obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
        simp [hs j' hj'])
      (fun j hj hg => by
        rcases j with j | j
        · simp at hg
        · rw [active_append] at hj
          simp only [Set.mem_union, Set.mem_image, reduceCtorEq, and_false, exists_false,
            false_or, Sum.inr.injEq, exists_eq_right] at hj
          exact Finset.mem_map.mpr ⟨j, hact j hj (by simpa using hg), rfl⟩)]
  exact (Finset.noncommProd_map s Function.Embedding.inr _ _).trans
    (Finset.noncommProd_congr rfl (fun j _ => congrArg (fun W => CompletedGroup.projection k
      W.label) (append_wall_inr D E j)) _)

/-- The completed label of a group of the first family is unchanged in the union. -/
@[simp]
theorem label_append_inl (g : κ₁) : (G₁.append G₂).label (.inl g) = G₁.label g :=
  (((G₁.append G₂).eq_label_iff (.inl g) _).mpr fun k => by
    rw [G₁.projection_label, G₁.groupLabel_append_inl G₂]).symm

/-- The completed label of a group of the second family is unchanged in the union. -/
@[simp]
theorem label_append_inr (g : κ₂) : (G₁.append G₂).label (.inr g) = G₂.label g :=
  (((G₁.append G₂).eq_label_iff (.inr g) _).mpr fun k => by
    rw [G₂.projection_label, G₁.groupLabel_append_inr G₂]).symm

variable {A : Type*} [CommRing A] [Algebra R A] {Q : AddSubmonoid Γ}
  {F : AlgFiltration (AddMonoidAlgebra A Q)}
  (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))

/-- A unit is a wall function of a group of the first family in the union exactly when it is one
in the first family. -/
@[simp]
theorem isWallFunction_append_inl_iff (g : κ₁) (f : F.completionˣ) :
    (G₁.append G₂).IsWallFunction σ (.inl g) f ↔ G₁.IsWallFunction σ g f := by
  rw [isWallFunction_iff, isWallFunction_iff]
  refine ⟨fun hf j hj => ?_, fun hf j hj => ?_⟩
  · simpa using hf (.inl j) (by simpa using hj)
  · rcases j with j | j
    · simpa using hf j (by simpa using hj)
    · simp at hj

/-- A unit is a wall function of a group of the second family in the union exactly when it is one
in the second family. -/
@[simp]
theorem isWallFunction_append_inr_iff (g : κ₂) (f : F.completionˣ) :
    (G₁.append G₂).IsWallFunction σ (.inr g) f ↔ G₂.IsWallFunction σ g f := by
  rw [isWallFunction_iff, isWallFunction_iff]
  refine ⟨fun hf j hj => ?_, fun hf j hj => ?_⟩
  · simpa using hf (.inr j) (by simpa using hj)
  · rcases j with j | j
    · simp at hj
    · simpa using hf j (by simpa using hj)

variable (P : Subsemiring (AddMonoidAlgebra A Q))

variable {σ P} in
/-- The union of positive groupings is positive. -/
theorem IsPositive.append {G₁ : D.FunctionWallGrouping π κ₁} {G₂ : E.FunctionWallGrouping π κ₂}
    (hG₁ : G₁.IsPositive σ P) (hG₂ : G₂.IsPositive σ P) : (G₁.append G₂).IsPositive σ P := by
  refine ((G₁.append G₂).isPositive_iff σ P).mpr ?_
  rintro (g | g)
  · obtain ⟨f, hf, hfP⟩ := (G₁.isPositive_iff σ P).mp hG₁ g
    exact ⟨f, (G₁.isWallFunction_append_inl_iff G₂ σ g f).mpr hf, hfP⟩
  · obtain ⟨f, hf, hfP⟩ := (G₂.isPositive_iff σ P).mp hG₂ g
    exact ⟨f, (G₁.isWallFunction_append_inr_iff G₂ σ g f).mpr hf, hfP⟩

end FunctionWallGrouping

end Mei.DirectedDiagram
