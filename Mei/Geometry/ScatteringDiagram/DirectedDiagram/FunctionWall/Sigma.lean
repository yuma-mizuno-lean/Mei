/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Sigma
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall

/-!
# Function-wall groupings of unions of finitely many wall families

Let `D b`, for `b` in a finite type `β`, be directed diagrams with the same positive degrees, wall
spaces and spatial lattice, and let `G b` be groupings of their walls into function walls for one
spatial projection `π`. The union `DirectedDiagram.sigma D` has the grouping
`FunctionWallGrouping.sigma G`, indexed by the pairs `(b, g)` of a family and a group of its
grouping: a wall of `D b` stays in its group of `G b`. Distinct groups may share a support, so no
condition on the supports of distinct families is needed.

The completed label of a group is unchanged (`FunctionWallGrouping.label_sigma`), hence so are its
wall functions (`FunctionWallGrouping.isWallFunction_sigma_iff`), and the union of positive
groupings is positive (`FunctionWallGrouping.IsPositive.sigma`). For two families these are the
statements of `FunctionWallGrouping.append`.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

open _root_.AddMonoidAlgebra

variable {Γ Λ R V M β : Type*} {L : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup M]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} [Finite β] {ι : β → Type*}
  {D : ∀ b, DirectedDiagram (d := d) h H (ι b)} {π : Γ →+ M} {κ : β → Type*}

namespace FunctionWallGrouping

variable (G : ∀ b, (D b).FunctionWallGrouping π (κ b))

/-- The grouping of the union of finitely many families: each wall keeps its group, and the groups
of distinct families are distinct. -/
def sigma : (DirectedDiagram.sigma D).FunctionWallGrouping π (Σ b, κ b) where
  group x := ⟨x.1, (G x.1).group x.2⟩
  support_eq {x x'} hx := by
    obtain ⟨b, j⟩ := x
    obtain ⟨b', j'⟩ := x'
    obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.mp hx
    simpa only [sigma_wall] using (G b).support_eq (eq_of_heq hj)
  normal_eq {x x'} hx := by
    obtain ⟨b, j⟩ := x
    obtain ⟨b', j'⟩ := x'
    obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.mp hx
    simpa only [sigma_wall] using (G b).normal_eq (eq_of_heq hj)
  projectedDirection_eq {x x'} hx hl hl' := by
    obtain ⟨b, j⟩ := x
    obtain ⟨b', j'⟩ := x'
    obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.mp hx
    simp only [sigma_wall] at hl hl' ⊢
    exact (G b).projectedDirection_eq (eq_of_heq hj) hl hl'
  isPrimitive_normal x := by
    obtain ⟨b, j⟩ := x
    simpa only [sigma_wall] using (G b).isPrimitive_normal j

@[simp]
theorem sigma_group (b : β) (j : ι b) : (sigma G).group ⟨b, j⟩ = ⟨b, (G b).group j⟩ := (rfl)

/-- The order-`k` label of a group of the family `b` is unchanged in the union. -/
@[simp]
theorem groupLabel_sigma (b : β) (g : κ b) (k : ℕ) :
    (sigma G).groupLabel ⟨b, g⟩ k = (G b).groupLabel g k := by
  classical
  let s : Finset (ι b) := (Set.toFinite ((D b).active k)).toFinset.filter fun j => (G b).group j = g
  have hs : ∀ j ∈ s, (G b).group j = g := fun j hj => (Finset.mem_filter.mp hj).2
  have hact : ∀ j ∈ (D b).active k, (G b).group j = g → j ∈ s := fun j hj hg =>
    Finset.mem_filter.mpr ⟨(Set.toFinite ((D b).active k)).mem_toFinset.mpr hj, hg⟩
  rw [(G b).groupLabel_eq_noncommProd g k s hs hact,
    (sigma G).groupLabel_eq_noncommProd ⟨b, g⟩ k (s.map (Function.Embedding.sigmaMk b))
      (fun x hx => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
        simp [hs j hj])
      (fun x hx hg => by
        obtain ⟨b', j⟩ := x
        rw [sigma_group] at hg
        obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.mp hg
        exact Finset.mem_map.mpr ⟨j, hact j (by simpa only [mem_active, sigma_wall] using hx)
          (eq_of_heq hj), rfl⟩)]
  exact (Finset.noncommProd_map s _ _ _).trans
    (Finset.noncommProd_congr rfl (fun j _ => by rw [Function.Embedding.sigmaMk_apply,
      sigma_wall]) _)

/-- The completed label of a group of the family `b` is unchanged in the union. -/
@[simp]
theorem label_sigma (b : β) (g : κ b) : (sigma G).label ⟨b, g⟩ = (G b).label g :=
  (((sigma G).eq_label_iff ⟨b, g⟩ _).mpr fun k => by
    rw [(G b).projection_label, groupLabel_sigma]).symm

variable {A : Type*} [CommRing A] [Algebra R A] {Q : AddSubmonoid Γ}
  {F : AlgFiltration (AddMonoidAlgebra A Q)}
  (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))

/-- A unit is a wall function of a group of the family `b` in the union exactly when it is one in
the family `b`. -/
@[simp]
theorem isWallFunction_sigma_iff (b : β) (g : κ b) (f : F.completionˣ) :
    (sigma G).IsWallFunction σ ⟨b, g⟩ f ↔ (G b).IsWallFunction σ g f := by
  rw [isWallFunction_iff, isWallFunction_iff]
  refine ⟨fun hf j hj => ?_, fun hf x hx => ?_⟩
  · simpa using hf ⟨b, j⟩ (by rw [sigma_group, hj])
  · obtain ⟨b', j⟩ := x
    rw [sigma_group] at hx
    obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.mp hx
    simpa using hf j (eq_of_heq hj)

variable {σ} in
/-- The union of finitely many positive groupings is positive. -/
theorem IsPositive.sigma {P : Subsemiring (AddMonoidAlgebra A Q)}
    {G : ∀ b, (D b).FunctionWallGrouping π (κ b)} (hG : ∀ b, (G b).IsPositive σ P) :
    (FunctionWallGrouping.sigma G).IsPositive σ P := by
  refine ((FunctionWallGrouping.sigma G).isPositive_iff σ P).mpr fun ⟨b, g⟩ => ?_
  obtain ⟨f, hf, hfP⟩ := ((G b).isPositive_iff σ P).mp (hG b) g
  exact ⟨f, (isWallFunction_sigma_iff G σ b g f).mpr hf, hfP⟩

end FunctionWallGrouping

end Mei.DirectedDiagram
