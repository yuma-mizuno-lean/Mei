/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence
public import Mei.Geometry.Convex.Polyhedron.Path.Refinement

/-!
# Refinements of directed diagrams

A refinement `E` of a directed diagram `D` assigns each nonidentity wall of `E` to a wall
of `D` with the same supported ray, normal and label whose support contains it. Each
nonidentity support of `D` is covered by the supports assigned to it, and these have
pairwise disjoint relative interiors. Repeated and overlapping indexed walls of `D` are
refined separately, and identity-labelled walls of `E` need no assignment.

A refinement is equivalent to the diagram it refines: at every cutoff, a path admissible
for both active wall families crosses the same walls at the same times, and each
simultaneous crossing has the same combined label. Hence directed equivalence does not
depend on the wall presentation.

Equivalence is the path-ordered-product equivalence of directed scattering diagrams in
Travis Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), §2. The comparison of products
is `Quiver.Path.wallPathProduct_eq_of_refines`, applied to the active walls.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

/-- A refinement `E` of `D`: every nonidentity wall of `E` is assigned to a wall of `D` with
the same ray, normal and label containing its support, and every nonidentity support of `D`
is covered by its assigned supports, with pairwise disjoint relative interiors. -/
@[ext]
structure Refinement (D : DirectedDiagram (d := d) h H ι)
    (E : DirectedDiagram (d := d) h H κ) where
  /-- The wall of `D` containing a nonidentity wall of `E`. -/
  assign : {j : κ // (E.wall j).label ≠ 1} → ι
  /-- Assigned walls have the same supported ray. -/
  ray_eq : ∀ j, (E.wall j.val).ray = (D.wall (assign j)).ray
  /-- Assigned walls have the same normal. -/
  normal_eq : ∀ j, (E.wall j.val).normal = (D.wall (assign j)).normal
  /-- Assigned walls have the same label. -/
  label_eq : ∀ j, (E.wall j.val).label = (D.wall (assign j)).label
  /-- An assigned wall contains the refined support. -/
  support_subset : ∀ j, (E.wall j.val).support ⊆ (D.wall (assign j)).support
  /-- Every nonidentity support is covered by the supports assigned to it. -/
  support_subset_iUnion : ∀ a, (D.wall a).label ≠ 1 →
    (D.wall a).support ⊆ ⋃ j ∈ assign ⁻¹' {a}, (E.wall j.val).support
  /-- Supports assigned to one wall have pairwise disjoint relative interiors. -/
  pairwiseDisjoint_intrinsicInterior : ∀ a,
    (assign ⁻¹' {a}).PairwiseDisjoint fun j => intrinsicInterior ℝ (E.wall j.val).support

namespace Refinement

variable {D : DirectedDiagram (d := d) h H ι} {E : DirectedDiagram (d := d) h H κ}
  (r : D.Refinement E)

/-- Every directed diagram refines itself by the identity assignment. -/
def refl (D : DirectedDiagram (d := d) h H ι) : D.Refinement D where
  assign := Subtype.val
  ray_eq _ := rfl
  normal_eq _ := rfl
  label_eq _ := rfl
  support_subset _ := subset_rfl
  support_subset_iUnion a ha z hz := mem_iUnion₂.mpr ⟨⟨a, ha⟩, rfl, hz⟩
  pairwiseDisjoint_intrinsicInterior a := by
    intro j₁ hj₁ j₂ hj₂ hne
    exact (hne (Subtype.ext (hj₁.trans hj₂.symm))).elim

@[simp]
theorem refl_assign (D : DirectedDiagram (d := d) h H ι) (j : {j : ι // (D.wall j).label ≠ 1}) :
    (refl D).assign j = j.val := (rfl)

/-- The assignment on walls active at order `k`. -/
private def activeAssign (k : ℕ) (j : E.active k) : D.active k :=
  ⟨r.assign ⟨j.val, E.label_ne_one_of_mem_active j.property⟩, by
    rw [mem_active, ← r.label_eq]
    exact (E.mem_active k j.val).mp j.property⟩

private theorem activeAssign_val (k : ℕ) (j : E.active k) :
    (r.activeAssign k j).val = r.assign ⟨j.val, E.label_ne_one_of_mem_active j.property⟩ := (rfl)

include r in
/-- At every cutoff, a refinement and the diagram it refines have equal products along
every path admissible for both active wall families. -/
theorem levelPathProduct_eq (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement (fun j : E.active k => (E.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    D.levelPathProduct k p = E.levelPathProduct k q := by
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k),
    E.levelPathProduct_eq_wallPathProduct k q (E.activeLabels_commute k)]
  symm
  refine Quiver.Path.wallPathProduct_eq_of_refines _ _ (D.activeLabels_commute k) _ _
    (E.activeLabels_commute k) (f := r.activeAssign k) (fun j => ?_) (fun a => ?_)
    (fun a => ?_) (fun j => ?_) (fun j => ?_) p q hpq.symm
  · rw [activeAssign_val]
    exact r.support_subset ⟨j.val, E.label_ne_one_of_mem_active j.property⟩
  · intro z hz
    have ha : (D.wall a.val).label ≠ 1 := D.label_ne_one_of_mem_active a.property
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (r.support_subset_iUnion a.val ha hz)
    have hj' : r.assign j = a.val := by simpa using hj
    have hact : j.val ∈ E.active k := by
      rw [mem_active, r.label_eq, hj']
      exact (D.mem_active k a.val).mp a.property
    refine mem_iUnion₂.mpr ⟨⟨j.val, hact⟩, ?_, hzj⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subtype.ext ((activeAssign_val r k _).trans hj')
  · intro j₁ hj₁ j₂ hj₂ hne
    have hmem (j : E.active k) (hj : j ∈ r.activeAssign k ⁻¹' {a}) :
        (⟨j.val, E.label_ne_one_of_mem_active j.property⟩ : {j : κ // (E.wall j).label ≠ 1}) ∈
          r.assign ⁻¹' {a.val} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← activeAssign_val,
        (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hj))]
    exact r.pairwiseDisjoint_intrinsicInterior a.val (hmem j₁ hj₁) (hmem j₂ hj₂)
      fun he => hne (Subtype.ext (Subtype.mk.inj he))
  · rw [activeAssign_val, ← r.normal_eq]
  · rw [activeAssign_val, ← r.label_eq]

include r in
/-- A refinement agrees with the refined diagram at every cutoff. -/
theorem levelEquivalent (k : ℕ) : D.LevelEquivalent E k :=
  (levelEquivalent_def D E k).mpr fun _ _ _ _ p q hpq => r.levelPathProduct_eq k p q hpq

include r in
/-- A refinement is equivalent to the diagram it refines. -/
theorem equivalent : D.Equivalent E := (equivalent_iff D E).mpr r.levelEquivalent

end Refinement
end Mei.DirectedDiagram
