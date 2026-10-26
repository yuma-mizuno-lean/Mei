/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.Equivalence
public import Mei.Geometry.Convex.PolyhedralComplex.Subdivision

/-!
# Compatible refinements of finite wall diagrams

A compatible refinement of a diagram `D` lives on a subdivision of its complex. A new wall
contained in a wall of `D` carries that wall's label and a positively proportional
coorientation; every other new wall is labelled `1`. Such a refinement has the same product
as `D` on every polygonal path admissible for both wall families, so the two diagrams are
equivalent and have the same consistency behaviour. This lets a diagram be replaced by one
on any finer complex, for instance a common subdivision of several complexes.

Equivalence is the path-product comparison of diagrams on different cone complexes in
Tom Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416), §2. The comparison uses `Quiver.Path.crossingWord_coarsen` and Mathlib's universal property
`FreeGroup.lift_unique`; no perturbation of the path is required.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C C' : FinitePolyhedralComplex h} {H K : Type*} [Group H] [Group K]

/-- `E` is a compatible refinement of `D`: its complex subdivides that of `D`, each wall
contained in a wall of `D` carries that wall's label and a positive multiple of its
coorientation, and every other wall is labelled `1`. -/
structure IsCompatibleRefinement (E : FiniteWallDiagram C' H) (D : FiniteWallDiagram C H) :
    Prop where
  /-- The complex of `E` subdivides the complex of `D`. -/
  isSubdivision : C'.IsSubdivision C
  /-- A wall inside a wall of `D` has a positively proportional coorientation. -/
  exists_pos_normal_eq_smul : ∀ (Q : C'.walls) (P : C.walls), (Q : Set V) ⊆ P →
    ∃ c : ℝ, 0 < c ∧ E.normal Q = c • D.normal P
  /-- A wall inside a wall of `D` carries the label of that wall. -/
  label_eq_of_subset : ∀ (Q : C'.walls) (P : C.walls), (Q : Set V) ⊆ P → E.label Q = D.label P
  /-- A wall inside no wall of `D` carries the identity label. -/
  label_eq_one : ∀ Q : C'.walls, (∀ P : C.walls, ¬(Q : Set V) ⊆ P) → E.label Q = 1

namespace IsCompatibleRefinement

/-- Every diagram is a compatible refinement of itself. -/
@[refl]
theorem refl (D : FiniteWallDiagram C H) : D.IsCompatibleRefinement D where
  isSubdivision := FinitePolyhedralComplex.IsSubdivision.refl C
  exists_pos_normal_eq_smul Q P hQP := by
    obtain rfl : Q = P := Subtype.ext (FinitePolyhedralComplex.eq_of_subset_of_mem_walls
      Q.property Q.property P.property subset_rfl hQP)
    exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  label_eq_of_subset Q P hQP := by
    rw [Subtype.ext (FinitePolyhedralComplex.eq_of_subset_of_mem_walls
      Q.property Q.property P.property subset_rfl hQP)]
  label_eq_one Q hQ := (hQ Q subset_rfl).elim

variable {E : FiniteWallDiagram C' H} {D : FiniteWallDiagram C H}

/-- Relabelling both diagrams along a homomorphism preserves compatible refinement. -/
theorem relabel (hED : E.IsCompatibleRefinement D) (f : H →* K) :
    (E.relabel f).IsCompatibleRefinement (D.relabel f) where
  isSubdivision := hED.isSubdivision
  exists_pos_normal_eq_smul Q P hQP := by
    simpa only [relabel_normal] using hED.exists_pos_normal_eq_smul Q P hQP
  label_eq_of_subset Q P hQP := by
    simp only [relabel_label, hED.label_eq_of_subset Q P hQP]
  label_eq_one Q hQ := by simp only [relabel_label, hED.label_eq_one Q hQ, map_one]

/-- Evaluating the labels of `D` after coarsening a word evaluates the labels of `E`. -/
private theorem lift_label_wallCoarsening (hED : E.IsCompatibleRefinement D)
    (g : FreeGroup C'.walls) :
    FreeGroup.lift D.label (C'.wallCoarsening C E.normal D.normal g) =
      FreeGroup.lift E.label g := by
  apply FreeGroup.lift_unique ((FreeGroup.lift D.label).comp
    (C'.wallCoarsening C E.normal D.normal))
  intro Q
  rw [MonoidHom.comp_apply]
  by_cases hQ : ∃ P : C.walls, (Q : Set V) ⊆ P
  · obtain ⟨P, hQP⟩ := hQ
    rw [FinitePolyhedralComplex.wallCoarsening_of_of_subset _ _ hQP,
      ite_eq_left (hED.exists_pos_normal_eq_smul Q P hQP), FreeGroup.lift_apply_of,
      hED.label_eq_of_subset Q P hQP]
  · rw [FinitePolyhedralComplex.wallCoarsening_of_of_forall_not_subset _ _
      (not_exists.mp hQ), map_one, hED.label_eq_one Q (not_exists.mp hQ)]

/-- A compatible refinement has the same product on every polygonal path admissible for
both wall families. -/
theorem pathProduct_eq (hED : E.IsCompatibleRefinement D)
    {x y : WallComplement (fun P : C'.walls => (P : Set V))}
    {x' y' : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    E.pathProduct p = D.pathProduct q := by
  rw [pathProduct_def, pathProduct_def, Quiver.Path.crossingWord_coarsen hED.isSubdivision
    E.normal D.normal E.ker_normal D.ker_normal p q hpq, hED.lift_label_wallCoarsening]

/-- A compatible refinement is equivalent to the diagram it refines. -/
theorem equivalent (hED : E.IsCompatibleRefinement D) : E.Equivalent D :=
  (equivalent_def E D).mpr fun _ _ _ _ p q hpq => hED.pathProduct_eq p q hpq

/-- A compatible refinement is consistent exactly when the diagram it refines is. -/
theorem consistent_iff (hED : E.IsCompatibleRefinement D) : E.Consistent ↔ D.Consistent :=
  hED.equivalent.consistent_iff

end IsCompatibleRefinement

end Mei.FiniteWallDiagram
