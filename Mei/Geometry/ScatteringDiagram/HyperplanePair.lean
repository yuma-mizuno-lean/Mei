/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.HyperplanePair
public import Mei.Geometry.ScatteringDiagram.Refinement.Basic

/-!
# Wall diagrams on one and on two hyperplanes

The diagram `hyperplaneDiagram f a` labels the unique wall `ker f` of
`hyperplaneComplex f` by `a`, cooriented by `f`. On the finer complex
`hyperplanePairComplex f g`, the diagram `hyperplanePairDiagram f g a` labels the walls
inside `ker f` by `a`, cooriented by `f`, and the remaining walls, which lie in `ker g`, by
`1`, cooriented by `g`. It is a compatible refinement of the first diagram
(`isCompatibleRefinement_hyperplanePairDiagram`): a second hyperplane carrying the trivial
label does not change the path product along any path admissible for both complexes
(`FiniteWallDiagram.IsCompatibleRefinement.pathProduct_eq`).
-/

public section

open Set Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {f g : V →L[ℝ] ℝ}
  (hf : Toric.IsRationalFunctional h f.toLinearMap)
  (hg : Toric.IsRationalFunctional h g.toLinearMap) {H K : Type*}

/-- The diagram whose only wall, the hyperplane `ker f`, carries `a` and is cooriented
by `f`. -/
noncomputable def hyperplaneDiagram (hf0 : f ≠ 0) (a : H) :
    FiniteWallDiagram (FinitePolyhedralComplex.hyperplaneComplex f hf) H where
  normal _ := f.toLinearMap
  ker_normal P := by
    let := h.finiteDimensional
    have hP := FinitePolyhedralComplex.eq_ker_of_mem_hyperplaneComplex_walls hf P.property
    exact f.toLinearMap.ker_eq_direction_affineSpan (by exact_mod_cast hf0)
      (fun x hx => by simpa [hP] using hx)
      ((FinitePolyhedralComplex.hyperplaneComplex f hf).finrank_direction_add_one_of_mem_walls
        P.property)
  label _ := a

/-- The wall of the hyperplane diagram is cooriented by `f`. -/
@[simp]
theorem hyperplaneDiagram_normal (hf0 : f ≠ 0) (a : H)
    (P : (FinitePolyhedralComplex.hyperplaneComplex f hf).walls) :
    (hyperplaneDiagram hf hf0 a).normal P = f.toLinearMap := (rfl)

/-- The wall of the hyperplane diagram carries `a`. -/
@[simp]
theorem hyperplaneDiagram_label (hf0 : f ≠ 0) (a : H)
    (P : (FinitePolyhedralComplex.hyperplaneComplex f hf).walls) :
    (hyperplaneDiagram hf hf0 a).label P = a := (rfl)

open scoped Classical in
/-- The diagram on the two hyperplanes `ker f` and `ker g` whose walls inside `ker f` carry
`a` and are cooriented by `f`, and whose other walls carry `1` and are cooriented by `g`. -/
noncomputable def hyperplanePairDiagram [One H] (hf0 : f ≠ 0) (hg0 : g ≠ 0) (a : H) :
    FiniteWallDiagram (FinitePolyhedralComplex.hyperplanePairComplex f g hf hg) H where
  normal Q := if (Q : Set V) ⊆ {θ | f θ = 0} then f.toLinearMap else g.toLinearMap
  ker_normal Q := by
    let := h.finiteDimensional
    have hd := (FinitePolyhedralComplex.hyperplanePairComplex f g hf hg)
      |>.finrank_direction_add_one_of_mem_walls Q.property
    by_cases hQ : (Q : Set V) ⊆ {θ | f θ = 0}
    · simp only [hQ, ↓reduceIte]
      exact f.toLinearMap.ker_eq_direction_affineSpan (by exact_mod_cast hf0)
        (fun x hx => hQ hx) hd
    · simp only [hQ, ↓reduceIte]
      have hQg := (FinitePolyhedralComplex.exists_subset_ker_of_mem_hyperplanePairComplex_walls
        hf hg Q.property).resolve_left hQ
      exact g.toLinearMap.ker_eq_direction_affineSpan (by exact_mod_cast hg0)
        (fun x hx => hQg hx) hd
  label Q := if (Q : Set V) ⊆ {θ | f θ = 0} then a else 1

section One

variable [One H] (hf0 : f ≠ 0) (hg0 : g ≠ 0) (a : H)

/-- A wall of the pair inside `ker f` is cooriented by `f`. -/
@[simp]
theorem hyperplanePairDiagram_normal_of_subset
    {Q : (FinitePolyhedralComplex.hyperplanePairComplex f g hf hg).walls}
    (hQ : (Q : Set V) ⊆ {θ | f θ = 0}) :
    (hyperplanePairDiagram hf hg hf0 hg0 a).normal Q = f.toLinearMap := by
  classical
  simp [hyperplanePairDiagram, hQ]

/-- A wall of the pair not inside `ker f` is cooriented by `g`. -/
@[simp]
theorem hyperplanePairDiagram_normal_of_not_subset
    {Q : (FinitePolyhedralComplex.hyperplanePairComplex f g hf hg).walls}
    (hQ : ¬(Q : Set V) ⊆ {θ | f θ = 0}) :
    (hyperplanePairDiagram hf hg hf0 hg0 a).normal Q = g.toLinearMap := by
  classical
  simp [hyperplanePairDiagram, hQ]

/-- A wall of the pair inside `ker f` carries `a`. -/
@[simp]
theorem hyperplanePairDiagram_label_of_subset
    {Q : (FinitePolyhedralComplex.hyperplanePairComplex f g hf hg).walls}
    (hQ : (Q : Set V) ⊆ {θ | f θ = 0}) :
    (hyperplanePairDiagram hf hg hf0 hg0 a).label Q = a := by
  classical
  simp [hyperplanePairDiagram, hQ]

/-- A wall of the pair not inside `ker f` carries the identity. -/
@[simp]
theorem hyperplanePairDiagram_label_of_not_subset
    {Q : (FinitePolyhedralComplex.hyperplanePairComplex f g hf hg).walls}
    (hQ : ¬(Q : Set V) ⊆ {θ | f θ = 0}) :
    (hyperplanePairDiagram hf hg hf0 hg0 a).label Q = 1 := by
  classical
  simp [hyperplanePairDiagram, hQ]

end One

variable [Group H] [Group K] (hf0 : f ≠ 0) (hg0 : g ≠ 0) (a : H)

/-- Relabelling the one-hyperplane diagram relabels its wall. -/
@[simp]
theorem relabel_hyperplaneDiagram (φ : H →* K) :
    (hyperplaneDiagram hf hf0 a).relabel φ = hyperplaneDiagram hf hf0 (φ a) :=
  FiniteWallDiagram.ext (funext fun P => by simp) (funext fun P => by simp)

/-- Relabelling the two-hyperplane diagram relabels its label `a`. -/
@[simp]
theorem relabel_hyperplanePairDiagram (φ : H →* K) :
    (hyperplanePairDiagram hf hg hf0 hg0 a).relabel φ =
      hyperplanePairDiagram hf hg hf0 hg0 (φ a) := by
  refine FiniteWallDiagram.ext (funext fun Q => ?_) (funext fun Q => ?_)
  · by_cases hQ : (Q : Set V) ⊆ {θ | f θ = 0}
    · simp [hyperplanePairDiagram_normal_of_subset hf hg hf0 hg0 _ hQ]
    · simp only [relabel_normal, hyperplanePairDiagram_normal_of_not_subset hf hg hf0 hg0 _ hQ]
  · by_cases hQ : (Q : Set V) ⊆ {θ | f θ = 0}
    · simp [hyperplanePairDiagram_label_of_subset hf hg hf0 hg0 _ hQ]
    · simp [hyperplanePairDiagram_label_of_not_subset hf hg hf0 hg0 _ hQ]

/-- A second hyperplane with the trivial label refines the diagram of the first one. -/
theorem isCompatibleRefinement_hyperplanePairDiagram :
    (hyperplanePairDiagram hf hg hf0 hg0 a).IsCompatibleRefinement
      (hyperplaneDiagram hf hf0 a) where
  isSubdivision := FinitePolyhedralComplex.isSubdivision_hyperplanePairComplex hf hg
  exists_pos_normal_eq_smul Q P hQP := by
    have hP := FinitePolyhedralComplex.eq_ker_of_mem_hyperplaneComplex_walls hf P.property
    exact ⟨1, one_pos, by simp [hyperplanePairDiagram_normal_of_subset hf hg hf0 hg0 a
      (hP ▸ hQP)]⟩
  label_eq_of_subset Q P hQP := by
    have hP := FinitePolyhedralComplex.eq_ker_of_mem_hyperplaneComplex_walls hf P.property
    simp [hyperplanePairDiagram_label_of_subset hf hg hf0 hg0 a (hP ▸ hQP)]
  label_eq_one Q hQ := by
    apply hyperplanePairDiagram_label_of_not_subset hf hg hf0 hg0 a
    intro hQf
    exact hQ ⟨_, (FinitePolyhedralComplex.mem_hyperplaneComplex_walls_iff hf hf0).mpr rfl⟩ hQf

end Mei.FiniteWallDiagram
