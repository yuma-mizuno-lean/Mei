/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.HyperplanePair
public import Mei.Geometry.ScatteringDiagram.Refinement.Basic
public import Mei.Geometry.ScatteringDiagram.LocalProduct

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

The path products of the one-hyperplane diagram depend only on the sides of `ker f` containing
the endpoints: with the crossing factor `hyperplaneFactor f a v`, equal to `a⁻¹` on the positive
side `0 < f v` and to `1` elsewhere, an admissible path from `x` to `y` has the product
`hyperplaneFactor f a y * (hyperplaneFactor f a x)⁻¹` (`pathProduct_hyperplaneDiagram`). In
particular the diagram is consistent (`consistent_hyperplaneDiagram`).
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

/-- The crossing factor of the hyperplane `ker f` at `v`: the inverse of the label `a` on the
positive side `0 < f v`, and `1` elsewhere. A path of the one-hyperplane diagram from `x` to `y`
has the product `hyperplaneFactor f a y * (hyperplaneFactor f a x)⁻¹`. -/
noncomputable def hyperplaneFactor [Inv H] [One H] (f : V →L[ℝ] ℝ) (a : H) (v : V) : H :=
  if 0 < f v then a⁻¹ else 1

/-- The crossing factor is the inverse label on the positive side of the hyperplane. -/
theorem hyperplaneFactor_def [Inv H] [One H] (a : H) (v : V) :
    hyperplaneFactor f a v = if 0 < f v then a⁻¹ else 1 := (rfl)

/-- The crossing factor depends only on the side of the hyperplane. -/
theorem hyperplaneFactor_eq_of_sign_eq [Inv H] [One H] (a : H) {v w : V}
    (hvw : SignType.sign (f v) = SignType.sign (f w)) :
    hyperplaneFactor f a v = hyperplaneFactor f a w := by
  simp only [hyperplaneFactor_def, ← sign_eq_one_iff, hvw]

variable [Group H] [Group K] (hf0 : f ≠ 0) (hg0 : g ≠ 0) (a : H)

/-- The product of a segment of the one-hyperplane diagram is the quotient of the crossing factors
of its endpoints: crossing to the positive side contributes `a⁻¹`, crossing to the negative side
`a`, and a segment staying on one side has product `1`. -/
theorem pathProduct_hyperplaneDiagram_toPath
    {x y : WallComplement (fun P : (FinitePolyhedralComplex.hyperplaneComplex f hf).walls =>
      (P : Set V))} (e : x ⟶ y) :
    (hyperplaneDiagram hf hf0 a).pathProduct e.toPath =
      hyperplaneFactor f a y.val * (hyperplaneFactor f a x.val)⁻¹ := by
  have hx := FinitePolyhedralComplex.apply_val_ne_zero_of_hyperplaneComplex hf hf0 x
  have hy := FinitePolyhedralComplex.apply_val_ne_zero_of_hyperplaneComplex hf hf0 y
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · rw [pathProduct_toPath_eq_one _ _
      (FinitePolyhedralComplex.crossings_hyperplaneComplex_eq_empty (mul_pos_of_neg_of_neg hx hy))]
    simp [hyperplaneFactor_def, hx.not_gt, hy.not_gt]
  · rw [pathProduct_toPath_eq_of_crossings_eq_singleton _ _
      (FinitePolyhedralComplex.crossings_hyperplaneComplex_eq_singleton hf hf0
        (mul_neg_of_neg_of_pos hx hy))]
    simp [hyperplaneFactor_def, hx.not_gt, hy, sub_pos.mpr (hx.trans hy)]
  · rw [pathProduct_toPath_eq_of_crossings_eq_singleton _ _
      (FinitePolyhedralComplex.crossings_hyperplaneComplex_eq_singleton hf hf0
        (mul_neg_of_pos_of_neg hx hy))]
    simp [hyperplaneFactor_def, hx, hy.not_gt, (sub_neg.mpr (hy.trans hx)).not_gt]
  · rw [pathProduct_toPath_eq_one _ _
      (FinitePolyhedralComplex.crossings_hyperplaneComplex_eq_empty (mul_pos hx hy))]
    simp [hyperplaneFactor_def, hx, hy]

/-- Every admissible path of the one-hyperplane diagram has the quotient of the crossing factors
of its endpoints as its product. -/
theorem pathProduct_hyperplaneDiagram
    {x y : WallComplement (fun P : (FinitePolyhedralComplex.hyperplaneComplex f hf).walls =>
      (P : Set V))} (p : AdmissiblePLPath x y) :
    (hyperplaneDiagram hf hf0 a).pathProduct p =
      hyperplaneFactor f a y.val * (hyperplaneFactor f a x.val)⁻¹ := by
  refine (hyperplaneDiagram hf hf0 a).pathProduct_eq_mul_inv_of_local (fun θ hθ => ?_)
    (fun P θ _ _ => ⟨1, one_pos, fun x y e _ _ _ =>
      pathProduct_hyperplaneDiagram_toPath hf hf0 a e⟩) p
  -- off the wall, the side of `ker f` is locally constant
  have hθ0 : f θ ≠ 0 :=
    hθ ⟨_, (FinitePolyhedralComplex.mem_hyperplaneComplex_walls_iff hf hf0).mpr rfl⟩
  rcases hθ0.lt_or_gt with hθ0 | hθ0
  · filter_upwards [f.continuous.continuousAt.eventually (gt_mem_nhds hθ0)] with φ hφ
    simp [hyperplaneFactor_def, hφ.not_gt, hθ0.not_gt]
  · filter_upwards [f.continuous.continuousAt.eventually (lt_mem_nhds hθ0)] with φ hφ
    simp [hyperplaneFactor_def, hφ, hθ0]

/-- The one-hyperplane diagram is consistent, for every label. -/
theorem consistent_hyperplaneDiagram : (hyperplaneDiagram hf hf0 a).Consistent :=
  (hyperplaneDiagram hf hf0 a).consistent_def.mpr fun _ _ p q => by
    rw [pathProduct_hyperplaneDiagram, pathProduct_hyperplaneDiagram]

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
