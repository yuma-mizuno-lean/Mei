/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cylinder.Decorated

/-!
# Cutoff decorated rays through cylinder walls

Cylinder projection identifies the complete finite-cutoff decorated ray family,
over all encounter itineraries at once. Prescribing the forgotten endpoint and
its velocity for each degree determines a unique lift. The comparison retains
whole decorations and distinct degree histories, including encounters whose
projected bend vanishes, and commutes with finite weighted evaluation.

Wall supports, singular sets and the incoming source are pulled back from the
projected space. The complete paths, incoming tails and encounter parameters
are preserved by projection. Properness follows separately when the projected
incoming direction is nonzero. The coefficient grading is retained; grouping
histories after coefficient regrading is a separate comparison.

We use `cutoffDecoratedRayFiberEquiv` for finiteness of the ray family and
`decoratedRayCylinderEquiv` for each itinerary's geometric lifting and
preservation properties. The geometric lifting follows Carl–Pumperla–Siebert, *A tropical
view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2); the whole-component
convention follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V V' J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  (v : Γ → V) (w : Γ → V') (W : J → Set V) (S : K → Set V)
  (C : Set V) (Q : V × V')

local notation "vw" => fun p => (v p, w p)

variable [AddCommGroup Γ] (d : PositiveDegrees Γ)
  (U : J → Module.End R M) (b : ℳ 0)
  (g : J → V →L[ℝ] ℝ) (h : J → ℝ) (sign : J → SignType)
  (A : J → Set V) (k : ℕ)

local notation "G" => fun j => ContinuousLinearMap.comp (g j) (ContinuousLinearMap.fst ℝ V V')
local notation "Lifted" => CutoffDecoratedRay d ℳ U b vw G h sign
  (fun j => Prod.fst ⁻¹' A j) (fun j => Prod.fst ⁻¹' W j)
  (fun j => Prod.fst ⁻¹' S j) (Prod.fst ⁻¹' C) k Q
local notation "Projected" => CutoffDecoratedRay d ℳ U b v g h sign A W S C k (Prod.fst Q)

/-- Cylinder projection identifies the complete cutoff family, allowing arbitrary
finite encounter words. All recorded degrees and whole decorations are retained. -/
def cutoffDecoratedRayCylinderEquiv : Lifted ≃ Projected where
  toFun r := ⟨r.itinerary,
    decoratedRayCylinderEquiv ℳ (fun j => U (r.itinerary.get j)) 0 b v w
      (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
      (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
      W S C Q r.realization,
    by simpa only [decoratedRayCylinderEquiv_history] using r.degree_mem,
    by simpa only [decoratedRayCylinderEquiv_history] using r.degree_sub_mem⟩
  invFun r := by
    let e := decoratedRayCylinderEquiv ℳ (fun j => U (r.itinerary.get j)) 0 b v w
      (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
      (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
      W S C Q
    have hh := decoratedRayCylinderEquiv_history ℳ (fun j => U (r.itinerary.get j))
      0 b v w (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
      (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
      W S C Q (e.symm r.realization)
    rw [Equiv.apply_symm_apply] at hh
    exact ⟨r.itinerary, e.symm r.realization,
      by simpa only [← hh] using r.degree_mem,
      by simpa only [← hh] using r.degree_sub_mem⟩
  left_inv r := by
    apply CutoffDecoratedRay.ext
    · rfl
    exact heq_of_eq (Equiv.symm_apply_apply _ _)
  right_inv r := by
    apply CutoffDecoratedRay.ext
    · rfl
    exact heq_of_eq (Equiv.apply_symm_apply _ _)

/-- Projection keeps the full encounter itinerary. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_itinerary (r : Lifted) :
    (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).itinerary =
      r.itinerary := (rfl)

/-- Lifting keeps the full encounter itinerary. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_symm_itinerary (r : Projected) :
    ((cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k).symm r).itinerary =
      r.itinerary := (rfl)

/-- Projection keeps the degree history, even when projected velocities coincide. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_history (r : Lifted) :
    HEq (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).realization.1.val
      r.realization.1.val :=
  heq_of_eq (decoratedRayCylinderEquiv_history ℳ (fun j => U (r.itinerary.get j))
    0 b v w (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
    (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
    W S C Q r.realization)

/-- Whole final decorations are preserved across the complete cutoff family. -/
@[simp↓]
theorem cutoffDecoratedRayCylinderEquiv_decoration (r : Lifted) :
    (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).decoration =
      r.decoration := by
  simp only [CutoffDecoratedRay.decoration_eq, cutoffDecoratedRayCylinderEquiv,
    Equiv.coe_fn_mk, decoratedRayCylinderEquiv_history]

/-- Every cutoff ray projects to its complete original path. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_ray (r : Lifted) :
    (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).realization.2.ray =
      r.realization.2.ray.map (AffineMap.fst : V × V' →ᵃ[ℝ] V) :=
  decoratedRayCylinderEquiv_ray ℳ (fun j => U (r.itinerary.get j)) 0 b v w
    (fun j => g (r.itinerary.get j))
    (fun j => h (r.itinerary.get j))
    (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
    W S C Q r.realization

/-- Cylinder lifting preserves the entire encounter-parameter list at the cutoff. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_parameter (r : Lifted) :
    HEq (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).realization.2.parameter
      r.realization.2.parameter :=
  heq_of_eq (decoratedRayCylinderEquiv_parameter ℳ (fun j => U (r.itinerary.get j))
    0 b v w (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
    (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
    W S C Q r.realization)

/-- Lifting keeps the degree history. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_symm_history (r : Projected) :
    HEq ((cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k).symm
      r).realization.1.val r.realization.1.val := by
  have hh := decoratedRayCylinderEquiv_history ℳ (fun j => U (r.itinerary.get j))
    0 b v w (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
    (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
    W S C Q ((decoratedRayCylinderEquiv ℳ (fun j => U (r.itinerary.get j)) 0 b v w
      (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
      (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
      W S C Q).symm r.realization)
  rw [Equiv.apply_symm_apply] at hh
  exact heq_of_eq hh.symm

/-- Lifting keeps whole final decorations. -/
@[simp↓]
theorem cutoffDecoratedRayCylinderEquiv_symm_decoration (r : Projected) :
    ((cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k).symm r).decoration =
      r.decoration := by
  rw [← cutoffDecoratedRayCylinderEquiv_decoration ℳ v w W S C Q d U b g h sign A k,
    Equiv.apply_symm_apply]

/-- The lift of a cutoff ray projects back to its complete path. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_symm_ray (r : Projected) :
    ((cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k).symm
      r).realization.2.ray.map (AffineMap.fst : V × V' →ᵃ[ℝ] V) = r.realization.2.ray := by
  have hr := decoratedRayCylinderEquiv_ray ℳ (fun j => U (r.itinerary.get j)) 0 b v w
    (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
    (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
    W S C Q ((decoratedRayCylinderEquiv ℳ (fun j => U (r.itinerary.get j)) 0 b v w
      (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
      (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
      W S C Q).symm r.realization)
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

/-- Lifting keeps the entire encounter-parameter list at the cutoff. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_symm_parameter (r : Projected) :
    HEq ((cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k).symm
      r).realization.2.parameter r.realization.2.parameter := by
  have hp := decoratedRayCylinderEquiv_parameter ℳ (fun j => U (r.itinerary.get j)) 0 b v w
    (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
    (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
    W S C Q ((decoratedRayCylinderEquiv ℳ (fun j => U (r.itinerary.get j)) 0 b v w
      (fun j => g (r.itinerary.get j)) (fun j => h (r.itinerary.get j))
      (fun j => sign (r.itinerary.get j)) (fun j => A (r.itinerary.get j))
      W S C Q).symm r.realization)
  rw [Equiv.apply_symm_apply] at hp
  exact heq_of_eq hp.symm

/-- The finite weighted sum over every cutoff itinerary is independent of the
forgotten endpoint and equals the projected evaluation, with multiplicity retained. -/
@[simp]
theorem cutoffDecoratedEvaluation_cylinder [Finite J] :
    cutoffDecoratedEvaluation d ℳ U b vw G h sign
        (fun j => Prod.fst ⁻¹' A j) (fun j => Prod.fst ⁻¹' W j)
        (fun j => Prod.fst ⁻¹' S j) (Prod.fst ⁻¹' C) k Q =
      cutoffDecoratedEvaluation d ℳ U b v g h sign A W S C k Q.1 := by
  classical
  let := Fintype.ofFinite Lifted
  let := Fintype.ofFinite Projected
  rw [cutoffDecoratedEvaluation_def, cutoffDecoratedEvaluation_def]
  exact Fintype.sum_equiv
    (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k)
    _ _ (fun r =>
      (cutoffDecoratedRayCylinderEquiv_decoration ℳ v w W S C Q d U b g h sign A k r).symm)

end Mei
