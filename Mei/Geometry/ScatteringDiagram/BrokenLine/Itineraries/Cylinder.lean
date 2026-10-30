/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.Convex.Sweep.Cylinder

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

We use `cutoffDecoratedRayFiberEquiv` for finiteness of the ray family,
`AdmissibleRayRealization.eq_backwardRay` and the backward cylinder-domain
identities. The geometric lifting follows Carl–Pumperla–Siebert, *A tropical
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
  toFun r := ⟨r.itinerary, ⟨⟨r.realization.1.val, by
    simpa only [mem_decoratedHistorySupport, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst'] using r.realization.1.property⟩,
    admissibleRayRealization _ _ _ _ _ _ _ _ (by
      simpa only [mem_admissibleBackwardDomain, backwardAvoidanceDomain_cylinder,
        backwardIncomingDomain_cylinder, backwardSingularAvoidanceDomain_cylinder,
        mem_preimage] using r.realization.2.mem_admissibleBackwardDomain)⟩,
    r.degree_mem, r.degree_sub_mem⟩
  invFun r := ⟨r.itinerary, ⟨⟨r.realization.1.val, by
    simpa only [mem_decoratedHistorySupport, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst'] using r.realization.1.property⟩,
    admissibleRayRealization _ _ _ _ _ _ _ _ (by
      simpa only [mem_admissibleBackwardDomain, backwardAvoidanceDomain_cylinder,
        backwardIncomingDomain_cylinder, backwardSingularAvoidanceDomain_cylinder,
        mem_preimage] using r.realization.2.mem_admissibleBackwardDomain)⟩,
    r.degree_mem, r.degree_sub_mem⟩
  left_inv r := by
    apply CutoffDecoratedRay.ext
    · rfl
    exact heq_of_eq (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))
  right_inv r := by
    apply CutoffDecoratedRay.ext
    · rfl
    exact heq_of_eq (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))

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
      r.realization.1.val := (HEq.rfl)

/-- Whole final decorations are preserved across the complete cutoff family. -/
@[simp↓]
theorem cutoffDecoratedRayCylinderEquiv_decoration (r : Lifted) :
    (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).decoration =
      r.decoration := by
  simp only [CutoffDecoratedRay.decoration_eq, cutoffDecoratedRayCylinderEquiv,
    Equiv.coe_fn_mk]

/-- Every cutoff ray projects to its complete original path. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_ray (r : Lifted) :
    (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).realization.2.ray =
      r.realization.2.ray.map (AffineMap.fst : V × V' →ᵃ[ℝ] V) := by
  obtain ⟨hpos, _, hr⟩ := r.realization.2.eq_backwardRay
  obtain ⟨_, _, he⟩ :=
    AdmissibleRayRealization.eq_backwardRay
      (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).realization.2
  rw [he, hr]
  exact (backwardRay_map_fst (fun j => g (r.itinerary.get j))
    (fun j => h (r.itinerary.get j))
    (fun j => v (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j))
    (fun j => w (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j)) Q
    (hpos := by
      have hp : ∀ j, 0 < backwardTime (fun j => g (r.itinerary.get j))
          (fun j => h (r.itinerary.get j))
          (fun j => v (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.castSucc)) j Q.1 := by
        simpa only [backwardTime_fst] using hpos
      simpa only [backwardTime_apply] using hp)).symm

/-- Cylinder lifting preserves the entire encounter-parameter list at the cutoff. -/
@[simp]
theorem cutoffDecoratedRayCylinderEquiv_parameter (r : Lifted) :
    HEq (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).realization.2.parameter
      r.realization.2.parameter := by
  obtain ⟨_, hp, _⟩ := r.realization.2.eq_backwardRay
  obtain ⟨_, he, _⟩ :=
    AdmissibleRayRealization.eq_backwardRay
      (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k r).realization.2
  apply heq_of_eq
  -- Align the dependent parameter index with the retained encounter word.
  simp only [cutoffDecoratedRayCylinderEquiv, Equiv.coe_fn_mk] at he ⊢
  ext j
  rw [he, hp, backwardParameter_fst]

/-- The finite weighted sum over every cutoff itinerary is independent of the
forgotten endpoint and equals the projected evaluation, with multiplicity retained. -/
theorem cutoffDecoratedEvaluation_cylinder [Finite J] :
    cutoffDecoratedEvaluation d ℳ U b vw G h sign
        (fun j => Prod.fst ⁻¹' A j) (fun j => Prod.fst ⁻¹' W j)
        (fun j => Prod.fst ⁻¹' S j) (Prod.fst ⁻¹' C) k Q =
      cutoffDecoratedEvaluation d ℳ U b v g h sign A W S C k Q.1 := by
  classical
  let := Fintype.ofFinite Lifted
  let := Fintype.ofFinite Projected
  rw [cutoffDecoratedEvaluation_eq_sum_decoration, cutoffDecoratedEvaluation_eq_sum_decoration]
  exact Fintype.sum_equiv
    (cutoffDecoratedRayCylinderEquiv ℳ v w W S C Q d U b g h sign A k)
    _ _ (fun r =>
      (cutoffDecoratedRayCylinderEquiv_decoration ℳ v w W S C Q d U b g h sign A k r).symm)

end Mei
