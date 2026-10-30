/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Affine.FiniteRay.Map
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Affine coordinate changes of admissible rays

An affine coordinate change transports the entire admissible ray and preserves
its encounter parameters. Normals transform by the inverse linear part, and
hyperplane offsets include the translation. Selected supports, all other walls,
singular sets and the incoming source transform together. This gives a bijection
without genericity, rationality, finiteness or nonzero-direction assumptions.

We use `FiniteAffineRay.map` for the path and `AdmissibleRayRealization` for the
complete encounter and avoidance conditions. The coordinate conventions are those
of Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter

namespace Mei.Convex

variable {V V' J K : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin (n + 1) → V)
  (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)
  (e : V ≃ᴬ[ℝ] V') (Q : V)

local notation "g" => fun j =>
  ContinuousLinearMap.comp (f j) e.symm.toContinuousAffineMap.contLinear
local notation "b" => fun j => c j - f j (e.symm 0)
local notation "u" => fun j => e.toAffineEquiv.linear (v j)
local notation "Source" => AdmissibleRayRealization f c v P W S C Q
local notation "Target" => AdmissibleRayRealization g b u
  (fun j => e '' P j) (fun j => e '' W j)
  (fun j => e '' S j) (e '' C) (e Q)

/-- Affine changes of coordinates identify actual admissible ray fibers. The
translation changes hyperplane offsets, while the inverse linear part changes
normals; every recorded encounter, including a geometrically straight one, remains. -/
def admissibleRayAffineEquiv : Source ≃ Target := by
  -- Normal pairings are linear, while encounter heights include the translation.
  have hlinear (j : Fin n) (x : V) : g j (e.toAffineEquiv.linear x) = f j x := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousAffineMap.coe_contLinear,
      ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
      AffineEquiv.linear_toAffineMap, ContinuousAffineEquiv.toAffineEquiv_symm,
      AffineEquiv.linear_symm, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hforward (j : Fin n) (x : V) : g j (e x) = f j x - f j (e.symm 0) := by
    have he := e.symm.toAffineEquiv.toAffineMap.linear_apply_vsub (e x) 0
    simpa only [ContinuousLinearMap.comp_apply, ContinuousAffineMap.coe_contLinear,
      ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
      AffineEquiv.coe_toAffineMap, vsub_eq_sub, sub_zero, ContinuousAffineEquiv.coe_coe,
      ContinuousAffineEquiv.symm_apply_apply, map_sub] using congrArg (f j) he
  have hbackward (j : Fin n) (x : V') :
      f j (e.symm x) = g j x + f j (e.symm 0) := by
    have he := hforward j (e.symm x)
    rw [e.apply_symm_apply] at he
    linarith
  -- Push the ray forward; pulling it back preserves the same local encounter data.
  refine {
    toFun := fun r => {
      ray := r.ray.map e.toAffineEquiv.toAffineMap
      parameter := r.parameter
      parameter_zero := r.parameter_zero
      strictAnti_parameter := r.strictAnti_parameter
      transverse := fun j => by rw [hlinear]; exact r.transverse j
      endpoint_eq := by simp [r.endpoint_eq]
      directionAt_eq := fun j => by simp [r.directionAt_eq]
      bends_recorded := fun t ht => r.bends_recorded t
        (r.ray.support_bends_map_subset _ ht)
      height_eq := fun j => by
        simp only [FiniteAffineRay.map_apply, AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, hforward, r.height_eq]
      incidence := fun j => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.incidence j
      avoids_walls := fun j t ht htime => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.avoids_walls j t ht htime
      incoming := by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.incoming
      avoids_singular := fun j t ht => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.avoids_singular j t ht
      off_walls := fun j => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, e.symm_apply_apply]
          using r.off_walls j }
    invFun := fun r => {
      ray := r.ray.map e.symm.toAffineEquiv.toAffineMap
      parameter := r.parameter
      parameter_zero := r.parameter_zero
      strictAnti_parameter := r.strictAnti_parameter
      transverse := fun j => by
        have ht := r.transverse j
        rwa [hlinear] at ht
      endpoint_eq := by simp [r.endpoint_eq]
      directionAt_eq := fun j => by simp [r.directionAt_eq]
      bends_recorded := fun t ht => r.bends_recorded t
        (r.ray.support_bends_map_subset _ ht)
      height_eq := fun j => by
        simp only [FiniteAffineRay.map_apply, AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe]
        rw [hbackward j (r.ray (r.parameter j.succ)), r.height_eq]
        ring
      incidence := fun j => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.incidence j
      avoids_walls := fun j t ht htime => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.avoids_walls j t ht htime
      incoming := by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.incoming
      avoids_singular := fun j t ht => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, FiniteAffineRay.map_apply,
          AffineEquiv.coe_toAffineMap,
          ContinuousAffineEquiv.coe_coe, e.symm_apply_apply] using r.avoids_singular j t ht
      off_walls := fun j => by
        simpa only [e.image_eq_preimage_symm, mem_preimage, e.symm_apply_apply]
          using r.off_walls j }
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }

/-- The forward coordinate change maps the entire path, including its incoming tail. -/
@[simp]
theorem admissibleRayAffineEquiv_ray (r : Source) :
    (admissibleRayAffineEquiv f c v P W S C e Q r).ray =
      r.ray.map e.toAffineEquiv.toAffineMap := (rfl)

/-- Coordinate changes preserve every encounter parameter. -/
@[simp]
theorem admissibleRayAffineEquiv_parameter (r : Source) :
    (admissibleRayAffineEquiv f c v P W S C e Q r).parameter = r.parameter := (rfl)

/-- The inverse coordinate change maps the complete path by the inverse affine map. -/
@[simp]
theorem admissibleRayAffineEquiv_symm_ray (r : Target) :
    ((admissibleRayAffineEquiv f c v P W S C e Q).symm r).ray =
      r.ray.map e.symm.toAffineEquiv.toAffineMap := (rfl)

/-- The inverse comparison also preserves every encounter parameter. -/
@[simp]
theorem admissibleRayAffineEquiv_symm_parameter (r : Target) :
    ((admissibleRayAffineEquiv f c v P W S C e Q).symm r).parameter = r.parameter := (rfl)

end Mei.Convex
