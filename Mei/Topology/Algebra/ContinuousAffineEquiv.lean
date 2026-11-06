/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Linear parts and normal pairings of continuous affine equivalences

The linear part of a composite continuous affine equivalence is the composite of the
linear parts, and a continuous linear equivalence is the linear part of the continuous affine
equivalence it defines.

An affine equivalence `e` transports a normal functional `f` to `f ∘ e⁻¹` on the
linear part. Pairing it with a transported vector gives the original pairing, while
pairing it with a transported point records the translation of `e`.
-/

public section

namespace ContinuousAffineEquiv

variable {k P₁ P₂ P₃ V₁ V₂ V₃ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]

/-- The linear part of a composite applies the two linear parts in order. -/
@[simp]
theorem linear_trans_apply (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (v : V₁) :
    (e.trans e').toAffineEquiv.linear v = e'.toAffineEquiv.linear (e.toAffineEquiv.linear v) :=
  (rfl)

variable {E F : Type*} [AddCommGroup E] [Module k E] [TopologicalSpace E]
  [AddCommGroup F] [Module k F] [TopologicalSpace F]

/-- A continuous linear equivalence is the linear part of the continuous affine equivalence it
defines. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.linear_toContinuousAffineEquiv_apply (L : E ≃L[k] F)
    (v : E) : L.toContinuousAffineEquiv.toAffineEquiv.linear v = L v :=
  -- `ContinuousLinearEquiv.toContinuousAffineEquiv` is built from `LinearEquiv.toAffineEquiv`,
  -- whose `linear` field is the given linear equivalence; Mathlib has no lemma for this field.
  (rfl)

end ContinuousAffineEquiv

namespace ContinuousLinearMap

variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- The transported normal pairs with a transported vector as the original normal
pairs with the vector. -/
theorem comp_symm_contLinear_linear (f : V →L[ℝ] ℝ) (e : V ≃ᴬ[ℝ] V') (x : V) :
    (f.comp e.symm.toContinuousAffineMap.contLinear) (e.toAffineEquiv.linear x) = f x := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousAffineMap.coe_contLinear,
    ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
    AffineEquiv.linear_toAffineMap, ContinuousAffineEquiv.toAffineEquiv_symm,
    AffineEquiv.linear_symm, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The transported normal pairs with a transported point as the original normal
pairs with the point, shifted by the pairing with the preimage of the origin. -/
theorem comp_symm_contLinear_apply (f : V →L[ℝ] ℝ) (e : V ≃ᴬ[ℝ] V') (x : V) :
    (f.comp e.symm.toContinuousAffineMap.contLinear) (e x) = f x - f (e.symm 0) := by
  have he := e.symm.toAffineEquiv.toAffineMap.linear_apply_vsub (e x) 0
  simpa only [ContinuousLinearMap.comp_apply, ContinuousAffineMap.coe_contLinear,
    ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
    AffineEquiv.coe_toAffineMap, vsub_eq_sub, sub_zero, ContinuousAffineEquiv.coe_coe,
    ContinuousAffineEquiv.symm_apply_apply, map_sub] using congrArg f he

end ContinuousLinearMap
