/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Normal pairings under affine coordinate changes

An affine equivalence `e` transports a normal functional `f` to `f ∘ e⁻¹` on the
linear part. Pairing it with a transported vector gives the original pairing, while
pairing it with a transported point records the translation of `e`.
-/

public section

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
