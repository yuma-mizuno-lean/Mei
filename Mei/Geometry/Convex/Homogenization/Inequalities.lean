/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Homogenization
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Homogeneous inequalities for homogenization

For a nonempty affine-inequality presentation, the closed cone generated
by its height-one embedding is exactly the cone obtained by homogenizing its
inequalities and requiring nonnegative height. The height-zero part follows
from the recession-cone theorem, so unbounded bases and lineality are included.

Nonemptiness is essential. Empty presentations can give different homogeneous
inequality cones, whereas carrier-defined homogenization always gives the zero
cone for the empty set.
-/

public section

namespace ContinuousAffineMap

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The continuous linear functional homogenizing an affine inequality. -/
def homogenizedInequality (g : V →ᴬ[ℝ] ℝ) : (V × ℝ) →L[ℝ] ℝ :=
  g.contLinear.comp (ContinuousLinearMap.fst ℝ V ℝ) +
    g 0 • ContinuousLinearMap.snd ℝ V ℝ

/-- At height `t`, homogenization adds `t` times the original affine offset. -/
@[simp]
theorem homogenizedInequality_apply (g : V →ᴬ[ℝ] ℝ) (x : V) (t : ℝ) :
    homogenizedInequality g (x, t) = g.linear x + t * g 0 := by
  simp [homogenizedInequality, mul_comm]

/-- At nonzero height, rescaling an affine value gives its homogeneous value. -/
theorem mul_affine_apply_inv_smul (g : V →ᴬ[ℝ] ℝ) (x : V) {t : ℝ}
    (ht : t ≠ 0) : t * g (t⁻¹ • x) = homogenizedInequality g (x, t) := by
  have heval : g (t⁻¹ • x) = t⁻¹ * g.linear x + g 0 := by
    simpa only [vadd_eq_add, add_zero, map_smul, smul_eq_mul,
      ContinuousAffineMap.coe_contLinear] using g.map_vadd 0 (t⁻¹ • x)
  rw [heval, homogenizedInequality_apply, mul_add, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]

end ContinuousAffineMap

open ContinuousAffineMap Set

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The cone of homogeneous inequalities associated with an affine family. -/
def homogeneousInequalityCone (g : ι → (V →ᴬ[ℝ] ℝ)) : PointedCone ℝ (V × ℝ) where
  carrier := {z | 0 ≤ z.2 ∧ ∀ i, homogenizedInequality (g i) z ≤ 0}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    refine ⟨add_nonneg hz.1 hw.1, fun i => ?_⟩
    simpa only [map_add] using add_nonpos (hz.2 i) (hw.2 i)
  smul_mem' := by
    intro c z hz
    refine ⟨mul_nonneg c.property hz.1, fun i => ?_⟩
    simp only [← Nonneg.coe_smul]
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos c.property (hz.2 i)

/-- Membership in the homogeneous inequality cone records height and all rows. -/
@[simp]
theorem mem_homogeneousInequalityCone {g : ι → (V →ᴬ[ℝ] ℝ)} {z : V × ℝ} :
    z ∈ homogeneousInequalityCone g ↔
      0 ≤ z.2 ∧ ∀ i, homogenizedInequality (g i) z ≤ 0 := (Iff.rfl)

/-- The carrier-defined homogenization of a nonempty affine-inequality
solution set has exactly its homogeneous inequalities. -/
theorem mem_homogenization_setOf_forall_iff
    {g : ι → (V →ᴬ[ℝ] ℝ)} (hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty)
    {x : V} {t : ℝ} :
    (x, t) ∈ homogenization {x : V | ∀ i, g i x ≤ 0} ↔
      0 ≤ t ∧ ∀ i, homogenizedInequality (g i) (x, t) ≤ 0 := by
  have heq : {x : V | ∀ i, g i x ≤ 0} = ⋂ i, (g i) ⁻¹' Set.Iic 0 := by
    ext x
    simp
  have hclosed : IsClosed {x : V | ∀ i, g i x ≤ 0} := by
    rw [heq]
    exact isClosed_iInter fun i => isClosed_Iic.preimage (g i).continuous
  have hconvex : _root_.Convex ℝ {x : V | ∀ i, g i x ≤ 0} := by
    rw [heq]
    exact convex_iInter fun i => (convex_Iic (0 : ℝ)).affine_preimage (g i).toAffineMap
  constructor
  · intro hz
    have ht := homogenization_height_nonneg hz
    refine ⟨ht, ?_⟩
    rcases ht.eq_or_lt with rfl | ht
    · have hv := (hconvex.mem_homogenization_zero_iff hne hclosed).mp hz
      have hlin := (mem_recessionCone_setOf_forall_iff (g := fun i => (g i).toAffineMap) hne).mp hv
      simpa only [homogenizedInequality_apply, zero_mul, add_zero] using hlin
    · have hx := (hconvex.mem_homogenization_pos_iff hclosed ht).mp hz
      intro i
      rw [← mul_affine_apply_inv_smul (g i) x ht.ne']
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hx i)
  · rintro ⟨ht, hrows⟩
    rcases ht.eq_or_lt with rfl | ht
    · apply (hconvex.mem_homogenization_zero_iff hne hclosed).mpr
      apply (mem_recessionCone_setOf_forall_iff (g := fun i => (g i).toAffineMap) hne).mpr
      simpa only [homogenizedInequality_apply, zero_mul, add_zero] using hrows
    · apply (hconvex.mem_homogenization_pos_iff hclosed ht).mpr
      intro i
      have hi := hrows i
      rw [← mul_affine_apply_inv_smul (g i) x ht.ne'] at hi
      by_contra hx
      exact (not_le_of_gt (mul_pos ht (lt_of_not_ge hx))) hi

/-- Homogenization agrees as a pointed cone with the explicit homogeneous
inequality cone of every nonempty affine presentation. -/
theorem homogenization_setOf_forall_eq
    (g : ι → (V →ᴬ[ℝ] ℝ)) (hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    homogenization {x : V | ∀ i, g i x ≤ 0} = homogeneousInequalityCone g := by
  ext z
  exact mem_homogenization_setOf_forall_iff hne

end Mei.Convex
