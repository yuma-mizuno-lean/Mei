/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Homogenization
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Homogeneous inequalities for polyhedral homogenization

For a nonempty finite affine-inequality presentation, the closed cone generated
by its height-one embedding is exactly the cone obtained by homogenizing its
inequalities and requiring nonnegative height. The height-zero part follows
from the recession-cone theorem, so unbounded bases and lineality are included.

Nonemptiness is essential. Empty presentations can give different homogeneous
inequality cones, whereas carrier-defined homogenization always gives the zero
cone for the empty set.
-/

public section

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The continuous linear functional homogenizing an affine inequality. -/
@[expose]
def homogenizedInequality (g : V →ᴬ[ℝ] ℝ) : (V × ℝ) →L[ℝ] ℝ :=
  g.contLinear.comp (ContinuousLinearMap.fst ℝ V ℝ) +
    g 0 • ContinuousLinearMap.snd ℝ V ℝ

/-- At height `t`, homogenization adds `t` times the original affine offset. -/
@[simp]
theorem homogenizedInequality_apply (g : V →ᴬ[ℝ] ℝ) (x : V) (t : ℝ) :
    homogenizedInequality g (x, t) = g.linear x + t * g 0 := by
  simp [homogenizedInequality, mul_comm]

/-- The cone of homogeneous inequalities associated with an affine family. -/
@[expose]
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
    change homogenizedInequality (g i) ((c : ℝ) • z) ≤ 0
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos c.property (hz.2 i)

/-- Membership in the homogeneous inequality cone records height and all rows. -/
@[simp]
theorem mem_homogeneousInequalityCone {g : ι → (V →ᴬ[ℝ] ℝ)} {z : V × ℝ} :
    z ∈ homogeneousInequalityCone g ↔
      0 ≤ z.2 ∧ ∀ i, homogenizedInequality (g i) z ≤ 0 := Iff.rfl

private theorem mul_affine_apply_inv_smul (g : V →ᴬ[ℝ] ℝ) (x : V) {t : ℝ}
    (ht : t ≠ 0) : t * g (t⁻¹ • x) = homogenizedInequality g (x, t) := by
  have heval : g (t⁻¹ • x) = t⁻¹ * g.linear x + g 0 := by
    have h := g.map_vadd' 0 (t⁻¹ • x)
    simpa only [vadd_eq_add, add_zero, map_smul, smul_eq_mul,
      AffineMap.toFun_eq_coe, ContinuousAffineMap.coe_toAffineMap] using h
  rw [heval, homogenizedInequality_apply, mul_add, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]

/-- The carrier-defined homogenization of a nonempty finite affine-inequality
polyhedron has exactly its homogeneous inequalities. -/
theorem mem_homogenization_setOf_forall_iff [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} (hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty)
    {x : V} {t : ℝ} :
    (x, t) ∈ homogenization {x : V | ∀ i, g i x ≤ 0} ↔
      0 ≤ t ∧ ∀ i, homogenizedInequality (g i) (x, t) ≤ 0 := by
  have hP := TauCeti.isConvexPolyhedron_setOf_forall g
  constructor
  · intro hz
    have ht := homogenization_height_nonneg hz
    refine ⟨ht, ?_⟩
    rcases ht.eq_or_lt with rfl | ht
    · have hv := (hP.convex.mem_homogenization_zero_iff hne hP.isClosed).mp hz
      have hlin := (mem_recessionCone_setOf_forall_iff hne).mp hv
      simpa only [homogenizedInequality_apply, zero_mul, add_zero] using hlin
    · have hx := (hP.convex.mem_homogenization_pos_iff hP.isClosed ht).mp hz
      intro i
      rw [← mul_affine_apply_inv_smul (g i) x ht.ne']
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hx i)
  · rintro ⟨ht, hrows⟩
    rcases ht.eq_or_lt with rfl | ht
    · apply (hP.convex.mem_homogenization_zero_iff hne hP.isClosed).mpr
      apply (mem_recessionCone_setOf_forall_iff hne).mpr
      simpa only [homogenizedInequality_apply, zero_mul, add_zero] using hrows
    · apply (hP.convex.mem_homogenization_pos_iff hP.isClosed ht).mpr
      intro i
      have hi := hrows i
      rw [← mul_affine_apply_inv_smul (g i) x ht.ne'] at hi
      by_contra hx
      exact (not_le_of_gt (mul_pos ht (lt_of_not_ge hx))) hi

/-- Homogenization agrees as a pointed cone with the explicit homogeneous
inequality cone of every nonempty finite affine presentation. -/
theorem homogenization_setOf_forall_eq [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    homogenization {x : V | ∀ i, g i x ≤ 0} = homogeneousInequalityCone g := by
  ext z
  exact mem_homogenization_setOf_forall_iff hne

/-- Homogeneous inequalities define a closed convex polyhedron when their
index family is finite. -/
theorem isConvexPolyhedron_homogeneousInequalityCone [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) :
    TauCeti.IsConvexPolyhedron (homogeneousInequalityCone g : Set (V × ℝ)) := by
  have hheight : TauCeti.IsConvexPolyhedron {z : V × ℝ | 0 ≤ z.2} := by
    simpa only [ContinuousAffineMap.neg_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousLinearMap.coe_snd', neg_nonpos] using
      TauCeti.isConvexPolyhedron_setOf_le
        (-(ContinuousLinearMap.snd ℝ V ℝ).toContinuousAffineMap)
  have hrows := TauCeti.isConvexPolyhedron_setOf_forall
    (fun i => (homogenizedInequality (g i)).toContinuousAffineMap)
  exact hheight.inter hrows

/-- In particular the actual homogenization of a nonempty convex polyhedron is
again a convex polyhedron, including for unbounded bases with lineality. -/
theorem isConvexPolyhedron_homogenization {P : Set V} (hP : TauCeti.IsConvexPolyhedron P)
    (hne : P.Nonempty) : TauCeti.IsConvexPolyhedron (homogenization P : Set (V × ℝ)) := by
  obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  rw [homogenization_setOf_forall_eq g hne]
  exact isConvexPolyhedron_homogeneousInequalityCone g

end Mei.Convex
