/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mei.Topology.Maps.Proper

/-!
# Evaluation and properness of continuous affine maps

This module gives the evaluation of a real continuous affine functional along
an affine ray in terms of its linear part, and characterizes eventual satisfaction
of an affine inequality along that ray. Nonzero-velocity real affine lines
are closed embeddings, and their restrictions to closed incoming half-lines are
proper. Continuous paths with the same incoming affine germ are also proper
on closed incoming half-lines, using `IsProperMap.of_eqOn_compl_isCompact`.
The embedding criterion is inherited from the linear part using Mathlib's
`AffineMap.isClosedEmbedding_linear_iff`.
-/

public section

namespace ContinuousAffineMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Evaluation of a continuous affine functional along an affine ray. -/
theorem apply_add_smul (g : V →ᴬ[ℝ] ℝ) (y n : V) (t : ℝ) :
    g (y + t • n) = g y + g.linear n * t := by
  rw [add_comm y]
  have h := g.map_vadd' y (t • n)
  simpa only [vadd_eq_add, map_smul, smul_eq_mul, mul_comm, add_comm,
    AffineMap.toFun_eq_coe, ContinuousAffineMap.coe_toAffineMap] using h

/-- An affine inequality holds eventually along a ray precisely when it decreases
strictly, or is constant along the ray and already holds at its base point. -/
@[simp↓] -- Normalize the affine ray before the generic atTop eventuality expands.
theorem eventually_apply_add_smul_le_iff (g : V →ᴬ[ℝ] ℝ) (x w : V) :
    (∀ᶠ t : ℝ in Filter.atTop, g (x + t • w) ≤ 0) ↔
      g.linear w < 0 ∨ g.linear w = 0 ∧ g x ≤ 0 := by
  simp only [apply_add_smul]
  rcases lt_trichotomy (g.linear w) 0 with hneg | hzero | hpos
  · refine iff_of_true ?_ (Or.inl hneg)
    filter_upwards [Filter.eventually_ge_atTop (-g x / g.linear w)] with t ht
    have := (div_le_iff_of_neg hneg).mp ht
    linarith
  · simp only [hzero, zero_mul, add_zero, Filter.eventually_const, lt_self_iff_false,
      true_and, false_or]
  · have hnot : ¬ ∀ᶠ t : ℝ in Filter.atTop, g x + g.linear w * t ≤ 0 := by
      intro he
      obtain ⟨t, ht, hle⟩ := ((Filter.eventually_gt_atTop (-g x / g.linear w)).and he).exists
      have := (div_lt_iff₀ hpos).mp ht
      nlinarith
    simp [hnot, hpos.ne', hpos.not_gt]

end ContinuousAffineMap

namespace ContinuousAffineMap

open Set Topology

variable {V P : Type*} [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [TopologicalSpace P] [AddTorsor V P] [IsTopologicalAddTorsor P]
  (f : ℝ →ᴬ[ℝ] P)

/-- A nonzero velocity gives a closed embedding of the entire affine line. -/
theorem isClosedEmbedding_of_velocity_ne_zero (hv : f.contLinear 1 ≠ 0) :
    IsClosedEmbedding f := by
  apply (AffineMap.isClosedEmbedding_linear_iff (f := f.toAffineMap)).mp
  have hlin : (f.toAffineMap.linear : ℝ → V) = fun t => t • f.contLinear 1 := by
    funext t
    simpa only [smul_eq_mul, mul_one, coe_contLinear] using f.contLinear.map_smul t (1 : ℝ)
  rw [hlin]
  exact isClosedEmbedding_smul_left hv

/-- Every closed incoming half-line with nonzero velocity is proper. -/
theorem isProperMap_restrict_Iic (hv : f.contLinear 1 ≠ 0) (a : ℝ) :
    IsProperMap (fun t : Iic a => f t) :=
  ((f.isClosedEmbedding_of_velocity_ne_zero hv).comp
    isClosed_Iic.isClosedEmbedding_subtypeVal).isProperMap

/-- A continuous path with a nonzero-velocity incoming affine germ is proper
on every closed incoming half-line. -/
theorem isProperMap_restrict_Iic_of_eventuallyEq {γ : ℝ → P}
    (hγ : Continuous γ) (heq : γ =ᶠ[Filter.atBot] f) (hv : f.contLinear 1 ≠ 0)
    (b : ℝ) : IsProperMap (fun t : Iic b => γ t) := by
  let : T2Space P := (Homeomorph.vaddConst (f 0)).t2Space
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp heq
  refine (f.isProperMap_restrict_Iic hv b).of_eqOn_compl_isCompact
    (K := Subtype.val ⁻¹' Icc a b) (hγ.comp continuous_subtype_val)
    (isClosed_Iic.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc) ?_
  intro t ht
  exact ha t.val (lt_of_not_ge (fun hat => ht ⟨hat, t.property⟩)).le

end ContinuousAffineMap
