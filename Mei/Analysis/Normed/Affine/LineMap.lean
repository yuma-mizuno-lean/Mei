/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Segments with perturbed endpoints

Two stability properties of affine segments `t ↦ AffineMap.lineMap x y t` when the
endpoints `x, y` move. A segment missing a closed set is surrounded by segments
missing it, by the tube lemma on the compact parameter interval. A line transverse
to a codimension-one affine subspace keeps meeting it, at a parameter depending
continuously on the two defining points; the parameter is the ratio of the values
of a linear functional whose kernel is the subspace direction.

These are the local ingredients for perturbing admissible wall-crossing paths
without changing their crossings.
-/

public section

open Set Filter Topology

namespace Mei

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- If the segment from `x` to `y` misses a closed set, so do all segments whose
endpoints are close to `x` and `y`. -/
theorem eventually_forall_lineMap_notMem {F : Set V} (hF : IsClosed F) {x y : V}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x y t ∉ F) :
    ∀ᶠ q : V × V in 𝓝 (x, y), ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap q.1 q.2 t ∉ F := by
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => ?_
  have hc : Continuous fun z : (V × V) × ℝ => AffineMap.lineMap z.1.1 z.1.2 z.2 :=
    continuous_fst.fst.lineMap continuous_fst.snd continuous_snd
  exact hc.continuousAt.eventually_mem (hF.isOpen_compl.mem_nhds (h t ht))

end Mei

namespace AffineSubspace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A line through `x` and `y`, transverse to a codimension-one affine subspace `A`,
meets `A` at a parameter `t₀`. Lines through points close to `x` and `y` meet `A` at
a parameter `τ q` depending continuously on the two points, with `τ (x, y) = t₀`. -/
theorem exists_continuousAt_lineMap_mem [FiniteDimensional ℝ V]
    (A : AffineSubspace ℝ V) (hA : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V)
    {x y : V} (hxy : y - x ∉ A.direction) {t₀ : ℝ} (ht₀ : AffineMap.lineMap x y t₀ ∈ A) :
    ∃ τ : V × V → ℝ, ContinuousAt τ (x, y) ∧ τ (x, y) = t₀ ∧
      ∀ᶠ q : V × V in 𝓝 (x, y), AffineMap.lineMap q.1 q.2 (τ q) ∈ A := by
  obtain ⟨f, hf, hfA⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxy inferInstance
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf rfl
  have hker : LinearMap.ker f = A.direction := by
    have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
    exact (Submodule.eq_of_le_of_finrank_eq (LinearMap.le_ker_iff_map.mpr hfA)
      (by omega)).symm
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hden : ContinuousAt (fun q : V × V => f (q.2 - q.1)) (x, y) :=
    (hfc.comp (continuous_snd.sub continuous_fst)).continuousAt
  refine ⟨fun q => f (AffineMap.lineMap x y t₀ - q.1) / f (q.2 - q.1), ?_, ?_, ?_⟩
  · exact ((hfc.comp (continuous_const.sub continuous_fst)).continuousAt).div hden hf
  · rw [map_sub] at hf
    simp [AffineMap.lineMap_apply_module', mul_div_assoc, div_self hf]
  · filter_upwards [hden.eventually_ne hf] with q hq
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem ht₀, ← hker, LinearMap.mem_ker,
      vsub_eq_sub, map_sub, AffineMap.lineMap_apply_module', map_add, map_smul, smul_eq_mul,
      div_mul_cancel₀ _ hq, map_sub]
    ring

end AffineSubspace
