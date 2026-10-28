/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Completion
public import Mei.LinearAlgebra.ModuleFiltration.Map
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Homogeneous components of completion maps

A continuous homogeneous linear map sends a completed coefficient to the sum of
its source components over the fiber of the target degree. The sum can be computed
in any source cutoff prescribed by the continuity modulus. This permits degree
maps with kernels: distinct source components can contribute to one target component.
For injective regradings, homogeneous projections commute with the completed map.

The constructions retain the compatible-family completions and use their finite
quotient maps. Finite reconstruction comes from `PositiveDegrees.completionEquivPi`;
the injective comparison uses `DirectSum.map_decompose_shift`.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open _root_.DirectSum

variable {ι κ R M N : Type*} [AddCommMonoid ι] [AddCommMonoid κ]
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [DecidableEq ι] [DecidableEq κ]
  (d : PositiveDegrees ι) (e : PositiveDegrees κ)
  (ℳ : ι → Submodule R M) (𝓝 : κ → Submodule R N)
  [Decomposition ℳ] [Decomposition 𝓝]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N)
  (hF : ∀ k, F.submodule (k + 1) = d.degreeSubmodule ℳ k)
  (hG : ∀ k, G.submodule (k + 1) = e.degreeSubmodule 𝓝 k)

variable (f : M →ₗ[R] N) (σ : ι → κ)
  (hhom : ∀ n x, x ∈ ℳ n → f x ∈ 𝓝 (σ n))
  (μ : ℕ → ℕ) (hμ : Monotone μ)
  (hf : ∀ k, F.submodule (μ k + 1) ≤ (G.submodule (k + 1)).comap f)

include hhom in
open Classical in
/-- A target component of the completed map is the finite sum of all source components
mapping to that degree. Any target cutoff retaining the component can be used. -/
theorem completionComponent_completionMap_eq_sum
    (hℳ : ∀ n, n ∉ d.monoid → ℳ n = ⊥)
    (j : κ) (k : ℕ) (hj : e.degree j ≤ k) (x : F.completion) :
    (e.completionComponent 𝓝 G hG j (F.completionMap G f μ hμ hf x) : N) =
      ∑ n ∈ (d.finite_cutoff (μ k)).toFinset with σ n = j,
        f (d.completionComponent ℳ F hF n x : M) := by
  rw [e.completionComponent_eq_quotientComponent 𝓝 G hG j k hj,
    F.projection_completionMap,
    d.projection_eq_sum_completionComponent ℳ F hF hℳ,
    Submodule.mapQ_apply, quotientComponent_mk]
  have hproj (n : ι) :
      (decompose 𝓝 (f (d.completionComponent ℳ F hF n x : M)) j : N) =
        if σ n = j then f (d.completionComponent ℳ F hF n x : M) else 0 := by
    split_ifs with h
    · exact decompose_of_mem_same 𝓝 (h ▸ hhom n _
        (d.completionComponent ℳ F hF n x).property)
    · exact decompose_of_mem_ne 𝓝 (hhom n _
        (d.completionComponent ℳ F hF n x).property) h
  simp only [map_sum, decompose_sum, sum_apply, Submodule.coe_sum]
  simp_rw [hproj]
  rw [Finset.sum_filter]

include hhom in
/-- Under an injective regrading, taking a completed component commutes with the map.
No support assumption on the source grading is needed for this comparison. -/
theorem completionComponent_completionMap_of_injective (hσ : Function.Injective σ)
    (n : ι) (x : F.completion) :
    (e.completionComponent 𝓝 G hG (σ n) (F.completionMap G f μ hμ hf x) : N) =
      f (d.completionComponent ℳ F hF n x : M) := by
  let k := (e.degree (σ n)).toNat
  let l := max (μ k) (d.degree n).toNat
  have hn : d.degree n ≤ l := (Int.self_le_toNat _).trans (Int.ofNat_le.mpr (le_max_right _ _))
  rw [e.completionComponent_eq_quotientComponent 𝓝 G hG (σ n) k
      (Int.self_le_toNat _),
    F.projection_completionMap_of_le G f μ hμ hf k l (le_max_left _ _) x,
    d.completionComponent_eq_quotientComponent ℳ F hF n l hn]
  obtain ⟨a, ha⟩ := (F.submodule (l + 1)).mkQ_surjective (F.projection l x)
  rw [← ha, Submodule.mkQ_apply, Submodule.mapQ_apply, quotientComponent_mk,
    quotientComponent_mk]
  exact (DirectSum.map_decompose_shift ℳ 𝓝 f.toAddMonoidHom σ hσ hhom n a).symm

end Mei.PositiveDegrees
