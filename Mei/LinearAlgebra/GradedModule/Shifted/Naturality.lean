/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Component
public import Mei.Algebra.PositiveDegrees.Naturality

/-!
# Regrading components of shifted coefficient completions

A homogeneous coefficient map may merge ambient degrees. On shifted completions,
each target component is the sum of the mapped source components in its degree
fiber, computed in a finite relative cutoff. The shift itself can have negative
ambient degree. The map on the shifted modules is supplied together with its
ambient formula, so the result applies to any existing restriction construction.

We use the finite reconstruction and component maps of the existing shifted
completion, and `ModuleFiltration.completionMap` for continuity. The shifted
coefficient setting follows Travis Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open _root_.DirectSum

variable {Γ Γ' R M N : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [DecidableEq Γ] [DecidableEq Γ']
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ')
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R N)
  [Decomposition ℳ] [Decomposition 𝓝]
  (p : Γ) (T : Γ →+ Γ') (ψ : M →ₗ[R] N)
  (f : shiftedSubmodule ℳ d.monoid p →ₗ[R] shiftedSubmodule 𝓝 e.monoid (T p))
  (hcoe : ∀ a, (f a : N) = ψ (a : M))
  (hhom : ∀ q a, a ∈ ℳ q → ψ a ∈ 𝓝 (T q))
  (μ : ℕ → ℕ) (hμ : Monotone μ)
  (hf : ∀ k, (d.shiftedFiltration ℳ p).submodule (μ k + 1) ≤
    ((e.shiftedFiltration 𝓝 (T p)).submodule (k + 1)).comap f)

include hcoe hhom in
open Classical in
/-- Under a continuous homogeneous coefficient map, all source degrees with the same
image contribute to the target shifted component. The sum uses relative degrees
through `μ k`, including zero and any nonzero degrees killed by a spatial projection. -/
theorem shiftedHomogeneousComponent_completionMap_eq_sum (j : Γ') (k : ℕ)
    (hj : e.degree j ≤ k) (x : d.ShiftedCoefficients ℳ p) :
    (e.shiftedHomogeneousComponent 𝓝 (T p) (T p + j)
      ((d.shiftedFiltration ℳ p).completionMap (e.shiftedFiltration 𝓝 (T p))
        f μ hμ hf x) : N) =
      ∑ n ∈ (d.finite_cutoff (μ k)).toFinset with T n = j,
        ψ (d.shiftedHomogeneousComponent ℳ p (p + n) x : M) := by
  let F := d.shiftedFiltration ℳ p
  let G := e.shiftedFiltration 𝓝 (T p)
  have hrel (n : Γ) (a : shiftedSubmodule ℳ d.monoid p)
      (ha : a ∈ shiftedGrading ℳ d.monoid p n) :
      f a ∈ shiftedGrading 𝓝 e.monoid (T p) (T n) := by
    apply (mem_shiftedGrading 𝓝 e.monoid (T p)).mpr
    rw [hcoe]
    simpa only [map_add] using hhom (p + n) a ((mem_shiftedGrading ℳ d.monoid p).mp ha)
  have h := d.completionComponent_completionMap_eq_sum e
    (shiftedGrading ℳ d.monoid p) (shiftedGrading 𝓝 e.monoid (T p)) F G
    (d.shiftedFiltration_succ ℳ p) (e.shiftedFiltration_succ 𝓝 (T p))
    f T hrel μ hμ hf (fun n hn => shiftedGrading_eq_bot ℳ d.monoid p hn) j k hj x
  rw [← e.coe_completionComponent_shiftedGrading 𝓝 (T p)]
  calc
    _ = ∑ n ∈ (d.finite_cutoff (μ k)).toFinset with T n = j,
        (f (d.completionComponent (shiftedGrading ℳ d.monoid p) F
          (d.shiftedFiltration_succ ℳ p) n x) : N) := by
      simpa only [Submodule.coe_sum] using congrArg (fun a : shiftedSubmodule 𝓝 e.monoid
        (T p) => (a : N)) h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hcoe]
      rw [d.coe_completionComponent_shiftedGrading ℳ p]

end Mei.PositiveDegrees
