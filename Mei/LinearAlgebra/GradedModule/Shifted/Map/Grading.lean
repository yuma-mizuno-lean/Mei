/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Map

/-!
# Homogeneity of fixed-degree finite coefficient maps

The fixed-degree coefficient map preserves the inherited relative grading of
each shifted quotient. This allows homogeneous incoming coefficients and their
entire histories to be specialized at the same coefficient cutoff.
-/

public section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R M N : Type*} [AddCommGroup Γ] [DecidableEq Γ] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  (p : Γ) (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝓝 q).comap f)

/-- Fixed-degree coefficient maps preserve the relative homogeneous pieces of
the finite quotient, including pieces killed by the map. -/
theorem quotientCoefficientMap_mem_shiftedQuotientGrading
    {k : ℕ} {n : Γ} {x : (d.shiftedFiltration ℳ p).quotient k}
    (hx : x ∈ (d.shiftedQuotientGrading ℳ p k).piece n) :
    d.quotientCoefficientMap ℳ 𝓝 p f hf k x ∈
      (d.shiftedQuotientGrading 𝓝 p k).piece n := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  rw [quotientCoefficientMap_mk]
  exact (d.mem_shiftedQuotientGrading_iff 𝓝 p).mpr
    ⟨_, d.shiftedCoefficientMap_mem_shiftedGrading ℳ 𝓝 p f hf ha, rfl⟩

end Mei.PositiveDegrees
