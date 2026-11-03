/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Recursion

/-!
# The completed recursion solution as a linear equivalence

For a filtration-raising endomorphism `f`, solving `x = a + f̂ x` is an invertible
linear operation on the completion. Its inverse recovers the incoming value as
`x - f̂ x`. Both directions preserve every completed filtration term, and filtered
coefficient intertwiners commute with the equivalence.

The forward map is the existing `completionRecursion`, assembled from the finite
quotient solutions. Invertibility uses its recursion equation and uniqueness;
no nilpotence on the original module, completeness, or separatedness is required.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) (f : Module.End R M)
  (hf : ∀ k, F.submodule k ≤ (F.submodule (k + 1)).comap f)

/-- The completed recursion solution operator, with inverse `x ↦ x - f̂ x`. -/
def completionRecursionEquiv : F.completion ≃ₗ[R] F.completion where
  __ := F.completionRecursion f hf
  invFun x := x - F.completionMap F f id monotone_id
    (fun k _ hx => F.antitone (Nat.le_succ (k + 1)) (hf (k + 1) hx)) x
  left_inv a := by
    have h := F.completionRecursion_eq_add_completionMap f hf a
    exact sub_eq_iff_eq_add.mpr h
  right_inv x := by
    apply Eq.symm
    apply F.eq_completionRecursion_of_eq_add_completionMap f hf
    exact (sub_add_cancel x _).symm

/-- The equivalence uses the canonical finite-quotient recursion solution. -/
@[simp]
theorem completionRecursionEquiv_apply (a : F.completion) :
    F.completionRecursionEquiv f hf a = F.completionRecursion f hf a := by
  rw [completionRecursionEquiv]
  rfl

/-- The inverse recovers the incoming coefficient by subtracting its propagated value. -/
theorem completionRecursionEquiv_symm_apply (x : F.completion) :
    (F.completionRecursionEquiv f hf).symm x = x - F.completionMap F f id monotone_id
      (fun k _ hx => F.antitone (Nat.le_succ (k + 1)) (hf (k + 1) hx)) x := by
  rw [completionRecursionEquiv]
  rfl

/-- Recovering the incoming value also preserves and reflects filtration order. -/
@[simp]
theorem completionRecursionEquiv_symm_mem_completedFiltration_iff
    (k : ℕ) (x : F.completion) :
    (F.completionRecursionEquiv f hf).symm x ∈ F.completedFiltration.submodule k ↔
      x ∈ F.completedFiltration.submodule k := by
  have h := F.completionRecursion_mem_completedFiltration_iff f hf k
    ((F.completionRecursionEquiv f hf).symm x)
  rw [← completionRecursionEquiv_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

section Naturality

variable {N : Type*} [AddCommGroup N] [Module R N]
  (G : ModuleFiltration R N) (g : Module.End R N)
  (hg : ∀ k, G.submodule k ≤ (G.submodule (k + 1)).comap g)
  (r : M →ₗ[R] N) (ρ : ℕ → ℕ) (hρ : Monotone ρ)
  (hr : ∀ k, F.submodule (ρ k + 1) ≤ (G.submodule (k + 1)).comap r)
  (hfg : r.comp f = g.comp r)

include hfg in
/-- Filtered coefficient intertwiners commute with the inverse solution operator,
also for nonidentity cutoff moduli and noninjective coefficient maps. -/
theorem completionMap_completionRecursionEquiv_symm (x : F.completion) :
    F.completionMap G r ρ hρ hr ((F.completionRecursionEquiv f hf).symm x) =
      (G.completionRecursionEquiv g hg).symm (F.completionMap G r ρ hρ hr x) := by
  apply (G.completionRecursionEquiv g hg).injective
  rw [LinearEquiv.apply_symm_apply, completionRecursionEquiv_apply,
    ← F.completionMap_completionRecursion f hf G g hg r ρ hρ hr hfg,
    ← completionRecursionEquiv_apply, LinearEquiv.apply_symm_apply]

end Naturality

end Mei.ModuleFiltration
