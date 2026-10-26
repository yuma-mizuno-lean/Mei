/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Selecting two equations for a subspace of codimension two

If a common kernel has codimension two, two members of the defining family
already cut it out. The family may be infinite and may contain zero or
redundant functionals. The proof uses Mathlib's dimension formula for the kernel
of a nonzero functional and strict monotonicity of finite dimension.
-/

public section

namespace LinearMap

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A common kernel of codimension two is the intersection of two kernels
from the same family. No finiteness assumption on the family is needed. -/
theorem exists_iInf_ker_eq_inf (f : ι → V →ₗ[K] K)
    (hdim : Module.finrank K (⨅ j, (f j).ker : Submodule K V) + 2 = Module.finrank K V) :
    ∃ j k, (⨅ l, (f l).ker) = (f j).ker ⊓ (f k).ker := by
  classical
  let W : Submodule K V := ⨅ j, (f j).ker
  have hW : W ≠ ⊤ := by
    intro heq
    have hd : Module.finrank K W + 2 = Module.finrank K V := hdim
    rw [heq, finrank_top] at hd
    omega
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra! hall
    exact hW (by simp [W, hall])
  have hdimj := Module.Dual.finrank_ker_add_one_of_ne_zero hj
  have hlt : W < (f j).ker := by
    refine lt_of_le_of_ne (iInf_le _ j) ?_
    intro heq
    have := congrArg (fun U : Submodule K V => Module.finrank K U) heq
    dsimp only [W] at this
    omega
  obtain ⟨v, hvj, hvW⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨k, hk⟩ : ∃ k, v ∉ (f k).ker := by
    simpa only [W, Submodule.mem_iInf, not_forall] using hvW
  have hinf : (f j).ker ⊓ (f k).ker < (f j).ker := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    exact hk ((heq.symm ▸ hvj : v ∈ (f j).ker ⊓ (f k).ker).2)
  refine ⟨j, k, Submodule.eq_of_le_of_finrank_eq
    (le_inf (iInf_le _ j) (iInf_le _ k)) ?_⟩
  have hupper := Submodule.finrank_lt_finrank_of_lt hinf
  have hlower := Submodule.finrank_mono
    (le_inf (iInf_le (fun l => (f l).ker) j) (iInf_le (fun l => (f l).ker) k))
  omega

end LinearMap
