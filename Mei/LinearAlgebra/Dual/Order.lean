/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Positive proportionality of linear functionals

Kernel inclusion makes two nonzero scalar-valued linear maps proportional.
If both are positive at one vector, the scalar is positive. This identifies
coorientations using a common positive test vector, without choosing a basis.
A functional vanishing on the kernel has constant sign on the positive half-space.

The construction uses Mathlib's `mem_span_of_iInf_ker_le_ker` for a singleton
family of linear functionals and `Submodule.mem_span_singleton`.
-/

public section

namespace LinearMap

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E]

/-- A functional vanishing on a coorientation's kernel has constant sign on its positive side. -/
theorem apply_pos_iff_of_ker_le_ker (f g : E →ₗ[K] K)
    (hker : f.ker ≤ g.ker) {v w : E} (hv : 0 < f v) (hw : 0 < f w) :
    0 < g v ↔ 0 < g w := by
  have hspan : g ∈ Submodule.span K ({f} : Set (E →ₗ[K] K)) := by
    simpa using (mem_span_of_iInf_ker_le_ker
      (L := fun _ : Unit => f) (K := g) (by simpa using hker))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hspan
  simp only [smul_apply, smul_eq_mul, mul_pos_iff_of_pos_right hv,
    mul_pos_iff_of_pos_right hw]

/-- Functionals with nested kernels and a common positive vector are positively proportional. -/
theorem exists_pos_smul_eq_of_ker_le_ker (f g : E →ₗ[K] K)
    (hker : f.ker ≤ g.ker) {v : E} (hf : 0 < f v) (hg : 0 < g v) :
    ∃ c : K, 0 < c ∧ c • f = g := by
  have hspan : g ∈ Submodule.span K ({f} : Set (E →ₗ[K] K)) := by
    simpa using (mem_span_of_iInf_ker_le_ker
      (L := fun _ : Unit => f) (K := g) (by simpa using hker))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  refine ⟨c, ?_, hc⟩
  have hv : c * f v = g v := by simpa using congrArg (fun q : E →ₗ[K] K => q v) hc
  exact (mul_pos_iff_of_pos_right hf).mp (hv.symm ▸ hg)

end LinearMap
