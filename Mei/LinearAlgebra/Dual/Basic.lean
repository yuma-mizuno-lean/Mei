/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Common kernels and dual coannihilators

The dual coannihilator of the span of a family of functionals is their common
kernel. This relates equations defining a submodule to the span of its conormals,
without finiteness assumptions on either the family or the ambient module.
-/

public section

namespace Submodule

/-- The dual coannihilator of a family's span is the intersection of its kernels. -/
@[simp]
theorem dualCoannihilator_span_range {R M : Type*} {ι : Sort*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] (f : ι → Module.Dual R M) :
    (span R (Set.range f)).dualCoannihilator = ⨅ j, (f j).ker := by
  ext v
  rw [← SetLike.mem_coe, coe_dualCoannihilator_span]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, mem_iInf, LinearMap.mem_ker]

end Submodule
