/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Extension of scalars and sums of submodules

Extension of scalars preserves arbitrary sums of submodules. This identifies
filtrations defined by sums of homogeneous pieces after a change of coefficients.
The span calculation is the module version of Tau Ceti's
`LieSubmodule.baseChange_iSup`.
-/

public section

namespace Submodule

variable {R M : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M]

/-- Extension of scalars preserves arbitrary sums of submodules. -/
@[simp]
theorem baseChange_iSup (S : Type*) [Semiring S] [Algebra R S]
    {ι : Sort*} (p : ι → Submodule R M) :
    (⨆ i, p i).baseChange S = ⨆ i, (p i).baseChange S := by
  rw [iSup_eq_span, baseChange_span, Set.image_iUnion, span_iUnion]
  simp only [baseChange_eq_span, map_coe]

end Submodule
