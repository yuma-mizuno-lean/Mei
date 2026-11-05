/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Completion
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit

/-!
# Module structure on the shifted direct limit of quantum coefficients

Instances for the direct limit of the shifted quantum coefficients, stated for the quantum grading
`grade q β` so that they are found directly rather than through the generic direct limit
construction.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

instance : AddCommMonoid (d.ShiftedDirectLimit (grade q β)) := inferInstance

instance : Module R (d.ShiftedDirectLimit (grade q β)) := inferInstance

end Mei.QuantumMonoidAlgebra
