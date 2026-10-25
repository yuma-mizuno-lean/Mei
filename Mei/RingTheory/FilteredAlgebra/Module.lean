/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Basic

/-!
# The underlying module filtration of a filtered algebra

Restricting scalars in the ideals of an algebra filtration gives a module filtration over
the coefficient semiring. This allows results on filtered modules to apply to coefficient
algebras without losing their original ideal filtration. In particular, the quotient
representation of a filtration-raising Lie action can be used on the original quotient rings.
-/

public section

namespace Mei.AlgFiltration

variable (R : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (F : AlgFiltration A)

/-- The ideal filtration viewed as submodules over the coefficient semiring. -/
abbrev toModuleFiltration : ModuleFiltration R A where
  submodule k := (F.ideal k).restrictScalars R
  antitone := fun _ _ h => Submodule.restrictScalars_mono R (F.antitone h)
  zero_eq_top := by simp

/-- Each module filtration term is the scalar restriction of the original ideal. -/
@[simp]
theorem toModuleFiltration_submodule (k : ℕ) :
    (F.toModuleFiltration R).submodule k = (F.ideal k).restrictScalars R := (rfl)

end Mei.AlgFiltration
