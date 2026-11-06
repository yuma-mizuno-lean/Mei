/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion

/-!
# The raising part of an endomorphism at finite filtration order

Fix a decreasing module filtration `F` and an order `k`. The *raising part* of an
endomorphism `e` of the order-`k` quotient `F.quotient k` is its difference `e - 1`
from the identity. For a wall-crossing action this is the correction that a crossing
adds to the coefficient it transports; the backward-ray recursions of
`Mei.ModuleProbe` read their blocks off it.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {F : ModuleFiltration R M}

/-- The raising part of an endomorphism: its difference from the identity. -/
def raisingPart {k : ℕ} (e : Module.End R (F.quotient k)) : Module.End R (F.quotient k) :=
  e - 1

theorem raisingPart_apply {k : ℕ} (e : Module.End R (F.quotient k)) (x : F.quotient k) :
    F.raisingPart e x = e x - x := by
  rw [raisingPart, LinearMap.sub_apply, Module.End.one_apply]

end Mei.ModuleFiltration
