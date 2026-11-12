/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Basic

/-!
# Powers in multiplicative ideal filtrations

Taking powers multiplies the filtration order.
-/

public section

namespace TauCeti.AlgFiltration

variable {A : Type*} [Semiring A] (F : AlgFiltration A)

/-- Powers multiply filtration orders. -/
theorem pow_mem {a : ℕ} {x : A} (hx : x ∈ F.ideal a) (n : ℕ) :
    x ^ n ∈ F.ideal (n * a) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using F.mul_mem ih hx

end TauCeti.AlgFiltration
