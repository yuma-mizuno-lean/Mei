/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Decreasing filtrations of modules

A `ModuleFiltration` is a decreasing family of submodules starting at the whole
module. Order `k` retains the quotient by the submodule at `k + 1`.
The same family on order-dual natural numbers carries Mathlib's `IsFiltration`.
Compatibility with a ring filtration can be imposed separately using
`IsModuleFiltration`; it is not needed to construct the module completion.
Scalar restriction acts termwise and preserves the underlying filtration sets.
-/

public section

namespace Mei

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- A decreasing filtration of a module, with zeroth term the whole module. -/
@[ext]
structure ModuleFiltration where
  /-- The submodule of elements of order at least `k`. -/
  submodule : ℕ → Submodule R M
  /-- Higher orders give smaller submodules. -/
  antitone : Antitone submodule
  /-- Every element has order at least zero. -/
  zero_eq_top : submodule 0 = ⊤

namespace ModuleFiltration

attribute [simp] zero_eq_top

variable {R M} (F : ModuleFiltration R M)

/-- The decreasing family, indexed increasingly by order-dual natural numbers. -/
def filtration (k : ℕᵒᵈ) : Submodule R M := F.submodule k.ofDual

@[simp]
lemma filtration_toDual (k : ℕ) : F.filtration (OrderDual.toDual k) = F.submodule k :=
  (rfl)

instance : IsFiltration F.filtration (fun k => F.submodule (k.ofDual + 1)) where
  mono := fun _ _ h => F.antitone h
  is_le h := F.antitone (Nat.succ_le_of_lt h)
  is_sup _ k h := h (OrderDual.toDual (k.ofDual + 1)) (Nat.lt_succ_self _)

section Semiring

variable (R : Type*) {S M : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module S M] [Module R M] [SMul R S] [IsScalarTower R S M]
  (F : ModuleFiltration S M)

/-- Restrict the scalars in every term of a module filtration. -/
abbrev restrictScalars : ModuleFiltration R M where
  submodule k := (F.submodule k).restrictScalars R
  antitone := fun _ _ h => Submodule.restrictScalars_mono R (F.antitone h)
  zero_eq_top := by simp

@[simp]
lemma restrictScalars_submodule (k : ℕ) :
    (F.restrictScalars R).submodule k = (F.submodule k).restrictScalars R :=
  (rfl)

@[simp]
lemma restrictScalars_self : F.restrictScalars S = F := by
  ext k
  simp

end Semiring

end ModuleFiltration
end Mei
