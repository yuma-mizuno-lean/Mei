/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Finsupp
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Completed expansions in a basis

A filtration on the scalar ring induces a coefficientwise filtration on any free
module with a chosen basis. Its completion has unique expansions with completed
scalar coefficients and finite support modulo every filtration term.

This transports `ModuleFiltration.finsuppCompletionEquiv` through `Basis.repr`.
-/

public section

noncomputable section

namespace Module.Basis

variable {ι : Type*}

section Semiring

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
  (b : Basis ι R V) (F : Mei.ModuleFiltration R R)

/-- The coefficientwise filtration of a module in a chosen basis. -/
def coefficientFiltration : Mei.ModuleFiltration R V where
  submodule k := ((F.finsupp ι).submodule k).comap b.repr.toLinearMap
  antitone _ _ h := Submodule.comap_mono ((F.finsupp ι).antitone h)
  zero_eq_top := by simp

/-- An element lies in a basis filtration term precisely when each coefficient does. -/
@[simp]
theorem mem_coefficientFiltration_submodule (k : ℕ) (x : V) :
    x ∈ (b.coefficientFiltration F).submodule k ↔ ∀ i, b.repr x i ∈ F.submodule k := by
  rw [coefficientFiltration, Submodule.mem_comap, Mei.ModuleFiltration.mem_finsupp_submodule]
  rfl

end Semiring

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
  (b : Basis ι R V) (F : Mei.ModuleFiltration R R)

/-- Completed basis expansions are exactly the families of completed scalars
with finite support at each order. -/
def completedCoefficientsEquiv : (b.coefficientFiltration F).completion ≃ₗ[R]
    F.restrictedFamilies ι :=
  ((b.coefficientFiltration F).completionEquiv (F.finsupp ι) b.repr (fun _ => rfl)).trans
    (F.finsuppCompletionEquiv ι)

/-- The completed coefficient expansion agrees with the original basis coordinates. -/
@[simp]
theorem completedCoefficientsEquiv_of (x : V) (i : ι) :
    (b.completedCoefficientsEquiv F ((b.coefficientFiltration F).of x)).val i =
      F.of (b.repr x i) := by
  have h := (b.coefficientFiltration F).completionEquiv_of (F.finsupp ι) b.repr
    (fun _ => rfl) x
  exact (congrArg (fun y => (F.finsuppCompletionEquiv ι y).val i) h).trans
    ((F.finsuppCompletionEquiv_apply ι ((F.finsupp ι).of (b.repr x)) i).trans
      (F.completedCoefficient_of ι (b.repr x) i))

section Ideal

variable {S W : Type*} [CommRing S] [AddCommGroup W] [Module S W]
  (c : Basis ι S W)

/-- Ideal multiples of a free module are detected by its basis coefficients. -/
theorem mem_ideal_smul_top_iff_repr_mem (I : Ideal S) (x : W) :
    x ∈ I • (⊤ : Submodule S W) ↔ ∀ i, c.repr x i ∈ I := by
  rw [← c.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [← Finsupp.linearCombination_apply, c.repr_linearCombination] using ha
  · intro hx
    exact ⟨c.repr x, hx, c.linearCombination_repr x⟩

end Ideal

end Module.Basis
