/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Basis
public import Mei.RingTheory.FilteredAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The coefficient-ideal filtration of a monoid algebra

For an ideal `I` of a commutative semiring `R`, the `k`-th term of the coefficient filtration of
`R[M]` consists of the elements all of whose coefficients lie in `I ^ k`. It is the direct sum of
copies of the `I`-adic filtration of `R`, indexed by the exponents, and is a filtration of `R[M]`
as an `R`-module. Unlike the monomial filtrations of `AddSubmonoid.monoidAlgebraFiltration`, it
does not depend on the exponents.
-/

public section

noncomputable section

namespace Ideal

variable {R : Type*} [CommSemiring R] (I : Ideal R) (M : Type*)

/-- The filtration of `R[M]` by the powers of a coefficient ideal: the `k`-th term consists of
the elements with all coefficients in `I ^ k`. -/
def coeffFiltration : Mei.ModuleFiltration R (AddMonoidAlgebra R M) :=
  (AddMonoidAlgebra.basis M R).coefficientFiltration
    ((Mei.AlgFiltration.ofIdeal I).toModuleFiltration R)

/-- Membership in the coefficient filtration is coefficientwise. -/
@[simp]
theorem mem_coeffFiltration_submodule {k : ℕ} {x : AddMonoidAlgebra R M} :
    x ∈ (coeffFiltration I M).submodule k ↔ ∀ m, x.coeff m ∈ I ^ k := by
  rw [coeffFiltration, Module.Basis.mem_coefficientFiltration_submodule]
  simp only [Mei.AlgFiltration.ofIdeal_ideal, Submodule.restrictScalars_mem]
  rfl

/-- A monomial lies in the coefficient filtration exactly when its coefficient lies in the
corresponding power of the ideal. -/
@[simp 1100]
theorem single_mem_coeffFiltration_submodule {k : ℕ} {m : M} {c : R} :
    AddMonoidAlgebra.single m c ∈ (coeffFiltration I M).submodule k ↔ c ∈ I ^ k := by
  classical
  rw [mem_coeffFiltration_submodule]
  refine ⟨fun h => by simpa using h m, fun h m' => ?_⟩
  by_cases hm : m = m'
  · simpa [hm] using h
  · simp [AddMonoidAlgebra.coeff_single, hm]

/-- If the ideal vanishes at order `r`, so does the coefficient filtration. -/
theorem coeffFiltration_submodule_eq_bot {r : ℕ} (hr : I ^ r = ⊥) :
    (coeffFiltration I M).submodule r = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  refine AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
  simpa [hr] using (mem_coeffFiltration_submodule (I := I) (M := M)).1 hx m

end Ideal
