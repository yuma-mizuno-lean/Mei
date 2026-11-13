/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
public import TauCeti.LinearAlgebra.SymmetricAlgebra.TotalDegree

/-!
# Total degree of pure symmetric tensors

Multiplication into the symmetric algebra preserves the total degree of the factors.
-/

public section

namespace Mei.SymmetricAlgebra

open scoped TensorProduct

variable {Γ : Type*} {R : Type} {M : Type*} [AddCommMonoid Γ]
  [CommSemiring R] [AddCommMonoid M] [Module R M] (ℳ : Γ → Submodule R M)

/-- Multiplication of a pure symmetric tensor retains the total degree of its
homogeneous factors in the symmetric algebra. -/
theorem toSymmetricAlgebra_tprod_mem_homogeneousSubmodule
    {n : ℕ} (degree : Fin n → Γ) (x : Fin n → M) (hx : ∀ i, x i ∈ ℳ (degree i)) :
    TauCeti.SymmetricPower.toSymmetricAlgebra R M n (⨂ₛ[R] i, x i) ∈
      TauCeti.SymmetricAlgebra.totalDegreeSubmodule ℳ (∑ i, degree i) := by
  rw [TauCeti.SymmetricPower.toSymmetricAlgebra_tprod]
  exact SetLike.prod_mem_graded _ _ _ fun i _ =>
    TauCeti.SymmetricAlgebra.ι_mem_totalDegreeSubmodule ℳ (hx i)

end Mei.SymmetricAlgebra
