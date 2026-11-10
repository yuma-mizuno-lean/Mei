/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Module.Primitive

/-!
# Primitive vectors from coprime coefficients

We use `TauCeti.IsPrimitive`, defined by an integer-valued functional taking value one.
A combination `p • b i + q • b j` of two distinct basis vectors with coprime coefficients is
primitive (`Module.Basis.isPrimitive_zsmul_add_zsmul`), and so is a pair `(p, q)` of coprime
integers in `ℤ × ℤ` (`Prod.isPrimitive_mk_of_isCoprime`).
-/

public section

namespace Module.Basis

variable {ι M : Type*} [AddCommGroup M] [Module ℤ M]

/-- A combination of two distinct basis vectors with coprime coefficients is primitive. -/
theorem isPrimitive_zsmul_add_zsmul (b : Basis ι ℤ M) {i j : ι} (hij : i ≠ j) {p q : ℤ}
    (hpq : IsCoprime p q) : TauCeti.IsPrimitive (p • b i + q • b j) := by
  obtain ⟨u, v, huv⟩ := hpq
  refine TauCeti.isPrimitive_def.mpr ⟨u • b.coord i + v • b.coord j, ?_⟩
  simpa [hij, hij.symm, mul_comm] using huv

end Module.Basis

/-- A pair of coprime integers is a primitive vector of `ℤ × ℤ`. -/
theorem Prod.isPrimitive_mk_of_isCoprime {p q : ℤ} (hpq : IsCoprime p q) :
    TauCeti.IsPrimitive ((p, q) : ℤ × ℤ) := by
  obtain ⟨u, v, huv⟩ := hpq
  exact TauCeti.isPrimitive_def.mpr ⟨u • LinearMap.fst ℤ ℤ ℤ + v • LinearMap.snd ℤ ℤ ℤ,
    by simpa using huv⟩
