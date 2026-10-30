/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Images of coefficient semirings in additive monoid algebras

An additive map preserves the images of coefficient semirings when it does so on
single monomials. The proof uses Mathlib's `AddMonoidAlgebra.induction_linear`.
-/

public section

namespace AddMonoidAlgebra

variable {A A' R S M M' : Type*} [Semiring A] [Semiring A'] [Semiring R] [Semiring S]
  [AddMonoid M] [AddMonoid M']

/-- An additive map between monoid algebras sends the image `ι(A)[M]` of the coefficients
`A` into the image `ι'(A')[M']` as soon as it does so on the monomials `ι(a) z^m`. -/
theorem map_mem_rangeS_mapRingHom (ι : A →+* R) (ι' : A' →+* S) (f : R[M] →+ S[M'])
    (hf : ∀ (m : M) (a : A), f (single m (ι a)) ∈ (mapRingHom M' ι').rangeS)
    {x : R[M]} (hx : x ∈ (mapRingHom M ι).rangeS) :
    f x ∈ (mapRingHom M' ι').rangeS := by
  obtain ⟨y, rfl⟩ := hx
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => simpa only [map_add] using add_mem hy hz
  | single m a => simpa only [mapRingHom_single] using hf m a

end AddMonoidAlgebra
