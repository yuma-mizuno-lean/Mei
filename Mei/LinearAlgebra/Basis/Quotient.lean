/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Bases after discarding coordinates

If a submodule consists exactly of vectors whose coordinates on `s` vanish,
the quotient has the surviving basis vectors, indexed by `s`, as a basis.
The quotient coordinates are the original coordinates restricted to `s`.
This describes degree truncations without any field or finite-rank assumption.

We use Mathlib's `Finsupp.lsubtypeDomain`, `LinearMap.quotKerEquivOfSurjective`
and `Basis.ofRepr`.
-/

public noncomputable section

namespace Module.Basis

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (b : Basis ι R M) (U : Submodule R M) (s : Set ι)
  (hU : ∀ x, x ∈ U ↔ ∀ i ∈ s, b.repr x i = 0)

/-- The quotient basis obtained by retaining exactly the coordinates indexed by `s`. -/
def quotientOfCoordinates : Basis s R (M ⧸ U) := by
  classical
  let f := (Finsupp.lsubtypeDomain s).comp b.repr.toLinearMap
  have hf : Function.Surjective f := by
    intro x
    exact ⟨b.repr.symm x.extendDomain, by
      simp [f, Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_extendDomain]⟩
  have hker : U = LinearMap.ker f := by
    ext x
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_eq_zero_iff']
    exact hU x
  exact Basis.ofRepr ((Submodule.quotEquivOfEq U _ hker).trans
    (f.quotKerEquivOfSurjective hf))

/-- Quotient coordinates read the same surviving coordinates on representatives. -/
@[simp]
theorem quotientOfCoordinates_repr_mk (x : M) (i : s) :
    (b.quotientOfCoordinates U s hU).repr (Submodule.Quotient.mk x) i =
      b.repr x i := by
  classical
  -- The first-isomorphism equivalence and coordinate restriction both compute on representatives.
  rfl

/-- Every surviving basis vector is the class of its original basis vector. -/
@[simp]
theorem quotientOfCoordinates_apply (i : s) :
    b.quotientOfCoordinates U s hU i = Submodule.Quotient.mk (b i) := by
  classical
  apply (b.quotientOfCoordinates U s hU).repr.injective
  ext j
  simp [Basis.repr_self, Finsupp.single_apply, Subtype.ext_iff]

end Module.Basis
