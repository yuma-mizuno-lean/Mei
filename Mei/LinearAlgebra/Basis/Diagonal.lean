/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Linear maps that are diagonal in a pair of bases

If a linear map sends each vector of one basis to a scalar multiple of the vector with the same
index in a second basis, then it multiplies each coordinate by that scalar. No finiteness of the
index type is needed, so this applies to monomial bases of infinite rank.
-/

public section

namespace Module.Basis

/-- A linear map sending `b i` to `s i • b' i` multiplies the `i`-th coordinate by `s i`. -/
theorem repr_apply_of_apply_eq_smul {ι R M M' : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (b : Basis ι R M) (b' : Basis ι R M') {g : M →ₗ[R] M'} {s : ι → R}
    (hg : ∀ i, g (b i) = s i • b' i) (x : M) (i : ι) :
    b'.repr (g x) i = s i * b.repr x i := by
  classical
  have h : (Finsupp.lapply i).comp (b'.repr.toLinearMap.comp g) =
      s i • (Finsupp.lapply i).comp b.repr.toLinearMap :=
    b.ext fun j => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, map_smul, repr_self,
        LinearMap.smul_apply, Finsupp.lapply_apply, Finsupp.single_apply, smul_eq_mul]
      split_ifs with hij <;> simp [hij]
  exact LinearMap.congr_fun h x

end Module.Basis
