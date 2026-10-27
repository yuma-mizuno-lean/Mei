/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Base change of characters annihilating a vector

For a finite free module `M` and a flat coefficient algebra `S`, scalar extension
identifies the dual vectors annihilating `v : M` with the `S`-valued linear maps
annihilating `v`. In particular, scalar-extended integral tangent characters can
be realized as coefficient-valued characters, including when `v` is zero or
nonprimitive. This is the comparison needed to realize formal homogeneous
coefficients as logarithmic derivations.

We use `IsBaseChange.linearMapRight` for the full character module and
`LinearMap.tensorKerEquiv` for its evaluation kernel. These are Mathlib's
base-change theorems; the resulting equivalence does not choose a basis.
The application to integral homogeneous coefficients follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(i).
-/

public section

noncomputable section

namespace Module.Dual

open TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module R M]

variable [Module.Free R M] [Module.Finite R M]

-- The usual base-change equivalence for the full character module.
local notation "E" =>
  IsBaseChange.equiv (IsBaseChange.linearMapRight M (IsBaseChange.linearMap R S))

private theorem eval_baseChange (v : M) (x : S ⊗[R] Dual R M) :
    E x v = AlgebraTensorModule.rid R S S
      (AlgebraTensorModule.lTensor S S (eval R M v) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all
  | tmul s m =>
    rw [IsBaseChange.equiv_tmul]
    simp [Algebra.smul_def, mul_comm]

private def evalKerEquiv (v : M) :
    (AlgebraTensorModule.lTensor S S (eval R M v)).ker ≃ₗ[S]
      (LinearMap.applyₗ' (R := R) (M₂ := S) S v).ker := by
  let p := (AlgebraTensorModule.lTensor S S (eval R M v)).ker
  let q := (LinearMap.applyₗ' (R := R) (M₂ := S) S v).ker
  have hpq : p = q.comap (E).toLinearMap := by
    ext x
    simp only [p, q, Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_coe,
      LinearMap.applyₗ'_apply_apply]
    rw [eval_baseChange]
    exact (AlgebraTensorModule.rid R S S).map_eq_zero_iff.symm
  exact (LinearEquiv.ofEq p _ hpq).trans ((E).ofSubmodule' q)

variable [Module.Flat R S]

/-- Scalar extension of the dual vectors annihilating `v` is the module of
`S`-valued linear maps annihilating `v`. -/
def evalKerBaseChangeEquiv (v : M) :
    S ⊗[R] (eval R M v).ker ≃ₗ[S] (LinearMap.applyₗ' (R := R) (M₂ := S) S v).ker :=
  (LinearMap.tensorKerEquiv S S (eval R M v)).trans (evalKerEquiv R S v)

/-- A pure tensor evaluates by multiplying the extended character by its coefficient. -/
@[simp]
theorem evalKerBaseChangeEquiv_tmul (v w : M) (s : S) (m : (eval R M v).ker) :
    (evalKerBaseChangeEquiv R S v (s ⊗ₜ[R] m)).val w =
      s * algebraMap R S (m.val w) := by
  simp [evalKerBaseChangeEquiv, evalKerEquiv, IsBaseChange.equiv_tmul]

end Module.Dual
