/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Algebra
public import Mei.RingTheory.FilteredAlgebra.Completion
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Monomials and products in filtered algebra completions

Algebra automorphisms fix completed constants. Quotient representatives
compute projections of scalar multiples of products.
-/

public section

namespace TauCeti.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (F : AlgFiltration A)

/-- An algebra automorphism of the completion fixes the canonical images of scalars. -/
theorem algEquiv_toCompletion_algebraMap (e : F.completion ≃ₐ[R] F.completion) (r : R) :
    e (F.toCompletion (algebraMap R A r)) = F.toCompletion (algebraMap R A r) := by
  rw [toCompletion_algebraMap, AlgEquiv.commutes]

/-- An algebra automorphism of the completion of a monoid algebra `R[Q]` over its coefficient
ring `R` fixes the constants `z^0 c`. -/
theorem algEquiv_toCompletion_single_zero {Q : Type*} [AddMonoid Q]
    {F : TauCeti.AlgFiltration (AddMonoidAlgebra R Q)} (e : F.completion ≃ₐ[R] F.completion)
    (c : R) :
    e (F.toCompletion (AddMonoidAlgebra.single 0 c)) =
      F.toCompletion (AddMonoidAlgebra.single 0 c) := by
  have hc : (AddMonoidAlgebra.single 0 c : AddMonoidAlgebra R Q) =
      algebraMap R (AddMonoidAlgebra R Q) c := by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [hc]
  exact F.algEquiv_toCompletion_algebraMap e c

/-- In the completion of a monoid algebra `B[N]`, a monomial `c z^p` is the product of the
monomial `z^p` and the constant `c z^0`. -/
theorem toCompletion_single_eq_mul {B N : Type*} [Ring B] [AddMonoid N]
    (E : TauCeti.AlgFiltration (AddMonoidAlgebra B N)) (p : N) (c : B) :
    E.toCompletion (AddMonoidAlgebra.single p c) =
      E.toCompletion (AddMonoidAlgebra.single p 1) *
        E.toCompletion (AddMonoidAlgebra.single 0 c) := by
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_zero, one_mul]

/-- A projected scalar multiple of a product is computed from representatives of both factors. -/
theorem projection_smul_mul_of_projections {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (F : AlgFiltration A) (r : R) (u v : A) (a b : F.completion) (k : ℕ)
    (ha : F.projection k a = Ideal.Quotient.mk (F.ideal (k + 1)) u)
    (hb : F.projection k b = Ideal.Quotient.mk (F.ideal (k + 1)) v) :
    F.projection k (r • (a * b)) = Ideal.Quotient.mk (F.ideal (k + 1)) (r • (u * v)) := by
  have hs : F.projection k (r • (a * b)) = r • F.projection k (a * b) := by
    simpa only [AlgHom.toLinearMap_apply, projectionₐ_apply] using
      (F.projectionₐ (R := R) k).toLinearMap.map_smul r (a * b)
  rw [hs, map_mul, ha, hb, ← map_mul]
  exact ((Ideal.Quotient.mkₐ R (F.ideal (k + 1))).toLinearMap.map_smul _ _).symm

/-- A projected scalar multiple of a product is computed from any quotient representative. -/
theorem projection_smul_mul_of_projection {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (F : AlgFiltration A) (r : R) (u b : A) (a : F.completion) (k : ℕ)
    (hb : F.projection k a = Ideal.Quotient.mk (F.ideal (k + 1)) b) :
    F.projection k (r • (F.toCompletion u * a)) =
      Ideal.Quotient.mk (F.ideal (k + 1)) (r • (u * b)) :=
  F.projection_smul_mul_of_projections r u b (F.toCompletion u) a k
    (F.projection_toCompletion k u) hb

end TauCeti.AlgFiltration
