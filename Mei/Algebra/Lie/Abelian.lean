/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Abelian

/-!
# The abelian Lie algebra of a module

`Mei.AbelianLie V` equips an additive commutative group with the zero Lie bracket.
Every module structure on `V` makes this synonym a Lie algebra over the same ring.
The linear equivalence `Mei.AbelianLie.linearEquiv` forgets the zero bracket.
-/

public section

noncomputable section

namespace Mei

/-- An additive commutative group, regarded as a Lie ring with zero bracket. -/
def AbelianLie (V : Type*) : Type _ := V

namespace AbelianLie

variable {V : Type*} [AddCommGroup V]

instance : AddCommGroup (AbelianLie V) := inferInstanceAs (AddCommGroup V)

instance : LieRing (AbelianLie V) where
  __ := (inferInstance : AddCommGroup (AbelianLie V))
  bracket _ _ := 0
  add_lie _ _ _ := (add_zero _).symm
  lie_add _ _ _ := (add_zero _).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (add_zero _).symm

/-- The bracket on the abelian Lie ring vanishes. -/
@[simp]
theorem lie_eq_zero (a b : AbelianLie V) : ⁅a, b⁆ = 0 := rfl

instance : IsLieAbelian (AbelianLie V) where
  trivial := lie_eq_zero

variable (R : Type*) [CommRing R] [Module R V]

instance : Module R (AbelianLie V) := inferInstanceAs (Module R V)

instance : LieAlgebra R (AbelianLie V) where
  __ := (inferInstance : Module R (AbelianLie V))
  lie_smul r _ _ := (smul_zero r).symm

/-- Forget the zero Lie bracket and recover the original module. -/
def linearEquiv : AbelianLie V ≃ₗ[R] V := LinearEquiv.refl R _

end AbelianLie
end Mei
