/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Nilpotent

/-!
# Nilpotence of Lie subalgebras and quotients

Subalgebras and quotients of nilpotent Lie algebras are nilpotent. These instances
allow constructions on nilpotent Lie algebras to apply to their subalgebras and
quotients without additional hypotheses. They use Mathlib's transport of
nilpotence along injective and surjective Lie homomorphisms.
-/

public section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing.IsNilpotent L]

/-- A subalgebra of a nilpotent Lie algebra is nilpotent. -/
instance LieSubalgebra.instIsNilpotent (K : LieSubalgebra R L) : LieRing.IsNilpotent K :=
  Function.Injective.lieAlgebra_isNilpotent (f := K.incl) Subtype.val_injective

/-- A quotient of a nilpotent Lie algebra is nilpotent. -/
instance LieIdeal.instQuotientIsNilpotent (I : LieIdeal R L) :
    LieRing.IsNilpotent (L ⧸ I) :=
  I.surjective_mkQ.lieAlgebra_isNilpotent
