/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Twisted monoid algebras over rings

The twisted monoid algebra inherits a ring structure over a commutative ring.
This explicitly specializes `Subalgebra.toRing` to the subalgebra of twisted
translations constructed by `TauCeti.twistedMonoidAlgebra`, so instance search
can find the additive inverses without unfolding that subalgebra.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {R G : Type*} [CommRing R] [Monoid G]
  (α : G → G → Rˣ) [IsFactorSet α]

/-- The inherited ring structure on the algebra of twisted translations. -/
noncomputable instance instRing : Ring (twistedMonoidAlgebra R G α) :=
  Subalgebra.toRing (R := R) (A := Module.End R (G →₀ R))
    (twistedMonoidAlgebra R G α)

end TauCeti.TwistedMonoidAlgebra
