/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Node.Basic

/-!
# Scalar towers for nodal algebras

The nodal algebra over an algebra `S` is itself an algebra over the original
coefficient semiring `R`. The scoped instances in `TauCeti.NodeAlgebra` use the
composite scalar map. They allow the chamber maps and incoming lifts to retain
their linear structures over `R` when `S` is a tangential coefficient algebra.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

variable (R S : Type*) [CommSemiring R] [CommRing S] [Algebra R S] (a : S)

/-- The scalar algebra on a nodal algebra over an `R`-algebra. -/
scoped instance scalarAlgebra : Algebra R (NodeAlgebra S a) :=
  Algebra.compHom _ (algebraMap R S)

/-- The composite scalar action is compatible with the nodal coefficient algebra. -/
scoped instance scalarTower : IsScalarTower R S (NodeAlgebra S a) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

end TauCeti.NodeAlgebra
