/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Connected components of homeomorphic spaces

A homeomorphism `e : X ≃ₜ Y` induces a bijection between the connected components of `X`
and of `Y`, sending the component of a point `x` to the component of `e x`.
-/

public section

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism induces a bijection of connected components. -/
def connectedComponentsEquiv (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv := ConnectedComponents.surjective_coe.forall.2 fun x => by
    simp [Continuous.connectedComponentsMap_mk]
  right_inv := ConnectedComponents.surjective_coe.forall.2 fun y => by
    simp [Continuous.connectedComponentsMap_mk]

/-- The bijection of connected components sends the component of a point to the component of
its image. -/
@[simp]
theorem connectedComponentsEquiv_mk (e : X ≃ₜ Y) (x : X) :
    e.connectedComponentsEquiv (ConnectedComponents.mk x) = ConnectedComponents.mk (e x) :=
  (rfl)

/-- The inverse bijection sends the component of a point to the component of its image
under the inverse homeomorphism. -/
@[simp]
theorem connectedComponentsEquiv_symm_mk (e : X ≃ₜ Y) (y : Y) :
    e.connectedComponentsEquiv.symm (ConnectedComponents.mk y) =
      ConnectedComponents.mk (e.symm y) :=
  (rfl)

end Homeomorph
