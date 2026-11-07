/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuity of linear contact parameters

The height difference divided by a fixed normal velocity varies continuously
with the base point. This gives continuity of the parameter at which a
transverse line meets a level hyperplane, for use in contact stability arguments.
-/

public section

namespace ContinuousLinearMap

/-- The contact-parameter formula for a fixed linear functional and direction
depends continuously on the base point. This holds even when the normal velocity
is zero, since division by a fixed scalar is continuous. -/
theorem continuousAt_contactTime {K V X : Type*} [DivisionRing K] [TopologicalSpace K]
    [IsTopologicalAddGroup K] [SeparatelyContinuousMul K]
    [AddCommMonoid V] [Module K V] [TopologicalSpace V] [TopologicalSpace X]
    (ν : V →L[K] K) {c : K} {v : V} {x : X → V} {Q : X}
    (hx : ContinuousAt x Q) : ContinuousAt (fun Y => (c - ν (x Y)) / ν v) Q :=
  (continuousAt_const.sub (ν.continuous.continuousAt.comp hx)).div_const _

end ContinuousLinearMap
