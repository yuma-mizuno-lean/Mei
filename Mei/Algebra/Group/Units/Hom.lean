/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Units.Hom

/-!
# Multiplicative maps and integer powers of units

Multiplicative maps preserve integer powers of units, expressed using the induced map on units.
This lets monoid-valued maps act on such powers without requiring inverses in the ambient monoid.
-/

public section

namespace Mei

/-- A multiplicative map sends an integer power of a unit to the same power of its image. -/
theorem map_units_zpow {M N F : Type*} [Monoid M] [Monoid N]
    [FunLike F M N] [MonoidHomClass F M N] (f : F) (u : Mˣ) (k : ℤ) :
    f ↑(u ^ k) = ↑(Units.map (f : M →* N) u ^ k) := by
  rw [← map_zpow, Units.coe_map, MonoidHom.coe_ofClass]

end Mei
