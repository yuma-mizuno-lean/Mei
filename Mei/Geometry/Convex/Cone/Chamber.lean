/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Group.AddSubmonoid.Degree
public import TauCeti.Geometry.Convex.Cone.Chamber

/-!
# Hyperplane avoidance in strict dual chambers

The strict dual chambers from TauCeti avoid every hyperplane indexed by a
nonzero element of the additive monoid.
-/

public section

namespace AddSubmonoid

variable {M V : Type*} [AddCommMonoid M] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (P : AddSubmonoid M) (i : M →+ V)

/-- A positive chamber point avoids every hyperplane of a nonzero monoid element. -/
theorem apply_ne_zero_of_mem_positiveChamber {θ : V →L[ℝ] ℝ}
    (hθ : θ ∈ P.positiveChamber i) {n : M} (hn : n ∈ P) (hn0 : n ≠ 0) :
    θ (i n) ≠ 0 := ((P.mem_positiveChamber i).mp hθ n hn hn0).ne'

/-- A negative chamber point avoids every hyperplane of a nonzero monoid element. -/
theorem apply_ne_zero_of_mem_negativeChamber {θ : V →L[ℝ] ℝ}
    (hθ : θ ∈ P.negativeChamber i) {n : M} (hn : n ∈ P) (hn0 : n ≠ 0) :
    θ (i n) ≠ 0 := ((P.mem_negativeChamber i).mp hθ n hn hn0).ne

end AddSubmonoid
