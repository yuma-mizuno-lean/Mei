/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Completion.Basic
public import Mei.Algebra.Lie.Graded.Truncation.Basic

/-!
# Degree completions of positively graded Lie algebras

The degree completion is the Lie algebra of compatible finite-degree truncations.
It uses the module-completion carrier with the quotient-wise Lie bracket from
`LieIdeal.completion`. Projections, the canonical map, extensionality and the
universal lift are available through that general completion API.
-/

public section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The Lie algebra of compatible finite-degree truncations. -/
abbrev completedLie := LieIdeal.completion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

end Mei.PositiveDegrees

