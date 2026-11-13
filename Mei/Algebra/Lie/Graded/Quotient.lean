/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Quotient
public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import Mei.Algebra.PositiveDegrees.Subquotient
public import Mathlib.Algebra.Lie.Quotient

/-!
# Lie gradings on homogeneous quotients

A homogeneous Lie ideal gives a Lie grading on the quotient. We use
`TauCeti.InternalGrading.quotient` for the underlying module grading, whose pieces are the
images of the original pieces. The new instance supplies the Lie bracket compatibility on
that same carrier and decomposition.

Use `TauCeti.InternalGrading.ofDecomposition` to start from Mathlib's `GradedLieAlgebra`
interface. The existing `quotient_piece`, `mem_quotient_piece_iff`, and
`decompose_quotient_mk` describe the pieces and compute their projections. In particular,
vanishing pieces remain zero, so positive support passes to the quotient via
`TauCeti.IsPositiveGrading.quotient`. Its degree ideals are the images of the original
degree ideals.
-/

public section

namespace LieIdeal

variable {R L : Type*} {ι : Type} [CommRing R] [LieRing L] [LieAlgebra R L]
  [DecidableEq ι] [AddCommMonoid ι]

/-- The cutoff ideal of a homogeneous quotient is the image of the original cutoff ideal.
In particular, passage to a homogeneous quotient preserves the positive degree filtration. -/
theorem degreeIdeal_eq_map (I : LieIdeal R L) (G : TauCeti.InternalGrading R L ι)
    [GradedLieAlgebra G.piece] (d : TauCeti.PositiveDegrees ι)
    [TauCeti.IsPositiveGrading d G.piece]
    (hI : DirectSum.SetLike.IsHomogeneous G.piece I.toSubmodule) (k : ℕ) :
    -- Install positivity explicitly at the module quotient / Lie quotient interface.
    let := TauCeti.IsPositiveGrading.quotient d G I.toSubmodule hI
    d.degreeIdeal (G.quotient I.toSubmodule hI).piece k =
      (d.degreeIdeal G.piece k).map I.mkQ := by
  apply LieSubmodule.toSubmodule_injective
  rw [TauCeti.PositiveDegrees.degreeIdeal_toSubmodule,
    LieIdeal.coe_map_of_surjective I.surjective_mkQ,
    TauCeti.PositiveDegrees.degreeIdeal_toSubmodule, funext (G.quotient_piece I.toSubmodule hI)]
  exact d.degreeSubmodule_map G.piece I.mkQ.toLinearMap k

end LieIdeal
