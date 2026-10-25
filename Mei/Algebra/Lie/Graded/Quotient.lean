/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Map
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
`Mei.IsPositiveGrading.quotient`. Its degree ideals are the images of the original
degree ideals.
-/

public section

namespace LieIdeal

variable {R L : Type*} {ι : Type} [CommRing R] [LieRing L] [LieAlgebra R L]
  [DecidableEq ι] [AddCommMonoid ι]

/-- The quotient by a homogeneous Lie ideal inherits the Lie grading on the images of the
homogeneous pieces, using the existing homogeneous module quotient grading. -/
noncomputable instance instGradedLieAlgebraQuotient (I : LieIdeal R L)
    (G : TauCeti.InternalGrading R L ι) [SetLike.GradedBracket G.piece G.piece]
    (hI : DirectSum.SetLike.IsHomogeneous G.piece I.toSubmodule) :
    GradedLieAlgebra (L := L ⧸ I) (G.quotient I.toSubmodule hI).piece where
  toDecomposition := inferInstance
  toGradedBracket := by
    -- The linear map in `LieIdeal.mkQ` is the module quotient map used by `G.quotient`.
    have hpieces : (G.quotient I.toSubmodule hI).piece =
        fun i ↦ (G.piece i).map I.mkQ.toLinearMap :=
      funext (G.quotient_piece I.toSubmodule hI)
    rw [hpieces]
    exact I.mkQ.gradedBracket_map G.piece

/-- The cutoff ideal of a homogeneous quotient is the image of the original cutoff ideal.
In particular, passage to a homogeneous quotient preserves the positive degree filtration. -/
theorem degreeIdeal_eq_map (I : LieIdeal R L) (G : TauCeti.InternalGrading R L ι)
    [GradedLieAlgebra G.piece] (d : Mei.PositiveDegrees ι)
    [Mei.IsPositiveGrading d G.piece]
    (hI : DirectSum.SetLike.IsHomogeneous G.piece I.toSubmodule) (k : ℕ) :
    -- Install positivity explicitly at the module quotient / Lie quotient interface.
    let := Mei.IsPositiveGrading.quotient d G I.toSubmodule hI
    d.degreeIdeal (G.quotient I.toSubmodule hI).piece k =
      (d.degreeIdeal G.piece k).map I.mkQ := by
  apply LieSubmodule.toSubmodule_injective
  rw [Mei.PositiveDegrees.degreeIdeal_toSubmodule,
    LieIdeal.coe_map_of_surjective I.surjective_mkQ,
    Mei.PositiveDegrees.degreeIdeal_toSubmodule, funext (G.quotient_piece I.toSubmodule hI)]
  exact d.degreeSubmodule_map G.piece I.mkQ.toLinearMap k

end LieIdeal
