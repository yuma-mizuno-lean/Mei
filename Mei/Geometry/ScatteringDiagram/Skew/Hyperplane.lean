/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.LieAlgebra
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane

/-!
# Full hyperplane diagrams with skew labels

If the form vanishes on the unfrozen sublattice, in particular for the zero form, the positive
skew Lie algebra is abelian. Hence every directed diagram whose walls are full affine
hyperplanes and whose labels lie in that positive skew Lie algebra is consistent, whatever
internal grading, positive monoid and spatial map are put on it. This applies uniformly to the
original, principal, projected principal and principal cylinder wall spaces of a skew lattice
datum.

The bracket convention and the skew Lie algebra follow Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2. We use
`SkewLatticeDatum.isLieAbelian_positiveLieAlgebra_of_forall_form_eq_zero` and
`DirectedDiagram.consistent_of_isLieAbelian_of_full`.
-/

public section

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N R V : Type*} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V] (D : SkewLatticeDatum N)
  {Γ Λ ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ] [DecidableEq Γ]
  {d : PositiveDegrees D.unfrozen} {e : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R
    (SkewLieAlgebra.positiveLieAlgebra (D.coefficientForm R) (D.isAlt_coefficientForm R) d)}
  [GradedLieAlgebra ℒ] [IsPositiveGrading e ℒ] {ρ : Γ →+ Λ} {H : DirectedWallSpaces ρ ℒ}
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- If the form vanishes on the unfrozen sublattice, every diagram of full affine hyperplanes
with skew labels is consistent, for any regrading and spatial map of the skew Lie algebra. This
covers the original, principal, projected principal and principal cylinder wall spaces. -/
theorem consistent_of_forall_form_eq_zero (hform : ∀ n m : D.unfrozen, D.form n m = 0)
    (F : DirectedDiagram (d := e) h H ι)
    (hfull : ∀ a, ∃ b : ℝ,
      (F.wall a).support = {v | h.realCharacter (F.wall a).normal v = b}) :
    F.Consistent :=
  have := D.isLieAbelian_positiveLieAlgebra_of_forall_form_eq_zero R (d := d) hform
  F.consistent_of_isLieAbelian_of_full hfull

end Mei.SkewLatticeDatum
