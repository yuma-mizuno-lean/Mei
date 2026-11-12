/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.BaseChange.Basic
public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Examples

/-!
# Scalar extension of the horizontal line from `ℚ` to `ℝ`

Take the horizontal incoming line `{y = 0}` of `ℤ²` with wall function `1 + c z^{2e₁}` on the
even quadrant `2ℕe₁ + ℕe₂` (`RankTwoPolynomialInput.Examples.horizontalInput`), with a rational
coefficient `c`, so that its labels lie in the tropical vertex group over `ℚ`. Extending scalars
along `ℚ → ℝ` gives a diagram for the wall spaces `ℝ ⊗[ℚ] h_{n,m}` of `ℝ ⊗[ℚ] g`, whose wall is
supported on the line `{y = 0}`
(`DirectedDiagram.Examples.affineSpan_baseChange_incomingDiagram_support`) and
is consistent (`DirectedDiagram.Examples.consistent_baseChange_incomingDiagram`). The
extended single-wall diagram is an outgoing completion of the extended incoming wall
(`DirectedDiagram.Examples.isOutgoingCompletion_baseChange`), so the scattering class
over `ℝ` of the extended input is the class of the extended single-wall diagram
(`DirectedDiagram.Examples.scat_baseChange_eq_toClass`), by
`DirectedDiagram.scat_baseChange_eq_toClass`.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram.Examples

open RankTwoPolynomialInput RankTwoPolynomialInput.Examples PositiveDegrees.Examples

variable (c : horizontalInput.Variable → ℚ) {latticeMap : ℤ × ℤ →+ ℝ × ℝ}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- Over `ℝ`, the support of the wall of the extended horizontal line still spans the line
`{y = 0}`. -/
theorem affineSpan_baseChange_incomingDiagram_support (j : horizontalInput.IncomingIndex) :
    affineSpan ℝ (((horizontalInput.incomingDiagram h c).baseChange ℝ).wall j).support =
      horizontalLine h := by
  rw [baseChange_wall, DirectedWall.baseChange_support]
  exact affineSpan_incomingDiagram_support c h j

/-- Over `ℝ`, the extended horizontal line is consistent. -/
theorem consistent_baseChange_incomingDiagram :
    ((horizontalInput.incomingDiagram h c).baseChange ℝ).Consistent :=
  (incomingDiagram_consistent c h).baseChange ℝ

/-- Over `ℝ`, the extended single-wall diagram is an outgoing completion of the extended
horizontal line. -/
theorem isOutgoingCompletion_baseChange :
    IsOutgoingCompletion (fun j => ((horizontalInput.incomingDiagram h c).wall j).baseChange ℝ)
      ((completionDiagram c h).baseChange ℝ) :=
  (isOutgoingCompletion c h).baseChange ℝ

/-- The scattering class over `ℝ` of the extended horizontal line is the class of the extended
single-wall diagram. -/
theorem scat_baseChange_eq_toClass :
    ((horizontalInput.incomingDiagram h c).baseChange ℝ).Scat (by
      simpa only [baseChange_wall, DirectedWall.baseChange_support,
        DirectedWall.baseChange_normal] using horizontalInput.incomingDiagram_full h c) =
      ((completionDiagram c h).baseChange ℝ).toClass :=
  DirectedDiagram.scat_baseChange_eq_toClass ℝ _ (horizontalInput.incomingDiagram_full h c)
    (isOutgoingCompletion c h)

end Mei.DirectedDiagram.Examples
