/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Regular

/-!
# The endpoint field of probe coefficients

Outside a finite exceptional arrangement of base endpoints `Q`, the point `(Q, 0)`
of the probe slice is regular and every incident wall is transverse to the upward
probe direction. The coefficient extracted from the short upward crossing at `(Q, 0)`
is therefore a field on generic base endpoints. It is characterized by the upward
crossing label `exp(-F(Q))`, independently of the length of the short crossing,
commutes with truncation, and agrees for equivalent diagrams on their common
generic locus. No consistency is involved.

The construction uses `ModuleProbe.regular_of_isGeneric` and the crossing
coefficient API. The field is the coefficient extracted from the module probe in
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (DirectedWallSpaces)

open Set Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)

local notation "v" => (0, j 1)
local notation "F" => d.shiftedFiltration ℳ p

/-- The relative order-`k` probe coefficient at a generic endpoint `Q`, extracted
from the upward crossing at the zero-slice point `(Q, 0)`. -/
def coefficientField (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) : (F).quotient k :=
  verticalCoefficient d ℳ p ℒ H h h' D k (Q, 0)
    (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)

/-- The endpoint field is the vertical coefficient at the zero-slice point. -/
theorem coefficientField_def (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) :
    coefficientField d ℳ p ℒ H h h' D k Q hQ =
      verticalCoefficient d ℳ p ℒ H h h' D k (Q, 0)
        (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ) := (rfl)

/-- The negative exponential of the field is the upward crossing label at the
zero-slice point, including simultaneous module-wall crossings. -/
theorem moduleBCHInclusion_neg_coefficientField [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
    (k : ℕ) (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) :
    moduleBCHInclusion d ℳ p ℒ k
        (Multiplicative.ofAdd (-coefficientField d ℳ p ℒ H h h' D k Q hQ)) =
      D.combinedLabel (k + 1) (Q, 0) v (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ) :=
  moduleBCHInclusion_neg_verticalCoefficient d ℳ p ℒ H h h' D k _ _
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)

/-- The upward crossing at the zero-slice point uniquely characterizes the field. -/
theorem coefficientField_eq_iff [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
    (k : ℕ) (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (a : (F).quotient k) :
    coefficientField d ℳ p ℒ H h h' D k Q hQ = a ↔
      moduleBCHInclusion d ℳ p ℒ k (Multiplicative.ofAdd (-a)) =
        D.combinedLabel (k + 1) (Q, 0) v (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ) :=
  verticalCoefficient_eq_iff d ℳ p ℒ H h h' D k _ _
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ) a

/-- Lowering the relative cutoff preserves the endpoint field on the common
generic locus. The arrangements themselves need not be nested. -/
@[simp]
theorem transition_coefficientField {k l : ℕ} (hkl : k ≤ l)
    (Q : V) (hQk : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQl : (coefficientArrangement d ℳ p ℒ H h h' D l).IsGeneric Q) :
    (F).transition hkl (coefficientField d ℳ p ℒ H h h' D l Q hQl) =
      coefficientField d ℳ p ℒ H h h' D k Q hQk :=
  transition_verticalCoefficient d ℳ p ℒ H h h' D hkl _ _ _

/-- Equivalent diagrams give the same endpoint field on their common generic locus,
independently of their indexed wall presentations. -/
theorem coefficientField_eq_of_levelEquivalent {κ : Type*}
    (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) κ) (k : ℕ) (hDD' : D.LevelEquivalent D' (k + 1))
    (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQ' : (coefficientArrangement d ℳ p ℒ H h h' D' k).IsGeneric Q) :
    coefficientField d ℳ p ℒ H h h' D k Q hQ =
      coefficientField d ℳ p ℒ H h h' D' k Q hQ' :=
  verticalCoefficient_eq_of_levelEquivalent d ℳ p ℒ H h h' D D' hDD' _ _ _
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D' k Q hQ')

end Mei.ModuleProbe
