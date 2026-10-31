/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Shifted
public import Mei.LinearAlgebra.GradedCorrespondence.Terminal

/-!
# Terminal common lifts for ordinary BCH walls

For an ordinary wall acting on a finite shifted coefficient module, the terminal
sums of incoming coefficients from the two sides have a unique common linear
lift through its graph correspondence. Positive normal degrees cross by the
inverse label on the negative side, negative normal degrees cross by the label
on the positive side, and tangent coefficients agree on both sides.

The normal sign is evaluated on the ambient degree `p + r`, even though the
finite quotient is graded by relative degrees `r`. Inputs may mix both sides
and tangent coefficients. The label is the signed transport from the negative
to the positive side; for the original cooriented wall label, take its inverse.
Combined labels are allowed.

This instantiates `GradedCorrespondence.existsUnique_terminalGraphLift` using
wall annihilation on the actual finite BCH action, without assuming the terminal
identity. It is the coefficient part of a single ordinary-face resolution;
matching these branches to a geometric degeneration is independent.
The wall action convention follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.DirectedWallSpaces

variable {Γ : Type} {Λ R L M E : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]
  [IsWallAnnihilating H ℳ] (p : Γ)
  [AddCommMonoid E] [Module R E]
  {w : SupportedRay d} {m : Λ →+ ℤ} {k : ℕ}
  (g : d.truncatedGroup ℒ k)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "𝓝" => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "θ" => ModuleFiltration.truncatedBCHAction (d.shiftedLieFiltration ℒ ℳ p) d ℒ k g
local notation "weight" => fun r => m (ρ (p + r))

/-- The independently formed terminal chamber sums for a finite ordinary wall
have a unique common lift, linear in any incoming parameter module. No
nonvanishing or one-sided support hypothesis on the incoming map is required. -/
theorem existsUnique_shiftedBCH_terminalGraphLift
    (hg : BCHGroup.log g ∈ H.truncatedRayLieSubalgebra w m k)
    (α : E →ₗ[R] (F).quotient k) :
    ∃! l : E →ₗ[R] (F).quotient k,
      (GradedCorrespondence.graph 𝓝 𝓝 θ).left.comp l =
        (GradedCorrespondence.terminalGraphLift 𝓝 θ weight).comp α ∧
      (GradedCorrespondence.graph 𝓝 𝓝 θ).right.comp l =
        (GradedCorrespondence.terminalGraphRight 𝓝 θ weight).comp α := by
  apply GradedCorrespondence.existsUnique_terminalGraphLift
  intro r a hr
  exact H.shiftedBCHAction_eq_self_of_normal_eq_zero ℳ p hg a.property hr

end Mei.DirectedWallSpaces
