/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison.Stable
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Cylinder.Equivalence
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension.Equivalence
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Stable

/-!
# Independence of ray sums from the wall presentation

Two equivalent consistent base diagrams may present the same scattering diagram by
different wall families, for instance after subdividing supports or merging coincident
walls. Their probe fields agree by `extendedCoefficientField_eq_of_levelEquivalent_base`.

The actual weighted sums of decorated rays through the two presentations, with the whole
space as incoming source, then agree at every endpoint where both sums are locally constant.
The comparison goes through the independently constructed relative completion of the probe
and its probe field, and never compares the broken lines of the two presentations. The
wall families, their encounter itineraries and their decorated types differ between the
presentations; only the total sums are compared.

The probe construction follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
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
  (B : DirectedDiagram (d := d) h H κ) (B' : DirectedDiagram (d := d) h H κ')

variable [Module.Free ℤ Γ]

/-- The weighted sums of actual decorated rays are independent of the wall presentation.
For equivalent presentations `B` and `B'` of a consistent diagram, and an incoming
homogeneous coefficient `b`, the total sums over all rays through the walls of `B` and
through the walls of `B'`, with the whole space as incoming source, agree at every endpoint
allowed for both presentations where each sum is locally constant. -/
theorem cutoffWallEventEvaluation_eq_of_equivalent (hB : B.Consistent) (hBB' : B.Equivalent B')
    (K : ℕ) (b : (d.shiftedQuotientGrading ℳ p K).piece 0) {x : V}
    (hx : x ∈ stableWallEventLocus d ℳ p ℒ H h B K b)
    (hx' : x ∈ stableWallEventLocus d ℳ p ℒ H h B' K b) :
    cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) b univ x =
      cutoffWallEventEvaluation d ℳ p ℒ H h B' K K (Nat.le_refl K) b univ x := by
  have h₀ : TauCeti.Toric.IsIntegralLattice (Int.castAddHom ℝ) :=
    TauCeti.Toric.isIntegralLattice_castAddHom
  obtain ⟨η, -, P, hP, -, -⟩ := exists_isRelativeOutgoingCompletion_probe d ℳ p ℒ H h h₀ hB
    (d.shiftedQuotientComponent ℳ p p K (by simp) b)
  rw [mem_stableWallEventLocus] at hx hx'
  have hcomp := hP.isOutgoingCompletion_initialDiagram
  have hPc := (P.consistent_iff.mp hcomp.consistent) (K + 1)
  have hBc := (B.consistent_iff.mp hB) K
  have hBc' := (B'.consistent_iff.mp (hBB'.consistent hB)) K
  have hBK := (DirectedDiagram.equivalent_iff _ _).mp
    (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
      d ℳ p ℒ H h h₀ B _ P hP) K
  have hBK' := hBK.trans
    (((DirectedDiagram.equivalent_iff _ _).mp hBB' K).cylinderDiagram d ℳ p ℒ H h h₀)
  have hout : ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ P.active (K + 1) →
      (p + n.val, 1) ∈ (P.wall (.inr c)).ray.rayDegrees → (P.wall (.inr c)).Outgoing :=
    fun _ c _ _ => hcomp.outgoing_inr c
  rw [← extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq d ℳ p ℒ H h h₀ B
      _ P B hcomp.wall_inl K hBc hPc hBK hout b rfl ⟨x, hx.1⟩ hx.2,
    ← extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq d ℳ p ℒ H h h₀ B
      _ P B' hcomp.wall_inl K hBc' hPc hBK' hout b rfl ⟨x, hx'.1⟩ hx'.2]
  exact extendedCoefficientField_eq_of_levelEquivalent_base d ℳ p ℒ H h h₀ P B B' K
    ((DirectedDiagram.equivalent_iff _ _).mp hBB' K) hBc hBc' hPc hBK _ _ rfl

end Mei.ModuleProbe
