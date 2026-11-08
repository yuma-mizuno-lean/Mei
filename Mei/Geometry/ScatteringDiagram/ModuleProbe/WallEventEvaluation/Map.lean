/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation
public import Mei.Algebra.Lie.Graded.Shifted.Map

/-!
# Coefficient maps of actual simultaneous-event ray sums

A homogeneous equivariant coefficient map commutes with the weighted evaluation
of the actual rays of a fixed directed diagram. Both sides use the same geometric
event inventory, even when the map kills an incoming coefficient or an entire
decoration. The coefficient cutoff may be smaller than the geometric cutoff.
No consistency, endpoint genericity, or injectivity is required.

In particular, evaluating an operator-valued ray sum gives the corresponding
ordinary ray sum, including inputs for which whole decorations vanish.
The whole-component interpretation follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Definition 2.10 and §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Λ V ι : Type*} {Γ : Type} {M N L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  (p : Γ) (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ 𝓝]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  {ρ : Γ →+ Λ} (W : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h W ι)
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝓝 q).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅x, f a⁆)

local notation "fₖ" => d.quotientCoefficientMap ℳ 𝓝 p f hf

include hequiv

/-- Coefficient specialization intertwines the signed simultaneous-event
propagation maps, with no injectivity assumption. -/
theorem map_wallEventPropagation (k K : ℕ) (hkK : k ≤ K)
    (e : WallEvent (B.active K)) (x : (d.shiftedFiltration ℳ p).quotient k) :
    fₖ k (wallEventPropagation d ℳ p ℒ W h B k K hkK e x) =
      wallEventPropagation d 𝓝 p ℒ W h B k K hkK e (fₖ k x) := by
  simp only [wallEventPropagation_apply]
  exact d.quotientCoefficientMap_truncatedBCHAction ℳ 𝓝 p ℒ f hf hequiv k _ x

/-- The whole actual weighted ray sum specializes by mapping its incoming
coefficient. Decorations whose images vanish contribute zero;
all encounters and the full incoming source region remain unchanged. -/
theorem map_cutoffWallEventEvaluation (k K : ℕ) (hkK : k ≤ K)
    (a : (d.shiftedQuotientGrading ℳ p k).piece 0) (C : Set V) (Q : V) :
    fₖ k (cutoffWallEventEvaluation d ℳ p ℒ W h B k K hkK a C Q) =
      cutoffWallEventEvaluation d 𝓝 p ℒ W h B k K hkK
        ⟨fₖ k a, d.quotientCoefficientMap_mem_shiftedQuotientGrading
          ℳ 𝓝 p f hf a.property⟩ C Q := by
  simp only [cutoffWallEventEvaluation_eq_cutoffDecoratedEvaluation]
  -- Compare the original ray fibers using equivariance of the finite BCH actions.
  apply map_cutoffDecoratedEvaluation
  intro e
  exact LinearMap.ext fun x => map_wallEventPropagation
    d ℳ 𝓝 p ℒ W h B f hf hequiv k K hkK e x

end Mei.ModuleProbe
