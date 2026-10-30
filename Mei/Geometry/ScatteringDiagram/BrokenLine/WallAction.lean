/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.History
public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Toric.Algebraic.DualLattice

/-!
# Decorated histories of actual wall actions

For finite shifted BCH actions of truncated wall labels, every surviving whole
coefficient history already preserves normal velocity. The existing decorated
history support therefore filters only by the crossing signs. Its weighted ray
evaluation can be computed from these histories and their full geometric
endpoint admission, without separately checking normal conservation.

The labels may already include an inverse or a product of commuting labels in
one wall group. No consistency or annihilation hypothesis is needed. Degrees
are relative to an arbitrary initial shift; velocities use the ambient degrees.
The full endpoint domain retains wall avoidance, singular avoidance and the
incoming source, and no genericity assumption is imposed.

This applies `DirectedWallSpaces.homogeneousHistory_shiftedBCHAction_normal_eq`
to `decoratedHistorySupport` and `decoratedRayEvaluation`. The whole-component
and crossing conventions follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.DirectedWallSpaces

open Mei.Convex

variable {Γ : Type} {Λ R L M V J K : Type*}
  [AddCommGroup Γ] [AddCommGroup Λ] [DecidableEq Γ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ} {ℒ : Γ → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
  (w : Fin n → SupportedRay d) (m : Fin n → Λ →+ ℤ)
  (hg : ∀ j, BCHGroup.log (g j) ∈ H.truncatedRayLieSubalgebra (w j) (m j) k)
  (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
  (ε : Fin n → SignType)

local notation "𝓝" => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "T" => fun j => LinearEquiv.toLinearMap
  (ModuleFiltration.truncatedBCHAction (d.shiftedLieFiltration ℒ ℳ p)
    d ℒ k (g j))
local notation "v" => fun r => i (ρ (p + r))
local notation "f" => fun j => h.continuousRealCharacter (m j)

include hg

/-- A surviving shifted BCH wall history preserves the real normal velocity
at every encounter, with velocities computed from the ambient degrees. -/
theorem continuousRealCharacter_shiftedBCHAction_normal_eq
    (r : Fin n → Γ) (hne : homogeneousHistory 𝓝 T r a ≠ 0) (j : Fin n) :
    f j (v (r j)) = f j (v (Fin.snoc (α := fun _ => Γ) r r₀ j.succ)) := by
  have he := H.homogeneousHistory_shiftedBCHAction_normal_eq ℳ p k g w m hg r r₀ a hne j
  simpa only [h.continuousRealCharacter_apply, h.realCharacter_apply] using
    congrArg (Int.cast : ℤ → ℝ) he

/-- Actual wall actions impose no extra normal-velocity filter on nonzero
homogeneous histories. Only the prescribed crossing signs remain to be checked. -/
theorem mem_decoratedHistorySupport_shiftedBCHAction_iff (r : Fin n → Γ) :
    r ∈ decoratedHistorySupport 𝓝 T r₀ a v f ε ↔
      homogeneousHistory 𝓝 T r a ≠ 0 ∧
        ∀ j, SignType.sign (f j (v (r j))) = ε j := by
  rw [mem_decoratedHistorySupport]
  constructor
  · exact fun hr => ⟨hr.1, fun j => (hr.2 j).2⟩
  · rintro ⟨hne, hs⟩
    exact ⟨hne, fun j =>
      ⟨H.continuousRealCharacter_shiftedBCHAction_normal_eq ℳ p h k g w m hg r₀ a r hne j,
        hs j⟩⟩

open Classical in
/-- Compute the weighted ray evaluation of actual wall actions using only
survival, the signed crossings and full geometric endpoint admission. Every
selected output is a whole homogeneous component, including unchanged degrees. -/
theorem decoratedRayEvaluation_shiftedBCHAction_eq_sum
    (c : Fin n → ℝ) (P : Fin n → Set V) (W : J → Set V)
    (S : K → Set V) (C : Set V) (Q : V) :
    decoratedRayEvaluation 𝓝 T r₀ a v f c ε P W S C Q =
      ∑ r ∈ homogeneousHistorySupport 𝓝 T (a : (d.shiftedLieFiltration ℒ ℳ p).quotient k),
        if (∀ j, SignType.sign (f j (v (r j))) = ε j) ∧
            Q ∈ admissibleBackwardDomain f c
              (fun j => v (Fin.snoc (α := fun _ => Γ) r r₀ j)) P W S C
        then homogeneousHistory 𝓝 T r a else 0 := by
  rw [decoratedRayEvaluation_eq_sum_homogeneousHistory]
  apply Finset.sum_congr rfl
  intro r hr
  have hne := (mem_homogeneousHistorySupport ..).mp hr
  simp only [H.continuousRealCharacter_shiftedBCHAction_normal_eq
    ℳ p h k g w m hg r₀ a r hne, true_and]

end Mei.DirectedWallSpaces
