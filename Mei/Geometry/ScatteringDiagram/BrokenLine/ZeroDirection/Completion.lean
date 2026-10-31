/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.ZeroDirection
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Completion

/-!
# Stationary components of completed BCH ray evaluations

The completed weighted evaluation has zero component in every stationary
absolute degree different from its incoming degree. Here the spatial velocity
of relative degree `n` is the velocity of absolute degree `p + n`. This proves
vanishing for the actual sum over all encounter itineraries, at every cutoff
and in the shifted completion. Stationary incoming coefficients and nonzero
shifts with unchanged spatial velocity remain permitted.

We combine `DecoratedAdmissibleRay.velocity_ne_zero_of_pos` with the inherited
quotient grading and `PositiveDegrees.projection_completedBCHCutoffEvaluation`.
For the stationary-output case of the broken-line recursion, see Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

section General

variable {Γ : Type} {R M V J K : Type*}
  [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

local notation "G" => fun k : ℕ =>
  TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)

/-- Every finite shifted-quotient ray sum has zero ambient component in a
stationary degree different from its incoming degree, including for stationary
incoming data. -/
@[simp]
theorem shiftedQuotientComponent_cutoffDecoratedEvaluation_eq_zero_of_velocity_eq_zero
    (k : ℕ) (T : J → Module.End R ((d.shiftedFiltration ℳ p).quotient k)) (a : G k 0)
    {q : Γ} (hq : v q = 0) (hne : q ≠ p) (hk : d.degree (q - p) ≤ k) :
    d.shiftedQuotientComponent ℳ p q k hk
      (cutoffDecoratedEvaluation d (G k) T a (fun n => v (p + n))
        f c ε P W S C k Q) = 0 := by
  classical
  let := Fintype.ofFinite (CutoffDecoratedRay d (G k) T a
    (fun n => v (p + n)) f c ε P W S C k Q)
  rw [cutoffDecoratedEvaluation_def, map_sum]
  apply Finset.sum_eq_zero
  intro r _
  cases hl : r.itinerary.length with
  | zero =>
    have hi : (0 : Fin (r.itinerary.length + 1)) = Fin.last r.itinerary.length := by
      ext
      simp [hl]
    have hw : r.decoration = (a : (d.shiftedFiltration ℳ p).quotient k) := by
      rw [CutoffDecoratedRay.decoration_eq, ← r.realization.decoration_zero, hi,
        DecoratedAdmissibleRay.decoration_last]
    rw [hw]
    exact d.shiftedQuotientComponent_eq_zero_of_mem ℳ p a.property
      (by simpa using hne.symm) hk
  | succ n =>
    let j : Fin r.itinerary.length := ⟨0, by omega⟩
    have hv := r.realization.velocity_ne_zero_of_pos (by omega) j.castSucc
    have hdeg : p + r.realization.1.val j ≠ q := by
      intro he
      exact hv (by simpa only [Fin.snoc_castSucc, he] using hq)
    have hw : r.decoration ∈ G k (r.realization.1.val j) := by
      have hi : j.castSucc = 0 := by ext; rfl
      simpa only [hi, CutoffDecoratedRay.decoration_eq,
        DecoratedAdmissibleRay.decoration_zero] using r.realization.decoration_mem j
    exact d.shiftedQuotientComponent_eq_zero_of_mem ℳ p hw hdeg hk

end General

section BCH

variable {Γ : Type} {R L M V J K : Type*}
  [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

/-- The stationary-output vanishing law holds for homogeneous components of
the completed evaluation itself, without choosing a finite cutoff in the API. -/
@[simp]
theorem shiftedHomogeneousComponent_completedBCHCutoffEvaluation_eq_zero_of_velocity_eq_zero
    (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0)
    {q : Γ} (hq : v q = 0) (hne : q ≠ p) :
    d.shiftedHomogeneousComponent ℳ p q
      (d.completedBCHCutoffEvaluation ℒ ℳ p (fun n => v (p + n))
        f c ε P W S C Q g a) = 0 := by
  rw [d.shiftedHomogeneousComponent_eq ℳ p q (d.degree (q - p)).toNat
    (Int.self_le_toNat _), d.projection_completedBCHCutoffEvaluation]
  exact d.shiftedQuotientComponent_cutoffDecoratedEvaluation_eq_zero_of_velocity_eq_zero
    ℳ p v f c ε P W S C Q _ _ _ hq hne _

end BCH

end Mei.PositiveDegrees
