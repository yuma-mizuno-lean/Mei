/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.ZeroDirection
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient

/-!
# Stationary components of finite shifted-quotient ray evaluations

The finite weighted evaluation has zero ambient component in every stationary
absolute degree different from its incoming degree, for arbitrary linear
propagation maps. The spatial velocity of relative degree `n` is the velocity of
absolute degree `p + n`. This supplies the finite vanishing result used by
completed evaluations, while allowing stationary incoming coefficients.

We combine `DecoratedAdmissibleRay.velocity_ne_zero_of_pos` with the inherited
shifted quotient grading and `PositiveDegrees.shiftedQuotientComponent_eq_zero_of_mem`.
The stationary-output convention follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
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

end Mei.PositiveDegrees
