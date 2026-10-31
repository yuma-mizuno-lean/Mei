/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

/-!
# Stationary output components of decorated ray sums

A transverse decorated ray with at least one encounter has nonzero spatial
velocity on every segment. Transversality gives this on the outgoing side of
each encounter, and conservation of normal velocity gives it on the incoming
tail. Consequently a stationary output degree different from the input cannot
occur, even when the input itself is stationary. Its component in the full
finite weighted evaluation vanishes.

These results concern absolute stationary directions, rather than degree shifts
with zero spatial projection: a nonzero shift preserving a nonzero velocity is
still allowed. They supply the stationary-output case in recursions comparing
probe fields with broken-line sums. The geometric conventions follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 and §3.3.3 (arXiv:1503.06183v5).

We use `DecoratedAdmissibleRay.normal_velocity_eq`, the transversality of its
actual admissible realization, and Mathlib's direct-sum homogeneous projections.
-/

public noncomputable section

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

namespace DecoratedAdmissibleRay

/-- A final decoration has zero component in every stationary degree other
than the incoming degree. Empty itineraries and stationary inputs are allowed. -/
theorem decompose_decoration_eq_zero_of_velocity_eq_zero
    (r : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q)
    {q : Γ} (hq : v q = 0) (hne : q ≠ p₀) :
    DirectSum.decompose ℳ (r.decoration 0) q = 0 := by
  apply Subtype.ext
  cases n with
  | zero =>
    have hi : (0 : Fin 1) = Fin.last 0 := rfl
    rw [hi, r.decoration_last]
    exact DirectSum.decompose_of_mem_ne ℳ a.property hne.symm
  | succ n =>
    have hv := r.velocity_ne_zero_of_pos (Nat.succ_pos n) 0
    have hdeg : r.1.val 0 ≠ q := by
      intro he
      exact hv (by simpa only [← Fin.castSucc_zero, Fin.snoc_castSucc, he] using hq)
    exact DirectSum.decompose_of_mem_ne ℳ (r.decoration_mem 0) hdeg

end DecoratedAdmissibleRay

/-- For a fixed encounter itinerary, the weighted sum has no stationary
output component distinct from the input. Cancellation is unrestricted. -/
@[simp]
theorem decompose_decoratedRayEvaluation_eq_zero_of_velocity_eq_zero
    {q : Γ} (hq : v q = 0) (hne : q ≠ p₀) :
    DirectSum.decompose ℳ
      (decoratedRayEvaluation ℳ T p₀ a v f c ε P W S C Q) q = 0 := by
  classical
  let := Fintype.ofFinite (DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q)
  rw [decoratedRayEvaluation_def]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply]
  exact Finset.sum_eq_zero fun r _ =>
    r.decompose_decoration_eq_zero_of_velocity_eq_zero hq hne

/-- Across all encounter itineraries, stationary relative degrees other than
zero have zero component in the actual cutoff weighted evaluation. No
assumption on the incoming velocity or the propagation maps is required. -/
@[simp]
theorem decompose_cutoffDecoratedEvaluation_eq_zero_of_velocity_eq_zero
    [AddCommGroup Γ] [Finite J] (d : PositiveDegrees Γ)
    (T : J → Module.End R M) (a : ℳ 0)
    (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
    (P W : J → Set V) (S : K → Set V) (C : Set V) (k : ℕ) (Q : V)
    {q : Γ} (hq : v q = 0) (hne : q ≠ 0) :
    DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q = 0 := by
  classical
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  rw [cutoffDecoratedEvaluation_def]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply]
  apply Finset.sum_eq_zero
  intro r _
  simpa only [CutoffDecoratedRay.decoration_eq, DecoratedAdmissibleRay.decoration_zero] using
    r.realization.decompose_decoration_eq_zero_of_velocity_eq_zero hq hne

end Mei
