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
