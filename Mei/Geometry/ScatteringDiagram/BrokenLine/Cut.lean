/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Admissible.Truncate

/-!
# Cutting decorated rays between encounters

Cut an actual decorated ray inside any open segment and retain its incoming
piece, including the whole decoration on every retained segment. The discarded
encounters are the first entries in the backward itinerary. The cut keeps the
original incoming coefficient, source admission, crossing signs, normal velocities
and all wall and singular avoidance conditions. Degree changes with equal spatial
velocity and encounters with unchanged degree are retained.

This lifts `Convex.AdmissibleRayRealization.truncate` through whole homogeneous
histories, using `homogeneousHistoryStage_natAdd` to preserve their segment maps.
It supplies incoming decorated pieces for the last-change decomposition of
broken lines. The geometric cutting argument follows Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {m n : ℕ} {T : Fin (m + n) → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {velocity : Γ → V} {f : Fin (m + n) → V →L[ℝ] ℝ}
  {c : Fin (m + n) → ℝ} {ε : Fin (m + n) → SignType}
  {P : Fin (m + n) → Set V} {W : J → Set V} {S : K → Set V}
  {C : Set V} {Q : V}
  (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
  (t : ℝ)
  (hupper : t < r.2.parameter (Fin.natAdd m (0 : Fin (n + 1))))
  (hlower : ∀ j : Fin n, r.2.parameter (Fin.natAdd m j).succ < t)

/-- Cut off the final `m` encounters, retaining the incoming `n` encounters and
the original input. The cut lies in the open segment between the two blocks. -/
def truncate :
    DecoratedAdmissibleRay ℳ (fun j => T (Fin.natAdd m j)) p₀ a velocity
      (fun j => f (Fin.natAdd m j)) (fun j => c (Fin.natAdd m j))
      (fun j => ε (Fin.natAdd m j)) (fun j => P (Fin.natAdd m j))
      W S C (r.2.ray t) := by
  let p : Fin n → Γ := fun j => r.1.val (Fin.natAdd m j)
  have hs : ∀ j : Fin (n + 1),
      Fin.snoc (α := fun _ => Γ) r.1.val p₀ (Fin.natAdd m j) =
        Fin.snoc (α := fun _ => Γ) p p₀ j :=
    fun j => congrFun (Fin.snoc_comp_natAdd r.1.val p₀) j
  have hv : (fun j : Fin (n + 1) =>
      velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ (Fin.natAdd m j))) =
        fun j => velocity (Fin.snoc (α := fun _ => Γ) p p₀ j) :=
    funext fun j => congrArg velocity (hs j)
  refine ⟨⟨p, (mem_decoratedHistorySupport ..).mpr ⟨?_, ?_⟩⟩,
    (r.2.truncate t hupper hlower).congrVelocity hv⟩
  · have hne := r.decoration_ne_zero (Fin.natAdd m (0 : Fin (n + 1)))
    simpa only [decoration_def, homogeneousHistoryStage_natAdd,
      homogeneousHistoryStage_zero] using hne
  · intro j
    have hnorm := r.normal_velocity_eq (Fin.natAdd m j)
    have hsign := r.crossing_sign (Fin.natAdd m j)
    rw [Fin.succ_natAdd, hs] at hnorm
    exact ⟨hnorm, hsign⟩

/-- The retained degree history is precisely the incoming block. -/
@[simp]
theorem history_truncate :
    (r.truncate t hupper hlower).1.val = fun j => r.1.val (Fin.natAdd m j) := (rfl)

/-- Cutting a decorated ray uses the canonical geometric truncation. -/
@[simp]
theorem ray_truncate :
    (r.truncate t hupper hlower).2.ray = r.2.ray.truncate t := by
  simp only [truncate, AdmissibleRayRealization.ray_congrVelocity,
    AdmissibleRayRealization.ray_truncate]

/-- The complete retained path agrees with the original path after translating
time by the cut parameter. This includes the entire incoming half-line. -/
theorem truncate_apply (s : ℝ) (hs : s ≤ 0) :
    (r.truncate t hupper hlower).2.ray s = r.2.ray (s + t) := by
  rw [ray_truncate, FiniteAffineRay.truncate_apply _ _ hs]

/-- Retained encounter times are translated by the cut parameter. -/
@[simp]
theorem parameter_truncate_succ (j : Fin n) :
    (r.truncate t hupper hlower).2.parameter j.succ =
      r.2.parameter (Fin.natAdd m j).succ - t := by
  simp only [truncate, AdmissibleRayRealization.parameter_congrVelocity,
    AdmissibleRayRealization.parameter_truncate_succ]

/-- Each retained encounter stays at its original geometric position. -/
theorem truncate_ray_parameter_succ (j : Fin n) :
    (r.truncate t hupper hlower).2.ray
        ((r.truncate t hupper hlower).2.parameter j.succ) =
      r.2.ray (r.2.parameter (Fin.natAdd m j).succ) := by
  simpa only [truncate, AdmissibleRayRealization.ray_congrVelocity,
    AdmissibleRayRealization.parameter_congrVelocity] using
      r.2.truncate_ray_parameter_succ t hupper hlower j

/-- Every retained segment keeps its whole decoration, including the final
segment at the new endpoint and the incoming segment. -/
@[simp]
theorem decoration_truncate (j : Fin (n + 1)) :
    (r.truncate t hupper hlower).decoration j =
      r.decoration (Fin.natAdd m j) := by
  simp only [decoration_def, history_truncate, homogeneousHistoryStage_natAdd]

end Mei.DecoratedAdmissibleRay
