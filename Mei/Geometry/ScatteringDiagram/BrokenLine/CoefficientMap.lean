/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay

/-!
# Coefficient change of decorated ray evaluations

For one fixed signed encounter itinerary on a fixed spatial base, an
intertwining homogeneous coefficient map commutes with the weighted evaluation
of actual decorated admissible rays. The degree map may identify infinitely many
degrees, provided it preserves spatial velocities. Source histories with the
same target history contribute additively; cancellation may delete a target ray.
Conversely every surviving target ray has a source refinement with exactly the
same geometric path and encounter parameters and a surviving final decoration.

These statements retain all wall and singular avoidance and incoming-source
conditions. They hold over semirings without injectivity, rational geometry or
endpoint genericity. They concern a fixed itinerary; comparison over all
itineraries and inverse limits is separate.

The proofs combine `homogeneousHistory_map_eq_sum` and
`map_sum_ite_homogeneousHistory` with the geometric domains and whole-component
decorations of `DecoratedAdmissibleRay`. Weighted regrading follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2), and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Definitions 3.1–3.3
(arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M N Γ Δ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [DecidableEq Γ] [DecidableEq Δ]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ → Δ)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : Fin n → Module.End R M) (U : Fin n → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (p₀ : Γ) (a : ℳ p₀) (v : Γ → V) (w : Δ → V)
  (hv : ∀ p, v p = w (σ p))
  (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (ε : Fin n → SignType)
  (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

include hT hv

/-- Weighted evaluation of the actual decorated rays commutes with an
intertwining coefficient regrading preserving velocities. Merging histories are
summed, so no injectivity or noncancellation hypothesis is imposed. -/
theorem map_decoratedRayEvaluation :
    r (decoratedRayEvaluation ℳ T p₀ a v f c ε P W S C Q) =
      decoratedRayEvaluation 𝓝 U (σ p₀) ⟨r a, hr p₀ a a.property⟩
        w f c ε P W S C Q := by
  classical
  let E (q : Fin n → Δ) : Prop :=
    (∀ j, f j (w (q j)) = f j (w (Fin.snoc (α := fun _ => Δ) q (σ p₀) j.succ)) ∧
      SignType.sign (f j (w (q j))) = ε j) ∧
    Q ∈ admissibleBackwardDomain f c (fun j => w (Fin.snoc (α := fun _ => Δ) q (σ p₀) j)) P W S C
  have hdir (p : Fin n → Γ) :
      (fun j => v (Fin.snoc (α := fun _ => Γ) p p₀ j)) =
        (fun j => w (Fin.snoc (α := fun _ => Δ) (σ ∘ p) (σ p₀) j)) := by
    simp only [← Fin.comp_snoc, Function.comp_apply, hv]
  have hpoint (p : Fin n → Γ) (j : Fin (n + 1)) := congrFun (hdir p) j
  calc
    _ = r (∑ p ∈ homogeneousHistorySupport ℳ T (a : M),
        if E (σ ∘ p) then homogeneousHistory ℳ T p a else 0) := by
      congr 1
      rw [decoratedRayEvaluation_eq_sum_homogeneousHistory]
      apply Finset.sum_congr rfl
      intro p _
      simp only [E, Function.comp_apply, ← hv, ← hpoint]
    _ = _ := by
      rw [decoratedRayEvaluation_eq_sum_homogeneousHistory]
      -- The abstract predicate and the expanded conjunction use different
      -- decidability instances. Compare their conditional summands explicitly.
      convert map_sum_ite_homogeneousHistory ℳ 𝓝 r σ hr T U hT E (a : M) using 1
      · congr 1
        apply Finset.sum_congr rfl
        intro p _
        split_ifs <;> rfl
      · apply Finset.sum_congr rfl
        intro q _
        split_ifs <;> rfl

/-- Every surviving target ray has a source degree refinement with a surviving
image decoration, the identical geometric ray, and identical encounter times.
This does not assert a map from individual source rays to target rays: their
images may cancel when their degree histories merge. -/
theorem DecoratedAdmissibleRay.exists_coefficient_refinement
    (β : DecoratedAdmissibleRay 𝓝 U (σ p₀) ⟨r a, hr p₀ a a.property⟩
      w f c ε P W S C Q) :
    ∃ α : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q,
      (∀ j, σ (α.1.val j) = β.1.val j) ∧ r (α.decoration 0) ≠ 0 ∧
        α.2.ray = β.2.ray ∧ α.2.parameter = β.2.parameter := by
  have hβ : homogeneousHistory 𝓝 U β.1.val (r a) ≠ 0 := by
    simpa only [DecoratedAdmissibleRay.decoration_zero] using β.decoration_ne_zero 0
  obtain ⟨p, hp, hn⟩ := exists_homogeneousHistory_ne_zero_of_map_ne_zero
    ℳ 𝓝 r σ hr T U hT β.1.val hβ
  have hdir (j : Fin (n + 1)) :
      v (Fin.snoc (α := fun _ => Γ) p p₀ j) = w (Fin.snoc (α := fun _ => Δ) β.1.val (σ p₀) j) := by
    rw [hv, ← Function.comp_apply (f := σ), Fin.comp_snoc, Function.comp_def, funext hp]
  have hsupport : p ∈ decoratedHistorySupport ℳ T p₀ a v f ε := by
    rw [mem_decoratedHistorySupport]
    refine ⟨fun hz => hn (by simp [hz]), fun j => ?_⟩
    have hout : v (p j) = w (β.1.val j) := (hv _).trans (congrArg w (hp j))
    rw [hout, hdir]
    exact ⟨β.normal_velocity_eq j, β.crossing_sign j⟩
  refine ⟨⟨⟨p, hsupport⟩, β.2.congrVelocity (funext hdir).symm⟩,
    hp, ?_, AdmissibleRayRealization.ray_congrVelocity ..,
    AdmissibleRayRealization.parameter_congrVelocity ..⟩
  simpa only [DecoratedAdmissibleRay.decoration_zero] using hn

end Mei
