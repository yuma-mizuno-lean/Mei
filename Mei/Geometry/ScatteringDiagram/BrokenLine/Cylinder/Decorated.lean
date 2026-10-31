/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Cylinder.Admissible
public import Mei.Geometry.ScatteringDiagram.BrokenLine.CoefficientMap

/-!
# Decorated cylinder lifts and weighted projection

For a fixed signed encounter itinerary, prescribing the forgotten velocity of
each degree and the forgotten endpoint identifies cylinder rays with projected
rays carrying the same contributing degree histories. All segment decorations,
encounter times, incoming tails and avoidance conditions are retained, including
coefficient changes with unchanged projected velocity.

Combining this equivalence with an intertwining coefficient regrading proves the
weighted projection identity. Several cylinder histories may refine one projected
history, and cancellation may remove that projected history. Nevertheless every
surviving projected ray has a contributing cylinder refinement. The refinements
at a fixed itinerary are finite, even for infinite degree fibers. These statements
concern a fixed itinerary; uniform bounds across itineraries and passage to
completed theta sections are separate.

We combine `Convex.admissibleRayCylinderEquiv`, whole homogeneous histories and
`map_decoratedRayEvaluation`. The weighted cylinder comparison follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2), and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Definitions 3.1–3.3
(arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei

open Set Mei.Convex

variable {R M Γ V W J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {n : ℕ} (T : Fin n → Module.End R M) (p₀ : Γ) (a : ℳ p₀)
  (v : Γ → V) (w : Γ → W)
  (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (ε : Fin n → SignType)
  (P : Fin n → Set V) (A : J → Set V) (S : K → Set V) (C : Set V)

local notation "F" => fun j => ContinuousLinearMap.comp (f j) (ContinuousLinearMap.fst ℝ V W)
local notation "vw" => fun p => (v p, w p)
local notation "Pc" => fun j => Prod.fst ⁻¹' P j
local notation "Ac" => fun j => Prod.fst ⁻¹' A j
local notation "Sc" => fun j => Prod.fst ⁻¹' S j
local notation "Dc" Q => DecoratedAdmissibleRay ℳ T p₀ a vw F c ε Pc Ac Sc (Prod.fst ⁻¹' C) Q
local notation "D" Q => DecoratedAdmissibleRay ℳ T p₀ a v f c ε P A S C Q

/-- Each contributing projected degree history has exactly one cylinder lift
with the prescribed forgotten endpoint. Projection keeps the crossing signs and
normal velocities as well as every coefficient decoration. -/
def decoratedRayCylinderEquiv (Q : V × W) : (Dc Q) ≃ (D (Q.1)) :=
  Equiv.sigmaCongr
    (Equiv.subtypeEquivRight fun p => by
      simp only [mem_decoratedHistorySupport, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst'])
    (fun p => admissibleRayCylinderEquiv f c
      (fun j => v (Fin.snoc (α := fun _ => Γ) p.val p₀ j))
      (fun j => w (Fin.snoc (α := fun _ => Γ) p.val p₀ j)) P A S C Q)

/-- Cylinder projection retains the entire degree history, including degrees
with the same projected velocity. -/
@[simp]
theorem decoratedRayCylinderEquiv_history (Q : V × W) (r : Dc Q) :
    (decoratedRayCylinderEquiv ℳ T p₀ a v w f c ε P A S C Q r).1.val = r.1.val := (rfl)

/-- Every segment keeps its whole homogeneous decoration under projection. -/
@[simp]
theorem decoratedRayCylinderEquiv_decoration (Q : V × W) (r : Dc Q) (j : Fin (n + 1)) :
    (decoratedRayCylinderEquiv ℳ T p₀ a v w f c ε P A S C Q r).decoration j =
      r.decoration j := by
  simp only [DecoratedAdmissibleRay.decoration_def, decoratedRayCylinderEquiv_history]

/-- Projection identifies the entire realized paths, including their incoming tails. -/
@[simp]
theorem decoratedRayCylinderEquiv_ray (Q : V × W) (r : Dc Q) :
    (decoratedRayCylinderEquiv ℳ T p₀ a v w f c ε P A S C Q r).2.ray =
      r.2.ray.map (AffineMap.fst : V × W →ᵃ[ℝ] V) :=
  admissibleRayCylinderEquiv_ray f c _ _ P A S C Q r.2

/-- Every actual encounter parameter is preserved by cylinder projection. -/
@[simp]
theorem decoratedRayCylinderEquiv_parameter (Q : V × W) (r : Dc Q) :
    (decoratedRayCylinderEquiv ℳ T p₀ a v w f c ε P A S C Q r).2.parameter =
      r.2.parameter :=
  admissibleRayCylinderEquiv_parameter f c _ _ P A S C Q r.2

/-- Cylinder lifting preserves finite weighted evaluation, with arbitrary
forgotten endpoint and without endpoint genericity or nonzero-velocity hypotheses. -/
@[simp]
theorem decoratedRayEvaluation_cylinder (Q : V × W) :
    decoratedRayEvaluation ℳ T p₀ a vw F c ε Pc Ac Sc (Prod.fst ⁻¹' C) Q =
      decoratedRayEvaluation ℳ T p₀ a v f c ε P A S C Q.1 := by
  classical
  rw [decoratedRayEvaluation_eq_sum_homogeneousHistory,
    decoratedRayEvaluation_eq_sum_homogeneousHistory]
  apply Finset.sum_congr rfl
  intro p _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    admissibleBackwardDomain_cylinder, mem_preimage]

section Regrading

variable {N Δ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq Δ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ → Δ)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  (U : Fin n → Module.End R N) (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (u : Δ → V) (hv : ∀ p, v p = u (σ p))

include hT hv

/-- Weighted projection groups all contributing cylinder refinements into the
whole projected decorations. It permits noninjective degree maps, vanished
coefficients and cancellation between refinements. -/
theorem map_decoratedRayEvaluation_cylinder (Q : V × W) :
    r (decoratedRayEvaluation ℳ T p₀ a vw F c ε Pc Ac Sc (Prod.fst ⁻¹' C) Q) =
      decoratedRayEvaluation 𝓝 U (σ p₀) ⟨r a, hr p₀ a a.property⟩
        u f c ε P A S C Q.1 := by
  rw [decoratedRayEvaluation_cylinder]
  exact map_decoratedRayEvaluation ℳ 𝓝 r σ hr T U hT p₀ a v u hv f c ε P A S C Q.1

/-- Every surviving projected ray comes from a cylinder degree refinement with
nonzero image decoration and exactly the same projected path and encounter times.
This is an existence statement: distinct source refinements can cancel. -/
theorem DecoratedAdmissibleRay.exists_cylinder_coefficient_refinement (Q : V × W)
    (β : DecoratedAdmissibleRay 𝓝 U (σ p₀) ⟨r a, hr p₀ a a.property⟩
      u f c ε P A S C Q.1) :
    ∃ α : Dc Q, (∀ j, σ (α.1.val j) = β.1.val j) ∧ r (α.decoration 0) ≠ 0 ∧
      α.2.ray.map (AffineMap.fst : V × W →ᵃ[ℝ] V) = β.2.ray ∧
        α.2.parameter = β.2.parameter := by
  obtain ⟨γ, hγ, hn, hpath, htime⟩ := β.exists_coefficient_refinement
    ℳ 𝓝 r σ hr T U hT p₀ a v u hv f c ε P A S C Q.1
  let e := decoratedRayCylinderEquiv ℳ T p₀ a v w f c ε P A S C Q
  refine ⟨e.symm γ, ?_, ?_, ?_, ?_⟩
  · have hh := decoratedRayCylinderEquiv_history ℳ T p₀ a v w f c ε P A S C Q (e.symm γ)
    rw [Equiv.apply_symm_apply] at hh
    simpa only [hh] using hγ
  · have hd := decoratedRayCylinderEquiv_decoration ℳ T p₀ a v w f c ε P A S C Q (e.symm γ) 0
    rw [Equiv.apply_symm_apply] at hd
    exact hd ▸ hn
  · rw [← decoratedRayCylinderEquiv_ray, Equiv.apply_symm_apply]
    exact hpath
  · rw [← decoratedRayCylinderEquiv_parameter, Equiv.apply_symm_apply]
    exact htime

end Regrading

end Mei
