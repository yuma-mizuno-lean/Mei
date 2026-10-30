/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

/-!
# Coefficient change across all cutoff encounter itineraries

A degree-preserving coefficient map intertwining the signed propagation maps
commutes with the weighted evaluation of the entire cutoff ray family. Rays
whose final decoration vanishes are discarded. The surviving source rays are
in bijection with target rays, preserving the encounter word, degree history,
geometric path and encounter times. No injectivity of the coefficient map or
endpoint genericity is required.

The construction uses `CutoffDecoratedRay` and its finite all-itinerary
inventory, together with `map_homogeneousHistory_of_injective`. Since the
degrees are fixed, no histories merge, and linear propagation ensures that a
vanished intermediate decoration cannot contribute later. This is the
coefficient-specialization comparison for whole-component broken lines of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definitions 3.1–3.3 (arXiv:1411.1394v2), and Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Definition 2.10 and
Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M N Γ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Γ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 p)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (U : J → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (a : ℳ 0) (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P W : J → Set V) (S : K → Set V) (C : Set V)
  (k : ℕ) (Q : V)

local notation "a'" => (Subtype.mk (r a) (hr 0 a a.property) : 𝓝 0)
local notation "Source" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
local notation "Target" => CutoffDecoratedRay d 𝓝 U a' v f c ε P W S C k Q

/-- Specialization identifies precisely the source rays whose whole final
coefficient survives with the target rays, over every encounter itinerary. -/
def cutoffDecoratedRayCoefficientEquiv : {β : Source // r β.decoration ≠ 0} ≃ Target where
  toFun β :=
    { itinerary := β.val.itinerary
      realization := ⟨⟨β.val.realization.1.val, by
        rw [mem_decoratedHistorySupport]
        refine ⟨?_, (mem_decoratedHistorySupport ..).mp β.val.realization.1.property |>.2⟩
        have he := map_homogeneousHistory_of_injective ℳ 𝓝 r id hr Function.injective_id
          (fun j => T (β.val.itinerary.get j)) (fun j => U (β.val.itinerary.get j))
          (fun j => hT _) β.val.realization.1.val a
        simp only [Function.id_comp] at he
        rw [← he]
        simpa only [CutoffDecoratedRay.decoration_eq] using β.property⟩,
        β.val.realization.2⟩
      degree_mem := β.val.degree_mem
      degree_sub_mem := β.val.degree_sub_mem }
  invFun β := by
    have he := map_homogeneousHistory_of_injective ℳ 𝓝 r id hr Function.injective_id
      (fun j => T (β.itinerary.get j)) (fun j => U (β.itinerary.get j))
      (fun j => hT _) β.realization.1.val a
    simp only [Function.id_comp] at he
    have hn := (mem_decoratedHistorySupport ..).mp β.realization.1.property
    have hsource : β.realization.1.val ∈
        decoratedHistorySupport ℳ (fun j => T (β.itinerary.get j)) 0 a v
          (fun j => f (β.itinerary.get j)) (fun j => ε (β.itinerary.get j)) := by
      rw [mem_decoratedHistorySupport]
      exact ⟨fun hz => hn.1 (by rw [← he, hz, map_zero]), hn.2⟩
    exact ⟨{ itinerary := β.itinerary
             realization := ⟨⟨β.realization.1.val, hsource⟩, β.realization.2⟩
             degree_mem := β.degree_mem
             degree_sub_mem := β.degree_sub_mem }, by
      simpa only [CutoffDecoratedRay.decoration_eq, he] using hn.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Specialization retains every recorded encounter, including identity
components and nonzero degree changes with zero spatial projection. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_itinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a v f c ε P W S C k Q β).itinerary =
      β.val.itinerary := (rfl)

/-- The selected degrees of every segment are unchanged by specialization. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_history
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a
      v f c ε P W S C k Q β).realization.1.val
      β.val.realization.1.val := (HEq.rfl)

/-- Specialization preserves the entire geometric ray, including its incoming tail. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_ray
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a
      v f c ε P W S C k Q β).realization.2.ray =
      β.val.realization.2.ray := (rfl)

/-- All encounter times are preserved, including unchanged-direction encounters. -/
@[simp]
theorem cutoffDecoratedRayCoefficientEquiv_parameter
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a
      v f c ε P W S C k Q β).realization.2.parameter
      β.val.realization.2.parameter := (HEq.rfl)

/-- The final whole decoration specializes by the given coefficient map. -/
@[simp↓]
theorem cutoffDecoratedRayCoefficientEquiv_decoration
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a v f c ε P W S C k Q β).decoration =
      r β.val.decoration := by
  simp only [CutoffDecoratedRay.decoration_eq]
  exact (map_homogeneousHistory_of_injective ℳ 𝓝 r id hr Function.injective_id
    (fun j => T (β.val.itinerary.get j)) (fun j => U (β.val.itinerary.get j))
    (fun j => hT _) β.val.realization.1.val a).symm

include hT

/-- Weighted evaluation across all cutoff itineraries commutes with a
coefficient specialization. Vanished decorations are discarded automatically. -/
theorem map_cutoffDecoratedEvaluation [Finite J] :
    r (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) =
      cutoffDecoratedEvaluation d 𝓝 U a' v f c ε P W S C k Q := by
  classical
  let := Fintype.ofFinite Source
  let := Fintype.ofFinite Target
  let e := cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a v f c ε P W S C k Q
  simp only [cutoffDecoratedEvaluation_def, map_sum]
  refine Finset.sum_bij_ne_zero (fun β _ hβ => e ⟨β, hβ⟩) (by simp) ?_ ?_ ?_
  · intro β _ hβ γ _ hγ he
    exact congrArg Subtype.val (e.injective he)
  · intro β _ _
    exact ⟨(e.symm β).val, Finset.mem_univ _, (e.symm β).property, e.apply_symm_apply β⟩
  · intro β _ hβ
    exact (cutoffDecoratedRayCoefficientEquiv_decoration d ℳ 𝓝 r hr T U hT a v f c ε
      P W S C k Q ⟨β, hβ⟩).symm

end Mei
