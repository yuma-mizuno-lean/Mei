/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.DirectLimit.Semilinear
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Inclusion

/-!
# Compatible transport of global coefficient charts

Semilinear maps of translated completions descend through Mathlib's module
colimit when they commute with support inclusions. The degree map only needs to
preserve the supporting monoids; no graded decomposition or injectivity is used.
-/

public section

open TauCeti (PositiveDegrees)
noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ Γ' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : Γ →+ Γ')
  (hT : ∀ {n}, n ∈ d.monoid → T n ∈ e.monoid)

/-- A canonical target chart containing the image of a source chart. -/
def coefficientImageChart (s : Multiset d.monoid) : Multiset e.monoid :=
  {⟨T (s.sum : Γ), hT s.sum.property⟩}

/-- The image chart has exactly the mapped source origin. -/
theorem coefficientImageChart_origin (s : Multiset d.monoid) :
    T (d.coefficientOrigin s) = e.coefficientOrigin (coefficientImageChart d e T hT s) := by
  simp only [PositiveDegrees.coefficientOrigin_eq_neg_sum, coefficientImageChart,
    Multiset.sum_singleton, map_neg]

/-- The mapped source origin belongs to its canonical image chart. -/
theorem coefficientImageChart_mem (s : Multiset d.monoid) :
    T (d.coefficientOrigin s) -
      e.coefficientOrigin (coefficientImageChart d e T hT s) ∈ e.monoid := by
  rw [coefficientImageChart_origin d e T hT, sub_self]
  exact e.monoid.zero_mem

variable {R S M N : Type*} [Ring R] [Ring S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  [DecidableEq Γ] [DecidableEq Γ']
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule S N) (σ : R →+* S)
  (F : ∀ p, d.ShiftedCoefficients ℳ p →ₛₗ[σ] e.ShiftedCoefficients 𝓝 (T p))
  (hF : ∀ p q (hpq : p - q ∈ d.monoid) (x : d.ShiftedCoefficients ℳ p),
    F q (d.shiftedCompletedInclusion ℳ p q hpq x) =
      e.shiftedCompletedInclusion 𝓝 (T p) (T q)
        ((map_sub T p q) ▸ hT hpq) (F p x))

private def mapGlobalChart (s : Multiset d.monoid) :
    d.ShiftedCoefficients ℳ (d.coefficientOrigin s) →ₛₗ[σ]
      e.ShiftedDirectLimit 𝓝 :=
  (e.toShiftedDirectLimitOfChart 𝓝 (T (d.coefficientOrigin s))
    (coefficientImageChart d e T hT s) (coefficientImageChart_mem d e T hT s)).comp
      (F (d.coefficientOrigin s))

omit [DecidableEq Γ] in
private theorem mapGlobalChart_apply (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    mapGlobalChart d e T hT ℳ 𝓝 σ F s x =
      e.toShiftedDirectLimitOfChart 𝓝 (T (d.coefficientOrigin s))
        (coefficientImageChart d e T hT s) (coefficientImageChart_mem d e T hT s)
        (F (d.coefficientOrigin s) x) := by
  -- Applying the composition exposes the defining chart map.
  rfl

include hF in
omit [DecidableEq Γ] in
private theorem mapGlobalChart_inclusion (s t : Multiset d.monoid) (hst : s ≤ t)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    mapGlobalChart d e T hT ℳ 𝓝 σ F t (d.coefficientInclusion ℳ s t hst x) =
      mapGlobalChart d e T hT ℳ 𝓝 σ F s x := by
  simp only [mapGlobalChart, LinearMap.comp_apply, PositiveDegrees.coefficientInclusion_eq,
    hF]
  exact e.toShiftedDirectLimitOfChart_inclusion 𝓝
    (T (d.coefficientOrigin s)) (T (d.coefficientOrigin t))
    (by simpa only [map_sub] using hT (d.coefficientOrigin_sub_mem hst))
    (coefficientImageChart d e T hT s) (coefficientImageChart d e T hT t)
    (coefficientImageChart_mem d e T hT s) (coefficientImageChart_mem d e T hT t) _

/-- Descend compatible semilinear maps of shifted coefficients to the direct limit. -/
def shiftedDirectLimitLift :
    d.ShiftedDirectLimit ℳ →ₛₗ[σ] e.ShiftedDirectLimit 𝓝 :=
  Module.DirectLimit.liftSemilinear
    (fun s t hst => d.coefficientInclusion ℳ s t hst) σ
    (mapGlobalChart d e T hT ℳ 𝓝 σ F) (mapGlobalChart_inclusion d e T hT ℳ 𝓝 σ F hF)

private theorem shiftedDirectLimitLift_chart (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    shiftedDirectLimitLift d e T hT ℳ 𝓝 σ F hF (d.toShiftedDirectLimit ℳ s x) =
      mapGlobalChart d e T hT ℳ 𝓝 σ F s x := by
  exact (congrArg (shiftedDirectLimitLift d e T hT ℳ 𝓝 σ F hF)
    (d.toShiftedDirectLimit_apply ℳ s x)).trans
      (Module.DirectLimit.liftSemilinear_of
        (fun s t hst => d.coefficientInclusion ℳ s t hst) σ
        (mapGlobalChart d e T hT ℳ 𝓝 σ F) (mapGlobalChart_inclusion d e T hT ℳ 𝓝 σ F hF) s x)

/-- Transport in a chart can use any target chart containing the mapped origin. -/
theorem shiftedDirectLimitLift_toShiftedDirectLimit (s : Multiset d.monoid)
    (t : Multiset e.monoid) (ht : T (d.coefficientOrigin s) - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    shiftedDirectLimitLift d e T hT ℳ 𝓝 σ F hF (d.toShiftedDirectLimit ℳ s x) =
      e.toShiftedDirectLimitOfChart 𝓝 (T (d.coefficientOrigin s)) t ht
        (F (d.coefficientOrigin s) x) := by
  rw [shiftedDirectLimitLift_chart, mapGlobalChart_apply]
  simpa only [PositiveDegrees.shiftedCompletedInclusion_refl] using
    e.toShiftedDirectLimitOfChart_inclusion 𝓝
      (T (d.coefficientOrigin s)) (T (d.coefficientOrigin s)) (by simp)
      t (coefficientImageChart d e T hT s) ht (coefficientImageChart_mem d e T hT s)
      (F (d.coefficientOrigin s) x)

/-- Arbitrary-origin chart embeddings commute with the global semilinear coefficient lift. -/
theorem shiftedDirectLimitLift_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hs : p - d.coefficientOrigin s ∈ d.monoid)
    (t : Multiset e.monoid) (ht : T p - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    shiftedDirectLimitLift d e T hT ℳ 𝓝 σ F hF (d.toShiftedDirectLimitOfChart ℳ p s hs x) =
      e.toShiftedDirectLimitOfChart 𝓝 (T p) t ht
        (F p x) := by
  let E := e.toShiftedDirectLimitOfChart 𝓝 (T (d.coefficientOrigin s))
    (coefficientImageChart d e T hT s) (coefficientImageChart_mem d e T hT s)
  have h₁ := congrArg (shiftedDirectLimitLift d e T hT ℳ 𝓝 σ F hF)
    (d.toShiftedDirectLimitOfChart_apply ℳ p s hs x)
  have h₂ := shiftedDirectLimitLift_chart d e T hT ℳ 𝓝 σ F hF s
    (d.shiftedCompletedInclusion ℳ p (d.coefficientOrigin s) hs x)
  have h₃ := mapGlobalChart_apply d e T hT ℳ 𝓝 σ F s
    (d.shiftedCompletedInclusion ℳ p (d.coefficientOrigin s) hs x)
  have h₄ := congrArg E (hF
    p (d.coefficientOrigin s) hs x)
  have h₅ := e.toShiftedDirectLimitOfChart_inclusion 𝓝 (T p)
    (T (d.coefficientOrigin s)) (by simpa only [map_sub] using hT hs)
    t (coefficientImageChart d e T hT s) ht (coefficientImageChart_mem d e T hT s)
    (F p x)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end TauCeti.PositiveDegrees
