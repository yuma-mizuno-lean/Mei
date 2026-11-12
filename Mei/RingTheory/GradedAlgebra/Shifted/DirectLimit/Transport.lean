/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Transport
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.NonUnital

/-!
# Multiplicative transport of global coefficient charts

A global map preserves products when its values on translated charts
are given by local maps preserving completed products. Only preservation of the
supporting monoids is needed for the additive degree map; no decomposition,
cutoff modulus, injectivity or homogeneous unit is used in this descent.
-/

public section

open TauCeti (PositiveDegrees)
noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ Γ' R S A B : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [CommRing R] [CommRing S] [Ring A] [Ring B] [Algebra R A] [Algebra S B]
  [DecidableEq Γ] [DecidableEq Γ']
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : Γ →+ Γ')
  (hT : ∀ {n}, n ∈ d.monoid → T n ∈ e.monoid)
  (𝒜 : Γ → Submodule R A) (ℬ : Γ' → Submodule S B)
  [SetLike.GradedMul 𝒜] [SetLike.GradedMul ℬ]
  (F : ∀ p, d.ShiftedCoefficients 𝒜 p → e.ShiftedCoefficients ℬ (T p))
  (Φ : d.ShiftedDirectLimit 𝒜 → e.ShiftedDirectLimit ℬ)
  (hchart : ∀ p s (hs : p - d.coefficientOrigin s ∈ d.monoid) t
    (ht : T p - e.coefficientOrigin t ∈ e.monoid) (x : d.ShiftedCoefficients 𝒜 p),
    Φ (d.toShiftedDirectLimitOfChart 𝒜 p s hs x) =
      e.toShiftedDirectLimitOfChart ℬ (T p) t ht (F p x))
  (hmul : ∀ p q (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q),
    cast (congrArg (e.ShiftedCoefficients ℬ) (map_add T p q))
      (F (p + q) (d.shiftedCompletionMul 𝒜 p q x y)) =
        e.shiftedCompletionMul ℬ (T p) (T q) (F p x) (F q y))

include hchart hmul

private theorem map_mul_charts (p r : Γ) (s t : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hr : r - d.coefficientOrigin t ∈ d.monoid) (u v : Multiset e.monoid)
    (hu : T p - e.coefficientOrigin u ∈ e.monoid)
    (hv : T r - e.coefficientOrigin v ∈ e.monoid)
    (x : d.ShiftedCoefficients 𝒜 p)
    (y : d.ShiftedCoefficients 𝒜 r) :
    Φ
        (d.toShiftedDirectLimitOfChart 𝒜 p s hp x *
          d.toShiftedDirectLimitOfChart 𝒜 r t hr y) =
      Φ (d.toShiftedDirectLimitOfChart 𝒜 p s hp x) *
        Φ (d.toShiftedDirectLimitOfChart 𝒜 r t hr y) := by
  have hst : p + r - d.coefficientOrigin (s + t) ∈ d.monoid := by
    simpa only [PositiveDegrees.coefficientOrigin_add, add_sub_add_comm] using
      d.monoid.add_mem hp hr
  have huv : T p + T r - e.coefficientOrigin (u + v) ∈ e.monoid := by
    simpa only [PositiveDegrees.coefficientOrigin_add, add_sub_add_comm] using
      e.monoid.add_mem hu hv
  have huv' : T (p + r) - e.coefficientOrigin (u + v) ∈ e.monoid := by
    simpa only [map_add] using huv
  let z := d.shiftedCompletionMul 𝒜 p r x y
  let E := e.toShiftedDirectLimitOfChart ℬ (T p + T r) (u + v) huv
  have hs := (d.shiftedDirectLimitMul_eq_mul 𝒜 _ _).symm.trans
    (d.shiftedDirectLimitMul_toShiftedDirectLimitOfChart 𝒜 p r s t hp hr x y)
  have h₁ := congrArg (Φ) hs
  have h₂ := hchart
    (p + r) (s + t) hst (u + v) huv' z
  have h₃ := e.toShiftedDirectLimitOfChart_cast ℬ (T (p + r)) (T p + T r)
    (map_add T p r) (u + v) (u + v) huv' huv
    (F (p + r) z)
  have h₄ := congrArg E (hmul p r x y)
  have ht := (e.shiftedDirectLimitMul_eq_mul ℬ _ _).symm.trans
    (e.shiftedDirectLimitMul_toShiftedDirectLimitOfChart ℬ
      (T p) (T r) u v hu hv
      (F p x) (F r y))
  have hf := congrArg₂ (fun a b : e.ShiftedDirectLimit ℬ => a * b)
    (hchart p s hp u hu x)
    (hchart r t hr v hv y)
  exact (h₁).trans <|
    (h₂).trans <|
    (h₃.symm).trans <|
    (h₄).trans <|
    (ht.symm).trans <|
    hf.symm

include hT in
/-- A map with multiplicative compatible chart values preserves global products. -/
theorem shiftedDirectLimitMap_mul_of_charts (x y : d.ShiftedDirectLimit 𝒜) :
    Φ (x * y) =
      Φ x * Φ y := by
  refine (d.exists_toShiftedDirectLimit 𝒜 x).elim fun s hs => ?_
  refine hs.elim fun a ha => ?_
  refine (d.exists_toShiftedDirectLimit 𝒜 y).elim fun t ht => ?_
  refine ht.elim fun b hb => ?_
  let u := d.coefficientImageChart e T hT s
  let v := d.coefficientImageChart e T hT t
  have hu := d.coefficientImageChart_mem e T hT s
  have hv := d.coefficientImageChart_mem e T hT t
  have hs : d.toShiftedDirectLimitOfChart 𝒜 (d.coefficientOrigin s) s (by simp) a = x :=
    (d.toShiftedDirectLimitOfChart_apply 𝒜 (d.coefficientOrigin s) s (by simp) a).trans
      ((congrArg (d.toShiftedDirectLimit 𝒜 s)
        (d.shiftedCompletedInclusion_refl 𝒜 (d.coefficientOrigin s) a)).trans ha)
  have ht : d.toShiftedDirectLimitOfChart 𝒜 (d.coefficientOrigin t) t (by simp) b = y :=
    (d.toShiftedDirectLimitOfChart_apply 𝒜 (d.coefficientOrigin t) t (by simp) b).trans
      ((congrArg (d.toShiftedDirectLimit 𝒜 t)
        (d.shiftedCompletedInclusion_refl 𝒜 (d.coefficientOrigin t) b)).trans hb)
  have hmul := map_mul_charts d e T 𝒜 ℬ F Φ hchart hmul
    (d.coefficientOrigin s) (d.coefficientOrigin t)
    s t (by simp) (by simp) u v hu hv a b
  have hl := congrArg₂ (fun a b => Φ (a * b)) hs ht
  have hr := congrArg₂ (fun a b => Φ a *
    Φ b) hs ht
  exact hl.symm.trans (hmul.trans hr)

end TauCeti.PositiveDegrees
