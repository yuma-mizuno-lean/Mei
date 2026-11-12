/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Transport
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component
public import Mei.LinearAlgebra.GradedModule.Shifted.Map
public import Mei.LinearAlgebra.GradedModule.Shifted.Naturality

/-!
# Degree-changing maps of global coefficient modules

A homogeneous linear map along a positive degree map induces a map of global
shifted coefficients. Every target component is a finite sum over a degree fiber
at a sufficient source cutoff; different source degrees may cancel. Neither the
degree map nor the coefficient map is assumed injective.

These coordinate changes occur in the coefficient setting of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, §2.1
(arXiv:1503.06183).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)
noncomputable section

namespace TauCeti.PositiveDegreeMap

open Mei

variable {Γ Γ' R M N : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R N)
  [DirectSum.Decomposition ℳ]
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

/-- Apply a homogeneous coefficient map on the direct limit of translated completions. -/
def shiftedDirectLimitMap : d.ShiftedDirectLimit ℳ →ₗ[R] e.ShiftedDirectLimit 𝓝 :=
  d.shiftedDirectLimitLift e T.toAddMonoidHom T.map_mem ℳ 𝓝 (RingHom.id R)
    (fun p => T.shiftedCompletionMap ℳ 𝓝 p f hf)
    (fun p q hpq x => T.shiftedCompletionMap_inclusion ℳ 𝓝 p f hf q hpq x)

/-- A global degree map is computed in any target chart containing the mapped origin. -/
theorem shiftedDirectLimitMap_toShiftedDirectLimit (s : Multiset d.monoid)
    (t : Multiset e.monoid) (ht : T (d.coefficientOrigin s) - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    T.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimit ℳ s x) =
      e.toShiftedDirectLimitOfChart 𝓝 (T (d.coefficientOrigin s)) t ht
        (T.shiftedCompletionMap ℳ 𝓝 (d.coefficientOrigin s) f hf x) :=
  d.shiftedDirectLimitLift_toShiftedDirectLimit e T.toAddMonoidHom T.map_mem ℳ 𝓝
    (RingHom.id R) (fun p => T.shiftedCompletionMap ℳ 𝓝 p f hf)
    (fun p q hpq x => T.shiftedCompletionMap_inclusion ℳ 𝓝 p f hf q hpq x) s t ht x

/-- Arbitrary-origin chart embeddings commute with the global degree map. -/
theorem shiftedDirectLimitMap_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hs : p - d.coefficientOrigin s ∈ d.monoid)
    (t : Multiset e.monoid) (ht : T p - e.coefficientOrigin t ∈ e.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    T.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimitOfChart ℳ p s hs x) =
      e.toShiftedDirectLimitOfChart 𝓝 (T p) t ht (T.shiftedCompletionMap ℳ 𝓝 p f hf x) :=
  d.shiftedDirectLimitLift_toShiftedDirectLimitOfChart e T.toAddMonoidHom T.map_mem ℳ 𝓝
    (RingHom.id R) (fun p => T.shiftedCompletionMap ℳ 𝓝 p f hf)
    (fun p q hpq x => T.shiftedCompletionMap_inclusion ℳ 𝓝 p f hf q hpq x) p s hs t ht x

/-- The canonical image chart computes global transport without a chart choice. -/
@[simp]
theorem shiftedDirectLimitMap_toShiftedDirectLimit_imageChart (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    T.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimit ℳ s x) =
      e.toShiftedDirectLimitOfChart 𝓝 (T (d.coefficientOrigin s))
        (d.coefficientImageChart e T.toAddMonoidHom T.map_mem s)
        (d.coefficientImageChart_mem e T.toAddMonoidHom T.map_mem s)
        (T.shiftedCompletionMap ℳ 𝓝 (d.coefficientOrigin s) f hf x) :=
  T.shiftedDirectLimitMap_toShiftedDirectLimit ℳ 𝓝 f hf s _ _ x

/-- The identity degree and coefficient maps fix every global coefficient. -/
@[simp]
theorem shiftedDirectLimitMap_id (x : d.ShiftedDirectLimit ℳ) :
    (PositiveDegreeMap.id d).shiftedDirectLimitMap ℳ ℳ LinearMap.id
      (fun q => by simpa only [PositiveDegreeMap.id_apply, Submodule.comap_id] using
        (le_rfl : ℳ q ≤ ℳ q)) x =
      x := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  have h : ∀ q, ℳ q ≤ (ℳ (PositiveDegreeMap.id d q)).comap (LinearMap.id : M →ₗ[R] M) :=
    fun q => by simpa only [PositiveDegreeMap.id_apply, Submodule.comap_id] using
        (le_rfl : ℳ q ≤ ℳ q)
  rw [(PositiveDegreeMap.id d).shiftedDirectLimitMap_toShiftedDirectLimit ℳ ℳ
    LinearMap.id h s s (by simp only [id_apply, sub_self]; exact d.monoid.zero_mem)]
  have hy := shiftedCompletionMap_id d ℳ (d.coefficientOrigin s) h a
  have hc := d.toShiftedDirectLimitOfChart_cast ℳ _ _
    (id_apply (d.coefficientOrigin s)) s s (by simp) (by simp)
    ((PositiveDegreeMap.id d).shiftedCompletionMap ℳ ℳ (d.coefficientOrigin s) LinearMap.id h a)
  have he : cast (congrArg (d.ShiftedCoefficients ℳ) (id_apply (d.coefficientOrigin s)))
      ((PositiveDegreeMap.id d).shiftedCompletionMap ℳ ℳ (d.coefficientOrigin s)
        LinearMap.id h a) = a := eq_of_heq ((cast_heq _ _).trans hy)
  rw [← hc, he, PositiveDegrees.toShiftedDirectLimitOfChart_apply,
    PositiveDegrees.shiftedCompletedInclusion_refl]

/-- Successive degree and coefficient changes agree with their composite.
The intermediate family needs a decomposition to define its completed map. -/
theorem shiftedDirectLimitMap_comp {Γ'' P : Type*} [AddCommGroup Γ'']
    [AddCommGroup P] [Module R P] [DecidableEq Γ'']
    {a : PositiveDegrees Γ''} (U : PositiveDegreeMap e a)
    (𝓟 : Γ'' → Submodule R P) [DirectSum.Decomposition 𝓝]
    (g : N →ₗ[R] P) (hg : ∀ q, 𝓝 q ≤ (𝓟 (U q)).comap g)
    (hc : ∀ q, ℳ q ≤ (𝓟 ((U.comp T) q)).comap (g.comp f))
    (x : d.ShiftedDirectLimit ℳ) :
    U.shiftedDirectLimitMap 𝓝 𝓟 g hg (T.shiftedDirectLimitMap ℳ 𝓝 f hf x) =
      (U.comp T).shiftedDirectLimitMap ℳ 𝓟 (g.comp f) hc x := by
  obtain ⟨s, z, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  let t := d.coefficientImageChart e T.toAddMonoidHom T.map_mem s
  have ht := d.coefficientImageChart_mem e T.toAddMonoidHom T.map_mem s
  let u := d.coefficientImageChart a (U.comp T).toAddMonoidHom (U.comp T).map_mem s
  have hu := d.coefficientImageChart_mem a (U.comp T).toAddMonoidHom (U.comp T).map_mem s
  have hu' : U (T (d.coefficientOrigin s)) - a.coefficientOrigin u ∈ a.monoid := by
    simpa only [comp_apply] using hu
  rw [T.shiftedDirectLimitMap_toShiftedDirectLimit ℳ 𝓝 f hf s t ht,
    U.shiftedDirectLimitMap_toShiftedDirectLimitOfChart 𝓝 𝓟 g hg
      (T (d.coefficientOrigin s)) t ht u hu',
    (U.comp T).shiftedDirectLimitMap_toShiftedDirectLimit ℳ 𝓟 (g.comp f) hc s u hu]
  have hm := T.shiftedCompletionMap_comp ℳ 𝓝 (d.coefficientOrigin s) f hf U 𝓟 g hg hc z
  have he : cast (congrArg (a.ShiftedCoefficients 𝓟) (comp_apply U T (d.coefficientOrigin s)))
      ((U.comp T).shiftedCompletionMap ℳ 𝓟 (d.coefficientOrigin s) (g.comp f) hc z) =
      U.shiftedCompletionMap 𝓝 𝓟 (T (d.coefficientOrigin s)) g hg
        (T.shiftedCompletionMap ℳ 𝓝 (d.coefficientOrigin s) f hf z) :=
    eq_of_heq ((cast_heq _ _).trans hm)
  have hchart := a.toShiftedDirectLimitOfChart_cast 𝓟 _ _
    (comp_apply U T (d.coefficientOrigin s)) u u hu hu'
    ((U.comp T).shiftedCompletionMap ℳ 𝓟 (d.coefficientOrigin s) (g.comp f) hc z)
  rw [he] at hchart
  exact hchart

variable [DirectSum.Decomposition 𝓝]

open Classical in
/-- A target global component is the sum of the source components in its finite cutoff fiber.
The cutoff bounds relative degrees, so this formula includes negative chart origins. -/
theorem coe_shiftedDirectLimitComponents_map_eq_sum (p : Γ)
    (s : Multiset d.monoid) (hs : p - d.coefficientOrigin s ∈ d.monoid)
    (j : Γ') (k : ℕ) (hj : e.degree j ≤ k) (x : d.ShiftedCoefficients ℳ p) :
    (e.shiftedDirectLimitComponents 𝓝
      (T.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimitOfChart ℳ p s hs x))
      (T p + j) : N) =
      ∑ n ∈ (d.finite_cutoff (T.modulus k)).toFinset with T n = j,
        f (d.shiftedHomogeneousComponent ℳ p (p + n) x : M) := by
  let t := d.coefficientImageChart e T.toAddMonoidHom T.map_mem s
  have ht : T p - e.coefficientOrigin t ∈ e.monoid := by
    rw [← d.coefficientImageChart_origin e T.toAddMonoidHom T.map_mem s, ← map_sub]
    exact T.map_mem hs
  rw [T.shiftedDirectLimitMap_toShiftedDirectLimitOfChart ℳ 𝓝 f hf p s hs t ht,
    e.shiftedDirectLimitComponents_toShiftedDirectLimitOfChart, shiftedCompletionMap_def]
  exact d.shiftedHomogeneousComponent_completionMap_eq_sum e ℳ 𝓝 p T.toAddMonoidHom f
    (T.shiftedMap ℳ 𝓝 p f hf) (fun a => T.coe_shiftedMap ℳ 𝓝 p f hf a)
    (fun q a ha => hf q ha) T.modulus T.monotone_modulus
    (fun l _ ha => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf l ha) j k hj x

end TauCeti.PositiveDegreeMap
