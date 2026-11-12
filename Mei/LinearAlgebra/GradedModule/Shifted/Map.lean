/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Inclusion
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient

/-!
# Maps of shifted coefficient modules

A homogeneous linear map along a positive degree map restricts to each shifted
module and extends to its completion. The degree map's cutoff modulus controls
which source quotient computes a target quotient, allowing changes of the degree
function and maps that merge degrees. Neither the degree map nor the linear map
needs to be injective.

The induced finite quotient maps preserve the inherited homogeneous pieces.

The completion is the existing `ModuleFiltration.completionMap`; its defining
projection and coefficient-image laws determine the shifted extension. This is
the shifted coefficient setting of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)

noncomputable section

namespace TauCeti.PositiveDegreeMap

open Mei

section Monoid

variable {Γ Γ' R M M' : Type*} [AddCommMonoid Γ] [AddCommMonoid Γ']
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M') (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

include hf

/-- Homogeneous maps preserve shifted support along their degree map. -/
theorem map_mem_shiftedSubmodule {x : M} (hx : x ∈ shiftedSubmodule ℳ d.monoid p) :
    f x ∈ shiftedSubmodule 𝓝 e.monoid (T p) := by
  rw [shiftedSubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => f x ∈ shiftedSubmodule 𝓝 e.monoid (T p)) hx ?_ ?_ ?_
  · intro n x hx
    apply le_shiftedSubmodule 𝓝 e.monoid (T p) (T.map_mem n.property)
    simpa only [map_add, Submodule.mem_comap] using hf (p + n) hx
  · simp
  · intro x y hx hy
    simpa only [_root_.map_add] using Submodule.add_mem _ hx hy

/-- Restrict a homogeneous coefficient map to a shifted module. -/
def shiftedMap : shiftedSubmodule ℳ d.monoid p →ₗ[R]
    shiftedSubmodule 𝓝 e.monoid (T p) :=
  (f.comp (shiftedSubmodule ℳ d.monoid p).subtype).codRestrict _
    (fun x => T.map_mem_shiftedSubmodule ℳ 𝓝 p f hf x.property)

/-- The restricted coefficient map has the same ambient values. -/
@[simp]
theorem coe_shiftedMap (x : shiftedSubmodule ℳ d.monoid p) :
    (T.shiftedMap ℳ 𝓝 p f hf x : M') = f x := (rfl)

/-- Relative degree `n` is carried to relative degree `T n`. -/
theorem shiftedMap_mem_shiftedGrading {n : Γ} {x : shiftedSubmodule ℳ d.monoid p}
    (hx : x ∈ shiftedGrading ℳ d.monoid p n) :
    T.shiftedMap ℳ 𝓝 p f hf x ∈ shiftedGrading 𝓝 e.monoid (T p) (T n) := by
  rw [mem_shiftedGrading, coe_shiftedMap]
  simpa only [map_add, Submodule.mem_comap] using
    hf (p + n) ((mem_shiftedGrading ℳ d.monoid p).mp hx)

end Monoid

section Filtration

variable {Γ Γ' R M M' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [DecidableEq Γ]
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M')
  [DirectSum.Decomposition ℳ] (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

include hf

/-- The degree map's modulus bounds the source filtration needed at each target order. -/
theorem shiftedMap_mem_shiftedFiltration (k : ℕ)
    {x : shiftedSubmodule ℳ d.monoid p}
    (hx : x ∈ (d.shiftedFiltration ℳ p).submodule (T.modulus k + 1)) :
    T.shiftedMap ℳ 𝓝 p f hf x ∈ (e.shiftedFiltration 𝓝 (T p)).submodule (k + 1) := by
  rw [d.shiftedFiltration_succ ℳ p] at hx
  rw [d.degreeSubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => T.shiftedMap ℳ 𝓝 p f hf x ∈
      (e.shiftedFiltration 𝓝 (T p)).submodule (k + 1)) hx ?_ ?_ ?_
  · intro n x hx
    by_cases hn : n.val ∈ d.monoid
    · rw [e.shiftedFiltration_submodule 𝓝 (T p), Submodule.mem_comap,
        Submodule.subtype_apply, coe_shiftedMap]
      apply Mei.DirectSum.le_degreeTail 𝓝 _ (i := T (p + n))
      · have hd := T.degree_gt k hn n.property
        simp only [map_add, add_sub_cancel_left, Nat.cast_add, Nat.cast_one]
        omega
      · exact hf (p + n) ((mem_shiftedGrading ℳ d.monoid p).mp hx)
    · rw [shiftedGrading_eq_bot ℳ d.monoid p hn, Submodule.mem_bot] at hx
      simp [hx]
  · simp
  · intro x y hx hy
    simpa only [_root_.map_add] using Submodule.add_mem _ hx hy

end Filtration

section Group

variable {Γ Γ' R M M' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [DecidableEq Γ]
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M')
  [DirectSum.Decomposition ℳ] (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

include hf

/-- The finite quotient map at the source cutoff specified by the degree modulus. -/
def shiftedQuotientMap (k : ℕ) :
    (d.shiftedFiltration ℳ p).quotient (T.modulus k) →ₗ[R]
      (e.shiftedFiltration 𝓝 (T p)).quotient k :=
  ((d.shiftedFiltration ℳ p).submodule (T.modulus k + 1)).mapQ
    ((e.shiftedFiltration 𝓝 (T p)).submodule (k + 1))
    (T.shiftedMap ℳ 𝓝 p f hf) (fun _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx)

/-- The finite shifted map is the induced map between the selected filtration quotients. -/
theorem shiftedQuotientMap_def (k : ℕ) :
    T.shiftedQuotientMap ℳ 𝓝 p f hf k =
      ((d.shiftedFiltration ℳ p).submodule (T.modulus k + 1)).mapQ
        ((e.shiftedFiltration 𝓝 (T p)).submodule (k + 1))
        (T.shiftedMap ℳ 𝓝 p f hf)
        (fun _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx) := (rfl)

/-- The finite shifted map sends a coefficient class to the class of its image. -/
@[simp]
theorem shiftedQuotientMap_mk (k : ℕ) (x : shiftedSubmodule ℳ d.monoid p) :
    T.shiftedQuotientMap ℳ 𝓝 p f hf k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (T.shiftedMap ℳ 𝓝 p f hf x) := (rfl)

/-- The induced map on the existing shifted coefficient completions. -/
def shiftedCompletionMap : d.ShiftedCoefficients ℳ p →ₗ[R] e.ShiftedCoefficients 𝓝 (T p) :=
  (d.shiftedFiltration ℳ p).completionMap (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus
    (fun k _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx)

/-- The shifted extension is the existing completion map for the restricted coefficient map. -/
theorem shiftedCompletionMap_def :
    T.shiftedCompletionMap ℳ 𝓝 p f hf =
      (d.shiftedFiltration ℳ p).completionMap (e.shiftedFiltration 𝓝 (T p))
        (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus
        (fun k _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx) := (rfl)

/-- A target finite projection is computed at the source cutoff given by the modulus. -/
@[simp]
theorem projection_shiftedCompletionMap (k : ℕ) (x : d.ShiftedCoefficients ℳ p) :
    (e.shiftedFiltration 𝓝 (T p)).projection k (T.shiftedCompletionMap ℳ 𝓝 p f hf x) =
      T.shiftedQuotientMap ℳ 𝓝 p f hf k ((d.shiftedFiltration ℳ p).projection (T.modulus k) x) :=
  (d.shiftedFiltration ℳ p).projection_completionMap (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus _ k x

/-- The completed shifted map extends the original homogeneous coefficient map. -/
@[simp]
theorem shiftedCompletionMap_of (x : shiftedSubmodule ℳ d.monoid p) :
    T.shiftedCompletionMap ℳ 𝓝 p f hf ((d.shiftedFiltration ℳ p).of x) =
      (e.shiftedFiltration 𝓝 (T p)).of (T.shiftedMap ℳ 𝓝 p f hf x) :=
  (d.shiftedFiltration ℳ p).completionMap_of (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus _ x

/-- A degree-changing completed map commutes with enlargement of translated support. -/
theorem shiftedCompletionMap_inclusion (q : Γ) (hpq : p - q ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    T.shiftedCompletionMap ℳ 𝓝 q f hf (d.shiftedCompletedInclusion ℳ p q hpq x) =
      e.shiftedCompletedInclusion 𝓝 (T p) (T q)
        (by simpa only [map_sub] using T.map_mem hpq)
        (T.shiftedCompletionMap ℳ 𝓝 p f hf x) := by
  let hTpq : T p - T q ∈ e.monoid := by simpa only [map_sub] using T.map_mem hpq
  have hi : (T.shiftedMap ℳ 𝓝 q f hf).comp
      (shiftedSupportInclusion ℳ d.monoid p q hpq) =
      (shiftedSupportInclusion 𝓝 e.monoid (T p) (T q) hTpq).comp
        (T.shiftedMap ℳ 𝓝 p f hf) := by
    ext a
    simp only [LinearMap.comp_apply, coe_shiftedMap, coe_shiftedSupportInclusion]
  have h₁ := ModuleFiltration.completionMap_comp
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration ℳ q)
    (shiftedSupportInclusion ℳ d.monoid p q hpq) _root_.id monotone_id
    (fun k => d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))
    (e.shiftedFiltration 𝓝 (T q)) (T.shiftedMap ℳ 𝓝 q f hf)
    T.modulus T.monotone_modulus
    (fun k _ ha => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 q f hf k ha)
  have h₂ := ModuleFiltration.completionMap_comp
    (d.shiftedFiltration ℳ p) (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus
    (fun k _ ha => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k ha)
    (e.shiftedFiltration 𝓝 (T q))
    (shiftedSupportInclusion 𝓝 e.monoid (T p) (T q) hTpq) _root_.id monotone_id
    (fun k => e.shiftedSupportInclusion_filtered 𝓝 (T p) (T q) hTpq (k + 1))
  simp only [hi, Function.id_comp, Function.comp_id] at h₁ h₂
  simpa only [shiftedCompletionMap_def, PositiveDegrees.shiftedCompletedInclusion_def,
    LinearMap.comp_apply] using congrArg (fun F => F x) (h₁.symm.trans h₂)

/-- Composition of degree-changing completed maps, with heterogeneous equality
accounting for the canonically equal target origins. -/
theorem shiftedCompletionMap_comp {Γ'' P : Type*} [AddCommGroup Γ'']
    [AddCommGroup P] [Module R P] [DecidableEq Γ']
    {a : PositiveDegrees Γ''} (U : PositiveDegreeMap e a)
    (𝓟 : Γ'' → Submodule R P) [DirectSum.Decomposition 𝓝]
    (g : M' →ₗ[R] P) (hg : ∀ q, 𝓝 q ≤ (𝓟 (U q)).comap g)
    (hc : ∀ q, ℳ q ≤ (𝓟 ((U.comp T) q)).comap (g.comp f))
    (x : d.ShiftedCoefficients ℳ p) :
    HEq ((U.comp T).shiftedCompletionMap ℳ 𝓟 p (g.comp f) hc x)
      (U.shiftedCompletionMap 𝓝 𝓟 (T p) g hg (T.shiftedCompletionMap ℳ 𝓝 p f hf x)) := by
  revert hc
  -- Expose only the composite degree data; the completion maps remain the
  -- existing functorial filtered maps.
  let C : PositiveDegreeMap d a :=
    { toAddMonoidHom := U.toAddMonoidHom.comp T.toAddMonoidHom
      map_mem := fun h => U.map_mem (T.map_mem h)
      map_ne_zero := fun h hn => U.map_ne_zero (T.map_mem h) (T.map_ne_zero h hn)
      modulus := T.modulus ∘ U.modulus
      monotone_modulus := T.monotone_modulus.comp U.monotone_modulus
      degree_gt := fun k hn h => U.degree_gt k (T.map_mem hn) (T.degree_gt _ hn h) }
  have hC : U.comp T = C :=
    PositiveDegreeMap.ext (fun q => comp_apply U T q) (fun k => comp_modulus U T k)
  rw [hC]
  intro hc
  have hi : C.shiftedMap ℳ 𝓟 p (g.comp f) hc =
      (U.shiftedMap 𝓝 𝓟 (T p) g hg).comp (T.shiftedMap ℳ 𝓝 p f hf) := by
    ext b
    simp only [coe_shiftedMap, LinearMap.comp_apply]
  simp only [heq_iff_eq, shiftedCompletionMap_def, hi]
  exact congrArg (fun F => F x) (ModuleFiltration.completionMap_comp
    (d.shiftedFiltration ℳ p) (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus
    (fun k _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx)
    (a.shiftedFiltration 𝓟 (U (T p))) (U.shiftedMap 𝓝 𝓟 (T p) g hg)
    U.modulus U.monotone_modulus
    (fun k _ hx => U.shiftedMap_mem_shiftedFiltration 𝓝 𝓟 (T p) g hg k hx))

end Group

section QuotientGrading

variable {Γ Γ' : Type} {R M M' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M')
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

/-- The induced finite coefficient map preserves relative homogeneous pieces
along the degree map, at the source order specified by its cutoff modulus. -/
theorem shiftedQuotientMap_mem_shiftedQuotientGrading
    (k : ℕ) {n : Γ}
    {x : (d.shiftedFiltration ℳ p).quotient (T.modulus k)}
    (hx : x ∈ (d.shiftedQuotientGrading ℳ p (T.modulus k)).piece n) :
    T.shiftedQuotientMap ℳ 𝓝 p f hf k x ∈
      (e.shiftedQuotientGrading 𝓝 (T p) k).piece (T n) := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  exact (e.mem_shiftedQuotientGrading_iff 𝓝 (T p)).mpr
    ⟨T.shiftedMap ℳ 𝓝 p f hf a,
      T.shiftedMap_mem_shiftedGrading ℳ 𝓝 p f hf ha, (T.shiftedQuotientMap_mk ..).symm⟩

end QuotientGrading

end TauCeti.PositiveDegreeMap

namespace TauCeti.PositiveDegrees

open Mei

section Monoid

variable {Γ Γ' R M N : Type*} [AddCommMonoid Γ] [AddCommMonoid Γ']
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝒩 : Γ' → Submodule R N) (p : Γ)
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝒩 (T q)).comap f)

private def shiftedMapAt (q : Γ') (hp : T p = q) :
    shiftedSubmodule ℳ d.monoid p →ₗ[R] shiftedSubmodule 𝒩 e.monoid q := by
  subst q
  exact T.shiftedMap ℳ 𝒩 p f hf

private theorem coe_shiftedMapAt (q : Γ') (hp : T p = q)
    (a : shiftedSubmodule ℳ d.monoid p) :
    (shiftedMapAt T ℳ 𝒩 p f hf q hp a : N) = f a := by
  subst q
  exact T.coe_shiftedMap ℳ 𝒩 p f hf a

private theorem shiftedMapAt_mem_shiftedGrading (q : Γ') (hp : T p = q)
    {n : Γ} {a : shiftedSubmodule ℳ d.monoid p}
    (ha : a ∈ shiftedGrading ℳ d.monoid p n) :
    shiftedMapAt T ℳ 𝒩 p f hf q hp a ∈ shiftedGrading 𝒩 e.monoid q (T n) := by
  subst q
  exact T.shiftedMap_mem_shiftedGrading ℳ 𝒩 p f hf ha

end Monoid

section FixedMonoid

variable {Γ R M N : Type*} [AddCommMonoid Γ] [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N) (p : Γ)
  (f : M →ₗ[R] N) (hf₀ : ∀ q, ℳ q ≤ (𝓝 q).comap f)

/-- The existing shifted map for the identity degree map, with its unchanged shift explicit. -/
def shiftedCoefficientMap : shiftedSubmodule ℳ d.monoid p →ₗ[R]
    shiftedSubmodule 𝓝 d.monoid p :=
  shiftedMapAt (PositiveDegreeMap.id d) ℳ 𝓝 p f
    (fun q => by simpa only [PositiveDegreeMap.id_apply] using hf₀ q) p
    (PositiveDegreeMap.id_apply p)

/-- A degree-preserving shifted map has the original ambient coefficient values. -/
@[simp]
theorem coe_shiftedCoefficientMap (a : shiftedSubmodule ℳ d.monoid p) :
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf₀ a : N) = f a :=
  coe_shiftedMapAt _ _ _ _ _ _ _ _ a

/-- Degree-preserving shifted coefficient maps preserve each relative homogeneous piece. -/
theorem shiftedCoefficientMap_mem_shiftedGrading {q : Γ}
    {a : shiftedSubmodule ℳ d.monoid p} (ha : a ∈ shiftedGrading ℳ d.monoid p q) :
    d.shiftedCoefficientMap ℳ 𝓝 p f hf₀ a ∈ shiftedGrading 𝓝 d.monoid p q := by
  simpa only [shiftedCoefficientMap, PositiveDegreeMap.id_apply] using
    shiftedMapAt_mem_shiftedGrading (PositiveDegreeMap.id d) ℳ 𝓝 p f
      (fun q => by simpa only [PositiveDegreeMap.id_apply] using hf₀ q) p
      (PositiveDegreeMap.id_apply p) ha

end FixedMonoid

section FixedGroup

variable {Γ R M N : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  (p : Γ) (f : M →ₗ[R] N) (hf₀ : ∀ q, ℳ q ≤ (𝓝 q).comap f)

/-- Degree-preserving shifted maps preserve the ambient degree tail defining the
relative filtration, without a decomposition of either family. -/
theorem shiftedCoefficientMap_mem_filtration (k : ℕ)
    {a : shiftedSubmodule ℳ d.monoid p}
    (ha : a ∈ (d.shiftedFiltration ℳ p).submodule (k + 1)) :
    d.shiftedCoefficientMap ℳ 𝓝 p f hf₀ a ∈ (d.shiftedFiltration 𝓝 p).submodule (k + 1) := by
  have htail : Mei.DirectSum.degreeTail ℳ (fun u => d.degree (u - p)) (k + 1) ≤
      (Mei.DirectSum.degreeTail 𝓝 (fun u => d.degree (u - p)) (k + 1)).comap f := by
    rw [Mei.DirectSum.degreeTail_def]
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact (hf₀ u).trans (Submodule.comap_mono (Mei.DirectSum.le_degreeTail 𝓝 _ hu))
  rw [d.shiftedFiltration_submodule] at ha ⊢
  simpa only [Submodule.mem_comap, Submodule.subtype_apply,
    coe_shiftedCoefficientMap] using htail ha

/-- The finite coefficient map induced between equal-order relative quotients. -/
def quotientCoefficientMap (k : ℕ) : (d.shiftedFiltration ℳ p).quotient k →ₗ[R]
    (d.shiftedFiltration 𝓝 p).quotient k :=
  ((d.shiftedFiltration ℳ p).submodule (k + 1)).mapQ
    ((d.shiftedFiltration 𝓝 p).submodule (k + 1))
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf₀)
    (fun _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf₀ k ha)

/-- The fixed-degree finite map is induced on the relative filtration quotients. -/
theorem quotientCoefficientMap_def (k : ℕ) :
    d.quotientCoefficientMap ℳ 𝓝 p f hf₀ k =
      ((d.shiftedFiltration ℳ p).submodule (k + 1)).mapQ
        ((d.shiftedFiltration 𝓝 p).submodule (k + 1))
        (d.shiftedCoefficientMap ℳ 𝓝 p f hf₀)
        (fun _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf₀ k ha) := (rfl)

/-- Degree-preserving finite coefficient maps send a class to the class of its image. -/
@[simp]
theorem quotientCoefficientMap_mk (k : ℕ) (a : shiftedSubmodule ℳ d.monoid p) :
    d.quotientCoefficientMap ℳ 𝓝 p f hf₀ k (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (d.shiftedCoefficientMap ℳ 𝓝 p f hf₀ a) := (rfl)

/-- Complete a degree-preserving coefficient map using the identity cutoff modulus. -/
def completionCoefficientMap : d.ShiftedCoefficients ℳ p →ₗ[R] d.ShiftedCoefficients 𝓝 p :=
  (d.shiftedFiltration ℳ p).completionMap (d.shiftedFiltration 𝓝 p)
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf₀) id monotone_id
    (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf₀ k ha)

/-- Degree-preserving completion maps project to the finite maps at the same cutoff. -/
@[simp]
theorem projection_completionCoefficientMap (k : ℕ) (a : d.ShiftedCoefficients ℳ p) :
    (d.shiftedFiltration 𝓝 p).projection k (d.completionCoefficientMap ℳ 𝓝 p f hf₀ a) =
      d.quotientCoefficientMap ℳ 𝓝 p f hf₀ k ((d.shiftedFiltration ℳ p).projection k a) :=
  (d.shiftedFiltration ℳ p).projection_completionMap (d.shiftedFiltration 𝓝 p)
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf₀) id monotone_id _ k a

end FixedGroup

section FixedQuotientGrading

variable {Γ : Type} {R M N : Type*} [AddCommGroup Γ] [DecidableEq Γ] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  (p : Γ) (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝓝 q).comap f)

/-- Fixed-degree coefficient maps preserve the relative homogeneous pieces of
the finite quotient, including pieces killed by the map. -/
theorem quotientCoefficientMap_mem_shiftedQuotientGrading
    {k : ℕ} {n : Γ} {x : (d.shiftedFiltration ℳ p).quotient k}
    (hx : x ∈ (d.shiftedQuotientGrading ℳ p k).piece n) :
    d.quotientCoefficientMap ℳ 𝓝 p f hf k x ∈
      (d.shiftedQuotientGrading 𝓝 p k).piece n := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  rw [quotientCoefficientMap_mk]
  exact (d.mem_shiftedQuotientGrading_iff 𝓝 p).mpr
    ⟨_, d.shiftedCoefficientMap_mem_shiftedGrading ℳ 𝓝 p f hf ha, rfl⟩

end FixedQuotientGrading

section FixedCompletion

variable {Γ R M N : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ u, ℳ u ≤ (𝓝 u).comap f)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- The fixed-degree coefficient map is the canonical filtered map with identity cutoff. -/
theorem completionCoefficientMap_eq_completionMap (p : Γ) :
    d.completionCoefficientMap ℳ 𝓝 p f hf =
      (d.shiftedFiltration ℳ p).completionMap (d.shiftedFiltration 𝓝 p)
        (d.shiftedCoefficientMap ℳ 𝓝 p f hf) id monotone_id
        (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf k ha) := (rfl)

omit [DirectSum.Decomposition 𝓝] in
/-- The identity degree-map completion agrees with the fixed-degree completion.
Heterogeneous equality accounts for the target origin `PositiveDegreeMap.id d p`. -/
theorem completionCoefficientMap_heq_shiftedCompletionMap_id (p : Γ)
    (hf' : ∀ q, ℳ q ≤ (𝓝 (PositiveDegreeMap.id d q)).comap f)
    (a : d.ShiftedCoefficients ℳ p) :
    HEq (d.completionCoefficientMap ℳ 𝓝 p f hf a)
      ((PositiveDegreeMap.id d).shiftedCompletionMap ℳ 𝓝 p f hf' a) := by
  revert hf'
  let I : PositiveDegreeMap d d :=
    { toAddMonoidHom := AddMonoidHom.id Γ
      map_mem := fun h => h
      map_ne_zero := fun _ h => h
      modulus := id
      monotone_modulus := monotone_id
      degree_gt := fun _ _ h => h }
  have hI : PositiveDegreeMap.id d = I :=
    PositiveDegreeMap.ext (fun q => PositiveDegreeMap.id_apply q)
      (fun k => PositiveDegreeMap.id_modulus k)
  rw [hI]
  intro hf'
  have hm : I.shiftedMap ℳ 𝓝 p f hf' = d.shiftedCoefficientMap ℳ 𝓝 p f hf := by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [PositiveDegreeMap.coe_shiftedMap, coe_shiftedCoefficientMap]
  simp only [completionCoefficientMap_eq_completionMap,
    PositiveDegreeMap.shiftedCompletionMap_def, hm, I, AddMonoidHom.id_apply, heq_iff_eq]

/-- A fixed-degree completed map applies the original linear map to each ambient component. -/
@[simp]
theorem coe_shiftedHomogeneousComponent_completionCoefficientMap (p u : Γ)
    (x : d.ShiftedCoefficients ℳ p) :
    (d.shiftedHomogeneousComponent 𝓝 p u (d.completionCoefficientMap ℳ 𝓝 p f hf x) : N) =
      f (d.shiftedHomogeneousComponent ℳ p u x) := by
  have h := d.completionComponent_completionMap_of_injective d
    (shiftedGrading ℳ d.monoid p) (shiftedGrading 𝓝 d.monoid p)
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration 𝓝 p)
    (d.shiftedFiltration_succ ℳ p) (d.shiftedFiltration_succ 𝓝 p)
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf) id
    (fun _ _ ha => d.shiftedCoefficientMap_mem_shiftedGrading ℳ 𝓝 p f hf ha)
    id monotone_id (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf k ha)
    Function.injective_id (u - p) x
  have h' := congrArg (fun a : shiftedSubmodule 𝓝 d.monoid p => (a : N)) h
  rw [coe_shiftedCoefficientMap, coe_completionComponent_shiftedGrading,
    coe_completionComponent_shiftedGrading] at h'
  have hp : p + (u - p) = u := by abel
  rw [id_eq, hp] at h'
  simpa only [← completionCoefficientMap_eq_completionMap] using h'

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Completing a degree-preserving map agrees with its map on ordinary shifted coefficients. -/
@[simp]
theorem completionCoefficientMap_of (p : Γ) (a : shiftedSubmodule ℳ d.monoid p) :
    d.completionCoefficientMap ℳ 𝓝 p f hf ((d.shiftedFiltration ℳ p).of a) =
      (d.shiftedFiltration 𝓝 p).of (d.shiftedCoefficientMap ℳ 𝓝 p f hf a) := by
  rw [completionCoefficientMap_eq_completionMap]
  exact (d.shiftedFiltration ℳ p).completionMap_of (d.shiftedFiltration 𝓝 p)
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf) id monotone_id
    (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf k ha) a

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Degree-preserving completed maps commute with enlarging a support translate. -/
theorem completionCoefficientMap_inclusion (p q : Γ) (hpq : p - q ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    d.completionCoefficientMap ℳ 𝓝 q f hf (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedCompletedInclusion 𝓝 p q hpq (d.completionCoefficientMap ℳ 𝓝 p f hf x) := by
  have hi : (d.shiftedCoefficientMap ℳ 𝓝 q f hf).comp
      (shiftedSupportInclusion ℳ d.monoid p q hpq) =
      (shiftedSupportInclusion 𝓝 d.monoid p q hpq).comp
        (d.shiftedCoefficientMap ℳ 𝓝 p f hf) := by
    ext a
    simp only [LinearMap.comp_apply, coe_shiftedCoefficientMap, coe_shiftedSupportInclusion]
  have h₁ := ModuleFiltration.completionMap_comp
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration ℳ q)
    (shiftedSupportInclusion ℳ d.monoid p q hpq) id monotone_id
    (fun k => d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))
    (d.shiftedFiltration 𝓝 q) (d.shiftedCoefficientMap ℳ 𝓝 q f hf) id monotone_id
    (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 q f hf k ha)
  have h₂ := ModuleFiltration.completionMap_comp
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration 𝓝 p)
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf) id monotone_id
    (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf k ha)
    (d.shiftedFiltration 𝓝 q) (shiftedSupportInclusion 𝓝 d.monoid p q hpq) id monotone_id
    (fun k => d.shiftedSupportInclusion_filtered 𝓝 p q hpq (k + 1))
  simp only [hi] at h₁
  simpa only [completionCoefficientMap_eq_completionMap, shiftedCompletedInclusion_def,
    LinearMap.comp_apply] using congrArg (fun F => F x) (h₁.symm.trans h₂)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Degree-preserving completion maps compose without decomposition assumptions. -/
theorem completionCoefficientMap_comp {P : Type*} [AddCommGroup P] [Module R P]
    (ℒ : Γ → Submodule R P) (g : N →ₗ[R] P) (hg : ∀ u, 𝓝 u ≤ (ℒ u).comap g)
    (p : Γ) (x : d.ShiftedCoefficients ℳ p) :
    d.completionCoefficientMap 𝓝 ℒ p g hg (d.completionCoefficientMap ℳ 𝓝 p f hf x) =
      d.completionCoefficientMap ℳ ℒ p (g.comp f) (fun u _ ha => hg u (hf u ha)) x := by
  have hi : (d.shiftedCoefficientMap 𝓝 ℒ p g hg).comp
      (d.shiftedCoefficientMap ℳ 𝓝 p f hf) =
      d.shiftedCoefficientMap ℳ ℒ p (g.comp f) (fun u _ ha => hg u (hf u ha)) := by
    ext a
    simp only [LinearMap.comp_apply, coe_shiftedCoefficientMap]
  have h := ModuleFiltration.completionMap_comp
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration 𝓝 p)
    (d.shiftedCoefficientMap ℳ 𝓝 p f hf) id monotone_id
    (fun k _ ha => d.shiftedCoefficientMap_mem_filtration ℳ 𝓝 p f hf k ha)
    (d.shiftedFiltration ℒ p) (d.shiftedCoefficientMap 𝓝 ℒ p g hg) id monotone_id
    (fun k _ ha => d.shiftedCoefficientMap_mem_filtration 𝓝 ℒ p g hg k ha)
  simpa only [hi, Function.id_comp, completionCoefficientMap_eq_completionMap,
    LinearMap.comp_apply] using (congrArg (fun F => F x) h).symm

end FixedCompletion

section TargetTransport

variable {Γ R M N : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (e : PositiveDegrees Γ) (𝓝 : Γ → Submodule R N)

/-- Transporting the target shift across an equality commutes with completion of a filtered map.
The source filtration is arbitrary, and the target family need not decompose its ambient module. -/
theorem cast_completionMap (F : ModuleFiltration R M) (s t : Γ) (h : s = t)
    (g : M →ₗ[R] shiftedSubmodule 𝓝 e.monoid s)
    (ρ : ℕ → ℕ) (hρ : Monotone ρ)
    (hg : ∀ k, F.submodule (ρ k + 1) ≤
      ((e.shiftedFiltration 𝓝 s).submodule (k + 1)).comap g) (x : F.completion) :
    cast (congrArg (e.ShiftedCoefficients 𝓝) h)
      (F.completionMap (e.shiftedFiltration 𝓝 s) g ρ hρ hg x) =
    F.completionMap (e.shiftedFiltration 𝓝 t)
      (h ▸ g) ρ hρ (by subst t; exact hg) x := by
  subst t
  rfl

end TargetTransport

end TauCeti.PositiveDegrees

namespace TauCeti.PositiveDegreeMap

open Mei

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

/-- Identity degree and coefficient maps fix completed coefficients, accounting
for the canonically equal target origin. -/
theorem shiftedCompletionMap_id (p : Γ)
    (hf : ∀ q, ℳ q ≤ (ℳ (PositiveDegreeMap.id d q)).comap (LinearMap.id : M →ₗ[R] M))
    (x : d.ShiftedCoefficients ℳ p) :
    HEq ((PositiveDegreeMap.id d).shiftedCompletionMap ℳ ℳ p LinearMap.id hf x) x := by
  have hi : d.shiftedCoefficientMap ℳ ℳ p LinearMap.id (fun _ => le_rfl) = LinearMap.id := by
    ext b
    simp only [PositiveDegrees.coe_shiftedCoefficientMap, LinearMap.id_apply]
  have hx : d.completionCoefficientMap ℳ ℳ p LinearMap.id (fun _ => le_rfl) x = x := by
    simp only [PositiveDegrees.completionCoefficientMap_eq_completionMap, hi,
      ModuleFiltration.completionMap_id, LinearMap.id_apply]
  exact (d.completionCoefficientMap_heq_shiftedCompletionMap_id ℳ ℳ LinearMap.id
    (fun _ => le_rfl) p hf x).symm.trans (heq_of_eq hx)

end TauCeti.PositiveDegreeMap
