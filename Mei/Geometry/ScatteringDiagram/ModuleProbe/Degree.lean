/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.FinitelyGenerated
public import Mei.Algebra.PositiveDegrees.Ray.Basic

/-!
# Positive degrees for module probes

For a positive monoid `P` in `Γ` and an arbitrary shift `p`, the module probe uses
the monoid `{(n + c • p, c) | n ∈ P, 0 ≤ c}` in `Γ × ℤ`.
Its degree is `δ(x) + (1 - δ(p))c`, hence `δ(n) + c` on this monoid.
We prove positivity and finite cutoffs without a finite-generation or saturation
assumption on `P`. Charge one at extended order `k + 1` is exactly the translate
by `p` of the original order-`k` cutoff.

The original supported rays lift with charge zero, while every allowed charge-one
degree is primitive and supplies a supported ray. Thus charge-one degrees remain
nonzero even when their original spatial direction vanishes.

The monoid is constructed with Mathlib's `AddSubmonoid.map` and `AddSubmonoid.prod`;
the ray constructions use `TauCeti.IsPrimitive` and `TauCeti.SupportedRay`.
The motivating use of the semidirect Lie algebra to encode coefficient actions
is described in Travis Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3, arXiv:1503.06183v5.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap SupportedRay)

namespace Mei.ModuleProbe

variable {Γ : Type*} [AddCommGroup Γ] (d : PositiveDegrees Γ) (p : Γ)

/-- The additive inclusion of relative degrees and module charges in the
extended degree group. The module charge is the second coordinate. -/
def degreeEmbedding : (Γ × ℤ) →+ (Γ × ℤ) where
  toFun a := (a.1 + a.2 • p, a.2)
  map_zero' := by simp
  map_add' := by intros; simp [add_zsmul]; abel

/-- Evaluation of the relative-degree inclusion. -/
@[simp]
theorem degreeEmbedding_apply (n : Γ) (c : ℤ) :
    degreeEmbedding p (n, c) = (n + c • p, c) := (rfl)

/-- Relative degree and charge are recovered uniquely from their image. -/
theorem degreeEmbedding_injective : Function.Injective (degreeEmbedding p) := by
  rintro ⟨n, c⟩ ⟨n', c'⟩ h
  have hc : c = c' := congrArg Prod.snd h
  have hn := congrArg Prod.fst h
  simp only [degreeEmbedding_apply] at hn
  exact Prod.ext (add_right_cancel (hc ▸ hn)) hc

/-- The allowed extended degrees of a module probe with initial degree `p`. -/
def degreeMonoid : AddSubmonoid (Γ × ℤ) :=
  (d.monoid.prod (AddSubmonoid.nonneg ℤ)).map (degreeEmbedding p)

/-- An extended degree is allowed exactly when its charge is nonnegative
and its relative degree belongs to `P`. -/
@[simp]
theorem mem_degreeMonoid (x : Γ) (c : ℤ) :
    (x, c) ∈ degreeMonoid d p ↔ x - c • p ∈ d.monoid ∧ 0 ≤ c := by
  constructor
  · rintro ⟨⟨n, a⟩, ⟨hn, ha⟩, h⟩
    have hx : n + a • p = x := congrArg Prod.fst h
    have hc : a = c := congrArg Prod.snd h
    subst c
    subst x
    exact ⟨by simpa using hn, ha⟩
  · rintro ⟨hx, hc⟩
    exact ⟨(x - c • p, c), ⟨hx, hc⟩, by simp⟩

/-- The extended additive degree, correcting the shift by the module charge. -/
def degree : (Γ × ℤ) →+ ℤ where
  toFun a := d.degree a.1 + (1 - d.degree p) * a.2
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]; ring

/-- The extended degree on arbitrary ambient coordinates. -/
@[simp]
theorem degree_apply (x : Γ) (c : ℤ) :
    degree d p (x, c) = d.degree x + (1 - d.degree p) * c := (rfl)

/-- On relative degree `n` and charge `c`, the extended degree is `δ(n) + c`. -/
theorem degree_degreeEmbedding (n : Γ) (c : ℤ) :
    degree d p (degreeEmbedding p (n, c)) = d.degree n + c := by
  simp [map_zsmul]
  ring

/-- On ambient coordinates, the extended degree is relative degree plus charge. -/
theorem degree_eq_relative (x : Γ) (c : ℤ) :
    degree d p (x, c) = d.degree (x - c • p) + c := by
  simp [map_zsmul]
  ring

private theorem finite_degree_le (k : ℕ) :
    Set.Finite {a | a ∈ degreeMonoid d p ∧ degree d p a ≤ k} := by
  apply (((d.finite_cutoff k).prod
    (Set.finite_Icc (a := (0 : ℤ)) (b := k))).image (degreeEmbedding p)).subset
  rintro ⟨x, c⟩ ⟨hm, hk⟩
  obtain ⟨hn, hc⟩ := (mem_degreeMonoid d p x c).mp hm
  rw [degree_eq_relative] at hk
  have hn0 := d.degree_nonneg hn
  refine ⟨(x - c • p, c), ⟨d.mem_cutoff.mpr ⟨hn, ?_⟩, ⟨hc, by omega⟩⟩, by simp⟩
  dsimp only
  omega

/-- Positive degree data for a module probe. The shift may have any ambient
degree, including negative degree or degree outside the positive monoid. -/
def positiveDegrees : PositiveDegrees (Γ × ℤ) where
  monoid := degreeMonoid d p
  degree := degree d p
  degree_pos := by
    rintro ⟨x, c⟩ hm hne
    obtain ⟨hn, hc⟩ := (mem_degreeMonoid d p x c).mp hm
    rw [degree_eq_relative]
    have hn0 := d.degree_nonneg hn
    by_cases hc0 : c = 0
    · subst c
      simp only [zero_smul, sub_zero] at hn ⊢
      simpa using d.degree_pos hn (by intro hx; subst x; exact hne rfl)
    · omega
  finite_le := finite_degree_le d p

/-- Membership in the positive monoid uses the relative degree. -/
@[simp]
theorem mem_positiveDegrees_monoid (x : Γ) (c : ℤ) :
    (x, c) ∈ (positiveDegrees d p).monoid ↔
      x - c • p ∈ d.monoid ∧ 0 ≤ c := mem_degreeMonoid d p x c

/-- The degree functional of the probe positive data. -/
@[simp]
theorem positiveDegrees_degree (x : Γ) (c : ℤ) :
    (positiveDegrees d p).degree (x, c) = d.degree x + (1 - d.degree p) * c := (rfl)

/-- Charge one at extended order `k + 1` is relative order `k`. -/
theorem chargeOne_mem_cutoff (q : Γ) (k : ℕ) :
    (q, 1) ∈ (positiveDegrees d p).cutoff (k + 1) ↔ q - p ∈ d.cutoff k := by
  simp only [PositiveDegrees.mem_cutoff, mem_positiveDegrees_monoid, one_smul,
    positiveDegrees_degree, mul_one, zero_le_one, and_true, Nat.cast_add,
    Nat.cast_one, map_sub]
  exact and_congr_right fun _ => by omega

/-- The charge-zero embedding preserves degree cutoffs with identity modulus. -/
def baseMap : PositiveDegreeMap d (positiveDegrees d p) where
  toAddMonoidHom :=
    { toFun := fun n => (n, 0)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_mem hn := by simpa using hn
  map_ne_zero _ hn h := hn (congrArg Prod.fst h)
  modulus := id
  monotone_modulus := monotone_id
  degree_gt k hn h := by simpa using h

/-- The base map adds a zero module charge. -/
@[simp]
theorem baseMap_apply (n : Γ) : baseMap d p n = (n, 0) := (rfl)

/-- The base map has the same cutoff on source and target. -/
@[simp]
theorem baseMap_modulus (k : ℕ) : (baseMap d p).modulus k = k := (rfl)

/-- Original primitive supported rays lift without changing their generators
or introducing a module charge. No saturation of the original monoid is needed. -/
def baseRay (w : SupportedRay d) : SupportedRay (positiveDegrees d p) where
  generator := (w.generator, 0)
  isPrimitive := by
    obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp w.isPrimitive
    exact TauCeti.isPrimitive_def.mpr ⟨f.comp (LinearMap.fst ℤ Γ ℤ), hf⟩
  supported := by
    obtain ⟨a, ha, hn⟩ := w.supported
    exact ⟨a, ha, by simpa using hn⟩

/-- The lifted base ray has the original generator in charge zero. -/
@[simp]
theorem baseRay_generator (w : SupportedRay d) :
    (baseRay d p w).generator = (w.generator, 0) := (rfl)

/-- Actual degrees of a lifted base ray are exactly the lifted original degrees. -/
@[simp]
theorem mem_baseRay_rayDegrees (w : SupportedRay d) (n : Γ) (c : ℤ) :
    (n, c) ∈ (baseRay d p w).rayDegrees ↔ n ∈ w.rayDegrees ∧ c = 0 := by
  simp only [SupportedRay.mem_rayDegrees, mem_positiveDegrees_monoid, baseRay_generator,
    Prod.smul_mk, smul_zero, Prod.mk.injEq]
  constructor
  · rintro ⟨hn, a, ha, hna, rfl⟩
    exact ⟨⟨by simpa using hn.1, a, ha, hna⟩, rfl⟩
  · rintro ⟨⟨hn, a, ha, hna⟩, rfl⟩
    exact ⟨by simpa using hn, a, ha, hna, rfl⟩

/-- An allowed charge-one degree is primitive, since the charge functional
takes the value one on it. It therefore indexes its own supported module ray. -/
def moduleRay (q : Γ) (hq : q - p ∈ d.monoid) : SupportedRay (positiveDegrees d p) :=
  SupportedRay.ofMem (q, 1) (by simpa using hq)
    (TauCeti.isPrimitive_def.mpr ⟨LinearMap.snd ℤ Γ ℤ, rfl⟩)

/-- The generator of the module ray is its charge-one degree. -/
@[simp]
theorem moduleRay_generator (q : Γ) (hq : q - p ∈ d.monoid) :
    (moduleRay d p q hq).generator = (q, 1) := SupportedRay.generator_ofMem _ _ _

/-- A module ray meets charge one only at its generator. -/
@[simp]
theorem chargeOne_mem_moduleRay (q : Γ) (hq : q - p ∈ d.monoid) (x : Γ) :
    (x, 1) ∈ (moduleRay d p q hq).rayDegrees ↔ x = q := by
  simp only [SupportedRay.mem_rayDegrees, moduleRay_generator, Prod.smul_mk,
    zsmul_eq_mul, Int.cast_id, mul_one, Prod.mk.injEq]
  constructor
  · rintro ⟨_, a, _, hx, ha⟩
    subst a
    simpa using hx
  · rintro rfl
    exact ⟨by simpa using hq, 1, by omega, by simp, rfl⟩

/-- A supported ray meeting charge zero is the lift of an original supported ray.
The original primitive generator need not itself belong to the positive monoid. -/
theorem exists_baseRay_eq_of_mem_rayDegrees (w : SupportedRay (positiveDegrees d p))
    {n : Γ} (hn : (n, 0) ∈ w.rayDegrees) :
    ∃ v : SupportedRay d, w = baseRay d p v := by
  obtain ⟨hn, a, ha, he⟩ := SupportedRay.mem_rayDegrees.mp hn
  have hc : w.generator.2 = 0 := by
    have := congrArg Prod.snd he
    simpa [ha.ne'] using this
  have hw : w.generator = (w.generator.1, 0) := Prod.ext rfl hc
  have hp : TauCeti.IsPrimitive w.generator.1 := by
    obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp w.isPrimitive
    refine TauCeti.isPrimitive_def.mpr ⟨f.comp (LinearMap.inl ℤ Γ ℤ), ?_⟩
    rw [hw] at hf
    exact hf
  have hm : a • w.generator.1 ∈ d.monoid := by
    have hn' : n ∈ d.monoid := by simpa using hn
    have he' : n = a • w.generator.1 := congrArg Prod.fst he
    rwa [← he']
  exact ⟨⟨w.generator.1, hp, a, ha, hm⟩, SupportedRay.ext hw⟩

/-- A ray meeting charge one is the module ray of that very degree: positive
integer multiplication cannot create charge one from a different generator. -/
theorem eq_moduleRay_of_mem_rayDegrees (w : SupportedRay (positiveDegrees d p))
    {q : Γ} (hq : q - p ∈ d.monoid) (hn : (q, 1) ∈ w.rayDegrees) :
    w = moduleRay d p q hq := by
  obtain ⟨_, a, ha, he⟩ := SupportedRay.mem_rayDegrees.mp hn
  have hc : (1 : ℤ) = a * w.generator.2 := by
    simpa using congrArg Prod.snd he
  have ha1 : a = 1 := by
    have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) ⟨w.generator.2, hc⟩
    omega
  apply SupportedRay.ext
  simpa only [ha1, one_smul, moduleRay_generator] using he.symm

end Mei.ModuleProbe
