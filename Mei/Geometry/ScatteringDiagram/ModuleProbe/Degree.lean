/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Map
public import Mei.Algebra.PositiveDegrees.Ray.Basic

/-!
# Positive degrees for module probes

For a positive monoid `P` in `Γ` and an arbitrary shift `p`, the module probe uses
the monoid `{(n + c • p, c, 0) | n ∈ P, 0 ≤ c}` in `Γ × ℤ × ℤ`.
Its degree is `δ(x) + (1 - δ(p))c`, hence `δ(n) + c` on this monoid.
We prove positivity and finite cutoffs without a finite-generation or saturation
assumption on `P`. Charge one at extended order `k + 1` is exactly the translate
by `p` of the original order-`k` cutoff.

The original supported rays lift with charge zero, while every allowed charge-one
degree is primitive and supplies a supported ray. Thus charge-one degrees remain
nonzero even when their original spatial direction vanishes.

The monoid is constructed with Mathlib's `AddSubmonoid.map` and `AddSubmonoid.prod`;
the ray constructions use `TauCeti.IsPrimitive` and `Mei.SupportedRay`.
The motivating use of the semidirect Lie algebra to encode coefficient actions
is described in Travis Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3, arXiv:1503.06183v5.
-/

public section

namespace Mei.ModuleProbe

variable {Γ : Type*} [AddCommGroup Γ] (d : PositiveDegrees Γ) (p : Γ)

/-- The additive inclusion of relative degrees and module charges in the
extended degree group. The final coordinate is reserved for the probe normal. -/
def degreeEmbedding : (Γ × ℤ) →+ (Γ × ℤ × ℤ) where
  toFun a := (a.1 + a.2 • p, a.2, 0)
  map_zero' := by simp
  map_add' := by intros; simp [add_zsmul]; abel

/-- Evaluation of the relative-degree inclusion. -/
@[simp]
theorem degreeEmbedding_apply (n : Γ) (c : ℤ) :
    degreeEmbedding p (n, c) = (n + c • p, c, 0) := (rfl)

/-- Relative degree and charge are recovered uniquely from their image. -/
theorem degreeEmbedding_injective : Function.Injective (degreeEmbedding p) := by
  rintro ⟨n, c⟩ ⟨n', c'⟩ h
  have hc : c = c' := congrArg (fun a => a.2.1) h
  have hn := congrArg Prod.fst h
  simp only [degreeEmbedding_apply] at hn
  exact Prod.ext (add_right_cancel (hc ▸ hn)) hc

/-- The allowed extended degrees of a module probe with initial degree `p`. -/
def degreeMonoid : AddSubmonoid (Γ × ℤ × ℤ) :=
  (d.monoid.prod (AddSubmonoid.nonneg ℤ)).map (degreeEmbedding p)

/-- An extended degree is allowed exactly when its charge is nonnegative,
its last coordinate vanishes, and its relative degree belongs to `P`. -/
@[simp]
theorem mem_degreeMonoid (x : Γ) (c l : ℤ) :
    (x, c, l) ∈ degreeMonoid d p ↔ x - c • p ∈ d.monoid ∧ 0 ≤ c ∧ l = 0 := by
  constructor
  · rintro ⟨⟨n, a⟩, ⟨hn, ha⟩, h⟩
    have hx : n + a • p = x := congrArg Prod.fst h
    have hc : a = c := congrArg (fun b => b.2.1) h
    have hl : (0 : ℤ) = l := congrArg (fun b => b.2.2) h
    subst c
    subst x
    exact ⟨by simpa using hn, ha, hl.symm⟩
  · rintro ⟨hx, hc, rfl⟩
    exact ⟨(x - c • p, c), ⟨hx, hc⟩, by simp⟩

/-- The extended additive degree, correcting the shift by the module charge. -/
def degree : (Γ × ℤ × ℤ) →+ ℤ where
  toFun a := d.degree a.1 + (1 - d.degree p) * a.2.1
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]; ring

/-- The extended degree on arbitrary ambient coordinates. -/
@[simp]
theorem degree_apply (x : Γ) (c l : ℤ) :
    degree d p (x, c, l) = d.degree x + (1 - d.degree p) * c := (rfl)

/-- On relative degree `n` and charge `c`, the extended degree is `δ(n) + c`. -/
theorem degree_degreeEmbedding (n : Γ) (c : ℤ) :
    degree d p (degreeEmbedding p (n, c)) = d.degree n + c := by
  simp [map_zsmul]
  ring

/-- On ambient coordinates, the extended degree is relative degree plus charge. -/
theorem degree_eq_relative (x : Γ) (c l : ℤ) :
    degree d p (x, c, l) = d.degree (x - c • p) + c := by
  simp [map_zsmul]
  ring

private theorem finite_degree_le (k : ℕ) :
    Set.Finite {a | a ∈ degreeMonoid d p ∧ degree d p a ≤ k} := by
  apply (((d.finite_cutoff k).prod
    (Set.finite_Icc (a := (0 : ℤ)) (b := k))).image (degreeEmbedding p)).subset
  rintro ⟨x, c, l⟩ ⟨hm, hk⟩
  obtain ⟨hn, hc, rfl⟩ := (mem_degreeMonoid d p x c l).mp hm
  rw [degree_eq_relative] at hk
  have hn0 := d.degree_nonneg hn
  refine ⟨(x - c • p, c), ⟨d.mem_cutoff.mpr ⟨hn, ?_⟩, ⟨hc, by omega⟩⟩, by simp⟩
  dsimp only
  omega

/-- Positive degree data for a module probe. The shift may have any ambient
degree, including negative degree or degree outside the positive monoid. -/
def positiveDegrees : PositiveDegrees (Γ × ℤ × ℤ) where
  monoid := degreeMonoid d p
  degree := degree d p
  degree_pos := by
    rintro ⟨x, c, l⟩ hm hne
    obtain ⟨hn, hc, rfl⟩ := (mem_degreeMonoid d p x c l).mp hm
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
theorem mem_positiveDegrees_monoid (x : Γ) (c l : ℤ) :
    (x, c, l) ∈ (positiveDegrees d p).monoid ↔
      x - c • p ∈ d.monoid ∧ 0 ≤ c ∧ l = 0 := mem_degreeMonoid d p x c l

/-- The degree functional of the probe positive data. -/
@[simp]
theorem positiveDegrees_degree (x : Γ) (c l : ℤ) :
    (positiveDegrees d p).degree (x, c, l) = d.degree x + (1 - d.degree p) * c := (rfl)

/-- Charge one at extended order `k + 1` is relative order `k`. -/
theorem chargeOne_mem_cutoff (q : Γ) (k : ℕ) :
    (q, 1, 0) ∈ (positiveDegrees d p).cutoff (k + 1) ↔ q - p ∈ d.cutoff k := by
  simp only [PositiveDegrees.mem_cutoff, mem_positiveDegrees_monoid, one_smul,
    positiveDegrees_degree, mul_one, zero_le_one, and_self, and_true, Nat.cast_add,
    Nat.cast_one, map_sub]
  exact and_congr_right fun _ => by omega

/-- The charge-zero embedding preserves degree cutoffs with identity modulus. -/
def baseMap : PositiveDegreeMap d (positiveDegrees d p) where
  toAddMonoidHom :=
    { toFun := fun n => (n, 0, 0)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_mem hn := by simpa using hn
  map_ne_zero _ hn h := hn (congrArg Prod.fst h)
  modulus := id
  monotone_modulus := monotone_id
  degree_gt k hn h := by simpa using h

/-- The base map adds two zero coordinates. -/
@[simp]
theorem baseMap_apply (n : Γ) : baseMap d p n = (n, 0, 0) := (rfl)

/-- The base map has the same cutoff on source and target. -/
@[simp]
theorem baseMap_modulus (k : ℕ) : (baseMap d p).modulus k = k := (rfl)

/-- Original primitive supported rays lift without changing their generators
or introducing a module charge. No saturation of the original monoid is needed. -/
def baseRay (w : SupportedRay d) : SupportedRay (positiveDegrees d p) where
  generator := (w.generator, 0, 0)
  isPrimitive := by
    obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp w.isPrimitive
    exact TauCeti.isPrimitive_def.mpr ⟨f.comp (LinearMap.fst ℤ Γ (ℤ × ℤ)), hf⟩
  supported := by
    obtain ⟨a, ha, hn⟩ := w.supported
    exact ⟨a, ha, by simpa using hn⟩

/-- The lifted base ray has the original generator in charge zero. -/
@[simp]
theorem baseRay_generator (w : SupportedRay d) :
    (baseRay d p w).generator = (w.generator, 0, 0) := (rfl)

/-- Actual degrees of a lifted base ray are exactly the lifted original degrees. -/
@[simp]
theorem mem_baseRay_rayDegrees (w : SupportedRay d) (n : Γ) (c l : ℤ) :
    (n, c, l) ∈ (baseRay d p w).rayDegrees ↔ n ∈ w.rayDegrees ∧ c = 0 ∧ l = 0 := by
  simp only [SupportedRay.mem_rayDegrees, mem_positiveDegrees_monoid, baseRay_generator,
    Prod.smul_mk, smul_zero, Prod.mk.injEq]
  constructor
  · rintro ⟨hn, a, ha, hna, rfl, rfl⟩
    exact ⟨⟨by simpa using hn.1, a, ha, hna⟩, rfl, rfl⟩
  · rintro ⟨⟨hn, a, ha, hna⟩, rfl, rfl⟩
    exact ⟨by simpa using hn, a, ha, hna, rfl, rfl⟩

/-- An allowed charge-one degree is primitive, since the charge functional
takes the value one on it. It therefore indexes its own supported module ray. -/
def moduleRay (q : Γ) (hq : q - p ∈ d.monoid) : SupportedRay (positiveDegrees d p) :=
  SupportedRay.ofMem (q, 1, 0) (by simpa using hq)
    (TauCeti.isPrimitive_def.mpr
      ⟨(LinearMap.fst ℤ ℤ ℤ).comp (LinearMap.snd ℤ Γ (ℤ × ℤ)), rfl⟩)

/-- The generator of the module ray is its charge-one degree. -/
@[simp]
theorem moduleRay_generator (q : Γ) (hq : q - p ∈ d.monoid) :
    (moduleRay d p q hq).generator = (q, 1, 0) := SupportedRay.generator_ofMem _ _ _

/-- A module ray meets charge one only at its generator. -/
@[simp]
theorem chargeOne_mem_moduleRay (q : Γ) (hq : q - p ∈ d.monoid) (x : Γ) :
    (x, 1, 0) ∈ (moduleRay d p q hq).rayDegrees ↔ x = q := by
  simp only [SupportedRay.mem_rayDegrees, moduleRay_generator, Prod.smul_mk,
    zsmul_eq_mul, Int.cast_id, mul_one, smul_zero, Prod.mk.injEq, and_true]
  constructor
  · rintro ⟨_, a, _, hx, ha⟩
    subst a
    simpa using hx
  · rintro rfl
    exact ⟨by simpa using hq, 1, by omega, by simp, rfl⟩

end Mei.ModuleProbe
