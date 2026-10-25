/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Ray.Basic

/-!
# Transport of supported primitive rays

An additive map preserving allowed nonzero degrees sends a supported primitive
generator to a positive integer multiple of a unique target supported generator.
The generator itself need not be allowed in either monoid. The induced ray map
and its integer multiplier respect identity and composition, and transport actual
ray degrees with any cutoff bound satisfied by the original additive map.

Only the target integer module must be free; neither finite rank nor injectivity
of the additive map is required. Primitive decomposition uses
`TauCeti.exists_eq_zsmul_isPrimitive`.
-/

public section

namespace Mei.SupportedRay

variable {N M K : Type*} [AddCommGroup N] [AddCommGroup M] [AddCommGroup K]
variable {d : PositiveDegrees N} {e : PositiveDegrees M} {q : PositiveDegrees K}

/-- A map that does not kill allowed nonzero degrees cannot kill a supported generator,
even if that generator does not belong to the allowed monoid. -/
theorem map_generator_ne_zero (w : SupportedRay d) (f : N →+ M)
    (h0 : ∀ n ∈ d.monoid, n ≠ 0 → f n ≠ 0) : f w.generator ≠ 0 := by
  obtain ⟨n, hn⟩ := w.rayDegrees_nonempty
  have hn' := mem_rayDegrees.mp hn
  have hfn := h0 n hn'.1 (ne_zero_of_mem_rayDegrees hn)
  obtain ⟨a, _, rfl⟩ := hn'.2
  intro h
  exact hfn (by simp [map_zsmul, h])

section FreeTarget

variable [Module.Free ℤ M]
variable (w : SupportedRay d) (f : N →+ M)
variable (hP : ∀ n ∈ d.monoid, f n ∈ e.monoid)
variable (h0 : ∀ n ∈ d.monoid, n ≠ 0 → f n ≠ 0)

include hP h0 in
private theorem exists_map_generator :
    ∃ v : SupportedRay e, ∃ b : ℤ, 0 < b ∧ f w.generator = b • v.generator := by
  obtain ⟨b, v, hb, hv, hfv⟩ :=
    TauCeti.exists_eq_zsmul_isPrimitive (w.map_generator_ne_zero f h0)
  obtain ⟨a, ha, ham⟩ := w.supported
  have hab : (a * b) • v ∈ e.monoid := by
    simpa [map_zsmul, hfv, mul_smul] using hP _ ham
  exact ⟨⟨v, hv, a * b, mul_pos ha hb, hab⟩, b, hb, hfv⟩

/-- The target supported ray of an additive map preserving allowed nonzero degrees. -/
noncomputable def map : SupportedRay e :=
  (exists_map_generator w f hP h0).choose

/-- The positive integer multiplier of the target primitive generator. -/
noncomputable def mapMultiplier : ℤ :=
  (exists_map_generator w f hP h0).choose_spec.choose

/-- The multiplier of a transported supported ray is positive. -/
theorem mapMultiplier_pos : 0 < w.mapMultiplier f hP h0 :=
  (exists_map_generator w f hP h0).choose_spec.choose_spec.1

/-- The image of the ambient generator, including when it is not an allowed degree. -/
theorem map_generator :
    f w.generator = w.mapMultiplier f hP h0 • (w.map f hP h0).generator :=
  (exists_map_generator w f hP h0).choose_spec.choose_spec.2

/-- Integer multiples are reindexed by multiplying their integer multipliers. -/
theorem map_zsmul_generator (a : ℤ) :
    f (a • w.generator) = (a * w.mapMultiplier f hP h0) •
      (w.map f hP h0).generator := by
  rw [map_zsmul, w.map_generator f hP h0, mul_smul]

/-- Actual allowed degrees map into the degrees of the transported ray. -/
theorem map_mem_rayDegrees {n : N} (hn : n ∈ w.rayDegrees) :
    f n ∈ (w.map f hP h0).rayDegrees := by
  obtain ⟨hnP, a, ha, rfl⟩ := mem_rayDegrees.mp hn
  exact mem_rayDegrees.mpr ⟨hP _ hnP, a * w.mapMultiplier f hP h0,
    mul_pos ha (w.mapMultiplier_pos f hP h0), w.map_zsmul_generator f hP h0 a⟩

/-- A positive-multiple equation characterizes the transported primitive ray. -/
theorem map_eq_iff (v : SupportedRay e) :
    w.map f hP h0 = v ↔ ∃ b : ℤ, 0 < b ∧ f w.generator = b • v.generator := by
  let : HasUniqueDiv M := .of_isTorsionFree ℤ M
  constructor
  · rintro rfl
    exact ⟨_, w.mapMultiplier_pos f hP h0, w.map_generator f hP h0⟩
  · rintro ⟨b, hb, hfv⟩
    exact ext ((w.map f hP h0).isPrimitive.eq_of_pos_zsmul_eq v.isPrimitive
      (w.mapMultiplier_pos f hP h0) hb ((w.map_generator f hP h0).symm.trans hfv))

/-- The integer multiplier is characterized by its generator equation. -/
theorem mapMultiplier_eq_iff (b : ℤ) :
    w.mapMultiplier f hP h0 = b ↔ f w.generator = b • (w.map f hP h0).generator := by
  rw [w.map_generator f hP h0]
  exact ⟨fun h => congrArg (fun a : ℤ => a • (w.map f hP h0).generator) h,
    fun h => (w.map f hP h0).isPrimitive.zsmul_left_injective h⟩

include hP h0 in
/-- The ray and its positive multiplier are jointly unique. -/
theorem existsUnique_map_generator :
    ∃! p : SupportedRay e × ℤ, 0 < p.2 ∧ f w.generator = p.2 • p.1.generator := by
  refine ⟨(w.map f hP h0, w.mapMultiplier f hP h0),
    ⟨w.mapMultiplier_pos f hP h0, w.map_generator f hP h0⟩, ?_⟩
  rintro ⟨v, b⟩ ⟨hb, hfv⟩
  have hv := (w.map_eq_iff f hP h0 v).mpr ⟨b, hb, hfv⟩
  subst v
  exact Prod.ext rfl ((w.mapMultiplier_eq_iff f hP h0 b).mpr hfv).symm

/-- Two rays agree after transport exactly when an actual degree maps to the second ray. -/
theorem map_eq_iff_exists_mem_rayDegrees (v : SupportedRay e) :
    w.map f hP h0 = v ↔ ∃ n ∈ w.rayDegrees, f n ∈ v.rayDegrees := by
  let : HasUniqueDiv M := .of_isTorsionFree ℤ M
  constructor
  · rintro rfl
    obtain ⟨n, hn⟩ := w.rayDegrees_nonempty
    exact ⟨n, hn, w.map_mem_rayDegrees f hP h0 hn⟩
  · rintro ⟨n, hn, hv⟩
    exact eq_of_mem_rayDegrees (w.map_mem_rayDegrees f hP h0 hn) hv

end FreeTarget

/-- Truncating the image of a ray uses exactly the original map's cutoff modulus.
Only actual allowed source degrees are cut off, even for nonsaturated monoids. -/
theorem image_rayDegrees_inter_cutoff (w : SupportedRay d) (f : N →+ M)
    {modulus : ℕ → ℕ}
    (hmod : ∀ (k : ℕ) (n : N), n ∈ d.monoid → e.degree (f n) ≤ k →
      d.degree n ≤ modulus k)
    (k : ℕ) :
    (f '' w.rayDegrees) ∩ e.cutoff k =
      (f '' (w.rayDegrees ∩ d.cutoff (modulus k))) ∩ e.cutoff k := by
  ext m
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, hk⟩
    have hnP := (mem_rayDegrees.mp hn).1
    have hbound := hmod k n hnP (e.mem_cutoff.mp hk).2
    exact ⟨⟨n, ⟨hn, d.mem_cutoff.mpr ⟨hnP, hbound⟩⟩, rfl⟩, hk⟩
  · rintro ⟨⟨n, hn, rfl⟩, hk⟩
    exact ⟨⟨n, hn.1, rfl⟩, hk⟩

section Identity

variable [Module.Free ℤ N] (w : SupportedRay d)

/-- The identity additive map fixes supported rays. -/
@[simp]
theorem map_id : w.map (AddMonoidHom.id N) (fun _ h => h) (fun _ _ h => h) = w := by
  exact (w.map_eq_iff _ _ _ w).mpr ⟨1, by omega, by simp⟩

/-- The identity map has primitive multiplier one. -/
@[simp]
theorem mapMultiplier_id :
    w.mapMultiplier (AddMonoidHom.id N) (fun _ h => h) (fun _ _ h => h) = 1 := by
  apply (w.mapMultiplier_eq_iff _ _ _ 1).mpr
  simp

end Identity

section Composition

variable [Module.Free ℤ M] [Module.Free ℤ K]
variable (w : SupportedRay d) (f : N →+ M) (g : M →+ K)
variable (hfP : ∀ n ∈ d.monoid, f n ∈ e.monoid)
variable (hf0 : ∀ n ∈ d.monoid, n ≠ 0 → f n ≠ 0)
variable (hgP : ∀ n ∈ e.monoid, g n ∈ q.monoid)
variable (hg0 : ∀ n ∈ e.monoid, n ≠ 0 → g n ≠ 0)

/-- Transport of supported rays respects composition, including nonprimitive images. -/
@[simp]
theorem map_comp :
    w.map (g.comp f) (fun n hn => hgP _ (hfP n hn))
      (fun n hn hne => hg0 _ (hfP n hn) (hf0 n hn hne)) =
      (w.map f hfP hf0).map g hgP hg0 := by
  apply (w.map_eq_iff _ _ _ _).mpr
  refine ⟨w.mapMultiplier f hfP hf0 * (w.map f hfP hf0).mapMultiplier g hgP hg0,
    mul_pos (w.mapMultiplier_pos f hfP hf0)
      ((w.map f hfP hf0).mapMultiplier_pos g hgP hg0), ?_⟩
  simp only [AddMonoidHom.comp_apply]
  rw [w.map_generator f hfP hf0, map_zsmul,
    (w.map f hfP hf0).map_generator g hgP hg0, mul_smul]

/-- Primitive multipliers multiply under composition in the original order. -/
@[simp]
theorem mapMultiplier_comp :
    w.mapMultiplier (g.comp f) (fun n hn => hgP _ (hfP n hn))
      (fun n hn hne => hg0 _ (hfP n hn) (hf0 n hn hne)) =
      w.mapMultiplier f hfP hf0 * (w.map f hfP hf0).mapMultiplier g hgP hg0 := by
  apply (w.mapMultiplier_eq_iff _ _ _ _).mpr
  simp only [map_comp, AddMonoidHom.comp_apply]
  rw [w.map_generator f hfP hf0, map_zsmul,
    (w.map f hfP hf0).map_generator g hgP hg0, mul_smul]

end Composition

end Mei.SupportedRay
