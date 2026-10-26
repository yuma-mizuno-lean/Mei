/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Topology
public import Mathlib.Analysis.Convex.Exposed
import Mathlib.Tactic.Linarith

/-!
# Exposed faces of transverse sweeps

Every nonempty exposed subset of a negative-ray sweep is either an exposed
subset of the base or the sweep of such a subset. For a transverse base both
possibilities are exposed: a normalized height adjusts an exposing functional
to vanish, or to be strictly positive, on the sweeping vector.

These are unsigned prism statements. No orientation, cochain relation, or
boundary operator is introduced here. The base may be unbounded and have
lineality; the exposed-subset classification does not require convexity.
-/

public section

open Mei.Convex

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A functional positive on the sweeping vector attains its maximum only
on the base, where its maximizers are unchanged. -/
theorem toExposed_sweep_of_pos (l : V →L[ℝ] ℝ) (P : Set V) {n : V}
    (hn : 0 < l n) : l.toExposed (sweep P n) = l.toExposed P := by
  ext y
  constructor
  · rintro ⟨hy, hmax⟩
    obtain ⟨x, hx, t, ht, rfl⟩ := mem_sweep_iff_exists.mp hy
    have hm := hmax x (subset_sweep P n hx)
    have ht0 : t = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul] at hm
      nlinarith
    subst t
    simp only [zero_smul, sub_zero] at hmax ⊢
    exact ⟨hx, fun z hz => hmax z (subset_sweep P n hz)⟩
  · rintro ⟨hy, hmax⟩
    refine ⟨subset_sweep P n hy, ?_⟩
    rintro z hz
    obtain ⟨x, hx, t, ht, rfl⟩ := mem_sweep_iff_exists.mp hz
    have hm := hmax x hx
    have hp := mul_nonneg ht hn.le
    simp only [map_sub, map_smul, smul_eq_mul]
    linarith

/-- A functional vanishing on the sweeping vector has precisely the swept
base maximizers as maximizers on the sweep. -/
theorem toExposed_sweep_of_eq_zero (l : V →L[ℝ] ℝ) (P : Set V) {n : V}
    (hn : l n = 0) : l.toExposed (sweep P n) = sweep (l.toExposed P) n := by
  ext y
  constructor
  · rintro ⟨hy, hmax⟩
    obtain ⟨x, hx, t, ht, rfl⟩ := mem_sweep_iff_exists.mp hy
    refine mem_sweep_iff_exists.mpr ⟨x, ⟨hx, ?_⟩, t, ht, rfl⟩
    intro z hz
    simpa only [map_sub, map_smul, smul_eq_mul, hn, mul_zero, sub_zero] using
      hmax z (subset_sweep P n hz)
  · intro hy
    obtain ⟨x, ⟨hx, hmax⟩, t, ht, rfl⟩ := mem_sweep_iff_exists.mp hy
    refine ⟨mem_sweep_iff_exists.mpr ⟨x, hx, t, ht, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨w, hw, s, hs, rfl⟩ := mem_sweep_iff_exists.mp hz
    simpa only [map_sub, map_smul, smul_eq_mul, hn, mul_zero, sub_zero] using hmax w hw

/-- A functional with a maximizer on a negative-ray sweep is nonnegative on
the sweeping vector. -/
theorem nonneg_apply_of_toExposed_sweep_nonempty (l : V →L[ℝ] ℝ) {P : Set V} {n : V}
    (hne : (l.toExposed (sweep P n)).Nonempty) : 0 ≤ l n := by
  obtain ⟨y, hy, hmax⟩ := hne
  have hm := hmax (y - (1 : ℝ) • n) (sub_smul_mem_sweep hy zero_le_one)
  simp only [map_sub, map_smul, smul_eq_mul, one_mul] at hm
  linarith

/-- Subtracting a multiple of a height constant on the base preserves all
comparisons of functional values there, and therefore preserves its maximizers. -/
theorem toExposed_sub_smul_of_eq (l f : V →L[ℝ] ℝ) (P : Set V) (a c : ℝ)
    (hfP : ∀ x ∈ P, f x = c) :
    (l - a • f).toExposed P = l.toExposed P := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    have hm := hmax y hy
    simpa only [sub_apply, smul_apply, smul_eq_mul, hfP x hx, hfP y hy,
      sub_le_sub_iff_right] using hm
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    simpa only [sub_apply, smul_apply, smul_eq_mul, hfP x hx, hfP y hy,
      sub_le_sub_iff_right] using hmax y hy

end ContinuousLinearMap

namespace IsExposed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {P G : Set V} {n : V}

/-- Every nonempty exposed subset of a negative-ray sweep is an exposed
subset of the base or the sweep of one. This direction needs no transversality. -/
theorem exists_base_or_sweep (hG : IsExposed ℝ (sweep P n) G) (hne : G.Nonempty) :
    ∃ F : Set V, F.Nonempty ∧ IsExposed ℝ P F ∧ (G = F ∨ G = sweep F n) := by
  obtain ⟨l, hl⟩ := hG hne
  change G = l.toExposed (sweep P n) at hl
  have hm : (l.toExposed (sweep P n)).Nonempty := hl ▸ hne
  have hn := l.nonneg_apply_of_toExposed_sweep_nonempty hm
  rcases eq_or_lt_of_le hn with hn | hn
  · have he : G = sweep (l.toExposed P) n :=
      hl.trans (l.toExposed_sweep_of_eq_zero P hn.symm)
    have hF : (l.toExposed P).Nonempty := by
      obtain ⟨y, hy⟩ := hne
      rw [he] at hy
      obtain ⟨x, hx, _, _, _⟩ := mem_sweep_iff_exists.mp hy
      exact ⟨x, hx⟩
    exact ⟨l.toExposed P, hF, ContinuousLinearMap.toExposed.isExposed, Or.inr he⟩
  · have he : G = l.toExposed P := hl.trans (l.toExposed_sweep_of_pos P hn)
    exact ⟨l.toExposed P, he ▸ hne, ContinuousLinearMap.toExposed.isExposed, Or.inl he⟩

end IsExposed

namespace IsExposed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {P F : Set V} {n : V}

/-- A height constant on the base and normalized on the sweeping vector makes
each exposed base subset an exposed subset of the whole sweep. -/
theorem in_sweep_of_height (hF : IsExposed ℝ P F) (f : V →L[ℝ] ℝ) (c : ℝ)
    (hfn : f n = 1) (hfP : ∀ x ∈ P, f x = c) : IsExposed ℝ (sweep P n) F := by
  intro hne
  obtain ⟨l, hl⟩ := hF hne
  change F = l.toExposed P at hl
  let k := l - (l n - 1) • f
  have hk : k.toExposed P = F :=
    (l.toExposed_sub_smul_of_eq f P (l n - 1) c hfP).trans hl.symm
  have hkn : 0 < k n := by
    dsimp only [k]
    simp only [sub_apply, smul_apply, smul_eq_mul, hfn, mul_one]
    linarith
  exact ⟨k, hk.symm.trans (k.toExposed_sweep_of_pos P hkn).symm⟩

/-- With a normalized height, sweeping an exposed base subset gives an exposed
subset of the sweep. The adjusted functional vanishes on the sweeping vector. -/
theorem sweep_of_height (hF : IsExposed ℝ P F) (f : V →L[ℝ] ℝ) (c : ℝ)
    (hfn : f n = 1) (hfP : ∀ x ∈ P, f x = c) :
    IsExposed ℝ (sweep P n) (sweep F n) := by
  intro hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, hx, _, _, _⟩ := mem_sweep_iff_exists.mp hy
  obtain ⟨l, hl⟩ := hF ⟨x, hx⟩
  change F = l.toExposed P at hl
  let k := l - l n • f
  have hk : k.toExposed P = F :=
    (l.toExposed_sub_smul_of_eq f P (l n) c hfP).trans hl.symm
  have hkn : k n = 0 := by simp [k, hfn]
  refine ⟨k, ?_⟩
  change sweep F n = k.toExposed (sweep P n)
  rw [k.toExposed_sweep_of_eq_zero P hkn, hk]

variable [FiniteDimensional ℝ V]

/-- A nonempty exposed subset with the same affine-direction dimension as its
base is the whole base. This also holds for a nonconvex base. -/
theorem eq_of_finrank_vectorSpan_eq (hF : IsExposed ℝ P F) (hne : F.Nonempty)
    (hdim : Module.finrank ℝ (vectorSpan ℝ F) = Module.finrank ℝ (vectorSpan ℝ P)) :
    F = P := by
  obtain ⟨l, hl⟩ := hF hne
  have hdir := Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hF.subset) hdim
  have hker : vectorSpan ℝ F ≤ LinearMap.ker l.toLinearMap := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    have ha' := hl ▸ ha
    have hb' := hl ▸ hb
    have hab := ha'.2 b hb'.1
    have hba := hb'.2 a ha'.1
    change l (a - b) = 0
    simp only [map_sub]
    linarith
  apply Set.Subset.antisymm hF.subset
  intro x hx
  obtain ⟨z, hz⟩ := hne
  have hxz := vsub_mem_vectorSpan ℝ hx (hF.subset hz)
  rw [← hdir] at hxz
  have hlxz := hker hxz
  have he : l x = l z := sub_eq_zero.mp (by simpa only [LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] using hlxz)
  have hz' := hl ▸ hz
  rw [hl]
  exact ⟨hx, fun y hy => by simpa only [he] using hz'.2 y hy⟩

/-- Every exposed subset of a transverse base is exposed in the whole sweep.
Empty subsets are included according to Mathlib's convention. -/
theorem in_sweep_of_transverse (hF : IsExposed ℝ P F) (hn : n ∉ vectorSpan ℝ P) :
    IsExposed ℝ (sweep P n) F := by
  intro hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height ⟨x, hF.subset hx⟩ hn
  exact hF.in_sweep_of_height ⟨f, f.continuous_of_finiteDimensional⟩ c hfn hfP ⟨x, hx⟩

/-- Sweeping preserves exposure when the sweeping vector is transverse to the base. -/
theorem sweep_of_transverse (hF : IsExposed ℝ P F) (hn : n ∉ vectorSpan ℝ P) :
    IsExposed ℝ (sweep P n) (sweep F n) := by
  intro hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, hx, _, _, _⟩ := mem_sweep_iff_exists.mp hy
  obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height ⟨x, hF.subset hx⟩ hn
  exact hF.sweep_of_height ⟨f, f.continuous_of_finiteDimensional⟩ c hfn hfP ⟨y, hy⟩

end IsExposed

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {P G : Set V} {n : V}

/-- The nonempty exposed subsets of a transverse sweep are exactly its base
faces and the sweeps of base faces. No convexity or closedness is required. -/
theorem isExposed_sweep_iff (hn : n ∉ vectorSpan ℝ P) (hG : G.Nonempty) :
    IsExposed ℝ (sweep P n) G ↔
      ∃ F : Set V, F.Nonempty ∧ IsExposed ℝ P F ∧ (G = F ∨ G = sweep F n) := by
  constructor
  · exact fun hex => hex.exists_base_or_sweep hG
  · rintro ⟨F, _, hF, rfl | rfl⟩
    · exact hF.in_sweep_of_transverse hn
    · exact hF.sweep_of_transverse hn

/-- The codimension-one nonempty exposed subsets of a transverse sweep are
exactly the base and sweeps of codimension-one exposed subsets of the base.
Dimensions are relative to the affine direction, so lineality is allowed. -/
theorem isExposed_sweep_codimension_one_iff (hP : P.Nonempty)
    (hn : n ∉ vectorSpan ℝ P) (hG : G.Nonempty) :
    (IsExposed ℝ (sweep P n) G ∧
      Module.finrank ℝ (vectorSpan ℝ G) + 1 =
        Module.finrank ℝ (vectorSpan ℝ (sweep P n))) ↔
    G = P ∨ ∃ F : Set V, F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (vectorSpan ℝ F) + 1 = Module.finrank ℝ (vectorSpan ℝ P) ∧
      G = sweep F n := by
  have hdimP := finrank_sweep hP hn
  constructor
  · rintro ⟨hex, hdim⟩
    obtain ⟨F, hFne, hF, rfl | rfl⟩ := hex.exists_base_or_sweep hG
    · left
      rw [hdimP] at hdim
      exact hF.eq_of_finrank_vectorSpan_eq hFne (Nat.add_right_cancel hdim)
    · right
      have hnF : n ∉ vectorSpan ℝ F := fun hn' => hn (vectorSpan_mono ℝ hF.subset hn')
      rw [finrank_sweep hFne hnF, hdimP] at hdim
      exact ⟨F, hFne, hF, Nat.add_right_cancel hdim, rfl⟩
  · rintro (rfl | ⟨F, hFne, hF, hdim, rfl⟩)
    · exact ⟨(IsExposed.refl _).in_sweep_of_transverse hn, hdimP.symm⟩
    · have hnF : n ∉ vectorSpan ℝ F := fun hn' => hn (vectorSpan_mono ℝ hF.subset hn')
      refine ⟨hF.sweep_of_transverse hn, ?_⟩
      rw [finrank_sweep hFne hnF, hdimP, hdim]

end Mei.Convex
