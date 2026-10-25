/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Module

/-!
# Transverse sweeps

The sweep of a set `P` in the direction `n` is `P - ℝ≥0 • n`. When `n` is
outside the affine direction of `P`, a normalized linear height recovers both
prism coordinates. This also gives closedness without a compactness hypothesis.

The height, uniqueness, outgoingness, closedness and dimension arguments are adapted
from the roadmap's
[sweep prototype](https://github.com/yuma-mizuno/TauCetiRoadmap/blob/9b9115dca5539f86f32bda388135321920596503/TauCetiRoadmap/ScatteringDiagrams/Formalized/SweepGeometry.lean).
This module supplies a reusable library API, including the prism equivalence and
convexity. It does not construct oriented cochains or rational-normal presentations.
-/

public section

namespace Mei.Convex

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The negative ray sweep of a set. -/
@[expose] def sweep (P : Set V) (n : V) : Set V :=
  {y | ∃ x ∈ P, ∃ t : ℝ, 0 ≤ t ∧ y = x - t • n}

/-- The base is the zero-height part of its sweep. -/
theorem subset_sweep (P : Set V) (n : V) : P ⊆ sweep P n := by
  intro x hx
  exact ⟨x, hx, 0, le_rfl, by simp⟩

/-- Sweeping preserves inclusions. -/
theorem sweep_mono {P Q : Set V} (h : P ⊆ Q) (n : V) : sweep P n ⊆ sweep Q n := by
  rintro y ⟨x, hx, t, ht, he⟩
  exact ⟨x, h hx, t, ht, he⟩

/-- The empty base has empty sweep. -/
@[simp]
theorem sweep_empty (n : V) : sweep (∅ : Set V) n = ∅ := by
  ext y
  simp [sweep]

/-- Every sweep is stable under further translation in its negative direction. -/
theorem sub_smul_mem_sweep {P : Set V} {n y : V} (hy : y ∈ sweep P n)
    {s : ℝ} (hs : 0 ≤ s) : y - s • n ∈ sweep P n := by
  obtain ⟨x, hx, t, ht, rfl⟩ := hy
  refine ⟨x, hx, t + s, add_nonneg ht hs, ?_⟩
  module

/-- A transverse direction admits a linear height constant on the base. -/
theorem exists_sweep_height {P : Set V} {n : V} (hP : P.Nonempty)
    (hn : n ∉ vectorSpan ℝ P) :
    ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), f n = 1 ∧ ∀ x ∈ P, f x = c := by
  obtain ⟨f, hfn, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨p, hp⟩ := hP
  refine ⟨(f n)⁻¹ • f, (f n)⁻¹ * f p, ?_, ?_⟩
  · simp [hfn]
  · intro x hx
    have h : f (x - p) = 0 := by
      have hmem : f (x - p) ∈ (vectorSpan ℝ P).map f :=
        Submodule.mem_map_of_mem (vsub_mem_vectorSpan ℝ hx hp)
      rwa [hf, Submodule.mem_bot] at hmem
    have heq : f x = f p := sub_eq_zero.mp (by simpa only [map_sub] using h)
    simp [heq]

/-- Membership via the uniquely determined base point and nonnegative height. -/
theorem mem_sweep_iff {P : Set V} {n y : V} (f : V →ₗ[ℝ] ℝ) (c : ℝ)
    (hfn : f n = 1) (hfP : ∀ x ∈ P, f x = c) :
    y ∈ sweep P n ↔ f y ≤ c ∧ y + (c - f y) • n ∈ P := by
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    have he : f (x - t • n) = c - t := by simp [hfP x hx, hfn]
    rw [he]
    refine ⟨sub_le_self _ ht, ?_⟩
    convert hx using 1
    module
  · rintro ⟨hy, hx⟩
    refine ⟨y + (c - f y) • n, hx, c - f y, sub_nonneg.mpr hy, ?_⟩
    module

/-- Transverse sweeps have unique base and ray coordinates. -/
theorem sweep_coordinates_unique {P : Set V} {n : V} (hn : n ∉ vectorSpan ℝ P)
    {x x' : V} (hx : x ∈ P) (hx' : x' ∈ P) {t t' : ℝ}
    (h : x - t • n = x' - t' • n) : x = x' ∧ t = t' := by
  obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height ⟨x, hx⟩ hn
  have hheight := congrArg f h
  simp only [map_sub, map_smul, hfP x hx, hfP x' hx', hfn, smul_eq_mul,
    mul_one, sub_right_inj] at hheight
  subst t'
  exact ⟨sub_left_inj.mp h, rfl⟩

/-- The prism parameterization of a transverse sweep is a bijection. -/
@[expose] noncomputable def sweepEquiv (P : Set V) (n : V)
    (hn : n ∉ vectorSpan ℝ P) :
    (P × {t : ℝ // 0 ≤ t}) ≃ sweep P n :=
  Equiv.ofBijective
    (fun z => ⟨z.1.1 - z.2.1 • n, z.1.1, z.1.2, z.2.1, z.2.2, rfl⟩)
    ⟨by
      intro z w h
      have he := sweep_coordinates_unique hn z.1.2 w.1.2 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2), by
      rintro ⟨y, x, hx, t, ht, rfl⟩
      exact ⟨(⟨x, hx⟩, ⟨t, ht⟩), rfl⟩⟩

/-- The prism equivalence evaluates by subtracting the ray parameter. -/
@[simp]
theorem sweepEquiv_apply (P : Set V) (n : V) (hn : n ∉ vectorSpan ℝ P)
    (z : P × {t : ℝ // 0 ≤ t}) :
    (sweepEquiv P n hn z : V) = z.1.1 - z.2.1 • n := rfl

/-- Every positive translate of a base point leaves the entire sweep. -/
theorem positive_translate_notMem_sweep {P : Set V} {n x : V}
    (hn : n ∉ vectorSpan ℝ P) (hx : x ∈ P) {t : ℝ} (ht : 0 < t) :
    x + t • n ∉ sweep P n := by
  obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height ⟨x, hx⟩ hn
  intro h
  have hle := ((mem_sweep_iff f c hfn hfP).mp h).1
  have : c + t ≤ c := by simpa [hfP x hx, hfn] using hle
  exact (not_le_of_gt (lt_add_of_pos_right c ht)) this

/-- The positive sweeping vector is not a recession direction. -/
theorem sweep_strictlyOutgoing {P : Set V} {n : V} (hP : P.Nonempty)
    (hn : n ∉ vectorSpan ℝ P) :
    ¬ ∀ x ∈ sweep P n, ∀ t : ℝ, 0 ≤ t → x + t • n ∈ sweep P n := by
  intro h
  obtain ⟨x, hx⟩ := hP
  exact positive_translate_notMem_sweep hn hx zero_lt_one
    (h x (subset_sweep P n hx) 1 zero_le_one)

/-- A sweep of a nonempty set is nonempty. -/
theorem sweep_nonempty {P : Set V} (hP : P.Nonempty) (n : V) :
    (sweep P n).Nonempty := hP.mono (subset_sweep P n)

/-- Subdivision covers remain covers under sweeping. -/
theorem sweep_iUnion {ι : Sort*} (P : ι → Set V) (n : V) :
    sweep (⋃ i, P i) n = ⋃ i, sweep (P i) n := by
  ext y
  simp only [sweep, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, hx⟩, t, ht, he⟩
    exact ⟨i, x, hx, t, ht, he⟩
  · rintro ⟨i, x, hx, t, ht, he⟩
    exact ⟨x, ⟨i, hx⟩, t, ht, he⟩

/-- On a transverse common base sweeping creates no new intersections. -/
theorem sweep_inter {P Q : Set V} {n : V} (hn : n ∉ vectorSpan ℝ (P ∪ Q)) :
    sweep P n ∩ sweep Q n = sweep (P ∩ Q) n := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, t, ht, he⟩, ⟨x', hx', t', ht', he'⟩⟩
    have hxx := (sweep_coordinates_unique hn (Or.inl hx) (Or.inr hx')
      (he.symm.trans he')).1
    exact ⟨x, ⟨hx, hxx ▸ hx'⟩, t, ht, he⟩
  · rintro ⟨x, ⟨hx, hx'⟩, t, ht, he⟩
    exact ⟨⟨x, hx, t, ht, he⟩, ⟨x, hx', t, ht, he⟩⟩

/-- The direction of a nonempty sweep gains exactly the sweeping line. -/
theorem vectorSpan_sweep {P : Set V} (hP : P.Nonempty) (n : V) :
    vectorSpan ℝ (sweep P n) = vectorSpan ℝ P ⊔ Submodule.span ℝ {n} := by
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    obtain ⟨x, hx, t, ht, rfl⟩ := ha
    obtain ⟨y, hy, s, hs, rfl⟩ := hb
    have hbase : x - y ∈ vectorSpan ℝ P ⊔ Submodule.span ℝ {n} :=
      (le_sup_left : vectorSpan ℝ P ≤ _)
        (vsub_mem_vectorSpan ℝ hx hy)
    have hn : n ∈ vectorSpan ℝ P ⊔ Submodule.span ℝ {n} :=
      (le_sup_right : Submodule.span ℝ {n} ≤ _)
        (Submodule.subset_span (Set.mem_singleton n))
    have hh := (vectorSpan ℝ P ⊔ Submodule.span ℝ {n}).add_mem hbase
      ((vectorSpan ℝ P ⊔ Submodule.span ℝ {n}).smul_mem (s - t) hn)
    change (x - t • n) - (y - s • n) ∈ _
    have he : (x - t • n) - (y - s • n) = x - y + (s - t) • n := by module
    rw [he]
    exact hh
  · apply sup_le (vectorSpan_mono ℝ (subset_sweep P n))
    rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨x, hx⟩ := hP
    have hy : x - n ∈ sweep P n := ⟨x, hx, 1, zero_le_one, by simp⟩
    simpa using vsub_mem_vectorSpan ℝ (subset_sweep P n hx) hy

end Algebra

section Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A closed transverse base has a closed sweep, even when unbounded. -/
theorem isClosed_sweep {P : Set V} {n : V} (hP : IsClosed P)
    (hn : n ∉ vectorSpan ℝ P) : IsClosed (sweep P n) := by
  rcases P.eq_empty_or_nonempty with he | hne
  · subst P
    simp [sweep]
  · obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height hne hn
    have he : sweep P n = {y | f y ≤ c} ∩
        (fun y => y + (c - f y) • n) ⁻¹' P := by
      ext y
      exact mem_sweep_iff f c hfn hfP
    rw [he]
    exact (isClosed_le f.continuous_of_finiteDimensional continuous_const).inter
      (hP.preimage (continuous_id.add
        ((continuous_const.sub f.continuous_of_finiteDimensional).smul continuous_const)))

/-- The affine dimension of a nonempty transverse sweep increases by one. -/
theorem finrank_sweep {P : Set V} {n : V} (hP : P.Nonempty)
    (hn : n ∉ vectorSpan ℝ P) :
    Module.finrank ℝ (vectorSpan ℝ (sweep P n)) =
      Module.finrank ℝ (vectorSpan ℝ P) + 1 := by
  rw [vectorSpan_sweep hP n]
  exact Submodule.finrank_sup_span_singleton hn

end Topology

end Mei.Convex

namespace Convex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Sweeping a convex base preserves convexity. -/
theorem sweep {P : Set V} (hP : Convex ℝ P) (n : V) :
    Convex ℝ (Mei.Convex.sweep P n) := by
  rintro _ ⟨x, hx, t, ht, rfl⟩ _ ⟨y, hy, s, hs, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hP hx hy ha hb hab, a * t + b * s,
    add_nonneg (mul_nonneg ha ht) (mul_nonneg hb hs), ?_⟩
  module

end Convex
