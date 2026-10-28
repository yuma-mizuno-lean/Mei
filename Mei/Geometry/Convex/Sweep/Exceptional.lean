/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep
public import Mei.Geometry.Affine.Generic

/-!
# Affine exceptions for swept sets

The affine span of a negative-ray sweep consists of the full lines parallel to
the sweeping vector through the original affine span. Sweeping a set of
codimension at least two therefore gives a proper affine span, including when
the sweeping vector is tangent or zero.

`ExceptionalArrangement.ofSweeps` assembles these spans for finitely many sets
and vectors. A generic endpoint has every corresponding full line disjoint
from the original affine spans, hence also from the swept sets. This detects
endpoints whose backward rays can encounter a singular cell.

The construction uses `Mei.Convex.vectorSpan_sweep`, Mathlib's affine-direction
and submodule-sum APIs, and the existing finite exceptional arrangements.
-/

public section

noncomputable section

namespace Mei.Convex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A swept affine span contains precisely the lines parallel to the sweeping
vector through the original affine span. Empty bases are allowed. -/
@[simp]
theorem mem_affineSpan_sweep_iff (P : Set V) (n y : V) :
    y ∈ affineSpan ℝ (sweep P n) ↔ ∃ t : ℝ, y + t • n ∈ affineSpan ℝ P := by
  obtain hP | ⟨x, hx⟩ := P.eq_empty_or_nonempty
  · simp [hP, AffineSubspace.notMem_bot]
  have hxP := subset_affineSpan ℝ P hx
  have hxS := subset_affineSpan ℝ (sweep P n) (subset_sweep P n hx)
  have hdir := vectorSpan_sweep ⟨x, hx⟩ n
  constructor
  · intro hy
    have hdiff := (affineSpan ℝ (sweep P n)).vsub_mem_direction hy hxS
    rw [direction_affineSpan, hdir] at hdiff
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hdiff
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨-t, ?_⟩
    have hmem := (affineSpan ℝ P).vadd_mem_of_mem_direction
      (by simpa only [direction_affineSpan] using hu) hxP
    simp only [vsub_eq_sub] at huv
    rw [← sub_add_cancel y x, ← huv]
    convert hmem using 1
    simp only [vadd_eq_add]
    module
  · rintro ⟨t, ht⟩
    have htS := affineSpan_mono ℝ (subset_sweep P n) ht
    have hn : n ∈ (affineSpan ℝ (sweep P n)).direction := by
      rw [direction_affineSpan, hdir]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self n)
    have hmem := (affineSpan ℝ (sweep P n)).vadd_mem_of_mem_direction
      ((affineSpan ℝ (sweep P n)).direction.smul_mem (-t) hn) htS
    convert hmem using 1
    simp only [vadd_eq_add]
    module

/-- Sweeping a set of codimension at least two has proper affine span.
Only nonempty bases need a dimension bound. -/
theorem affineSpan_sweep_ne_top [FiniteDimensional ℝ V] (P : Set V) (n : V)
    (hdim : P.Nonempty →
      Module.finrank ℝ (vectorSpan ℝ P) + 1 < Module.finrank ℝ V) :
    affineSpan ℝ (sweep P n) ≠ ⊤ := by
  obtain rfl | hP := P.eq_empty_or_nonempty
  · simp
  have hle : Module.finrank ℝ (vectorSpan ℝ (sweep P n)) ≤
      Module.finrank ℝ (vectorSpan ℝ P) + 1 := by
    by_cases hn : n ∈ vectorSpan ℝ P
    · rw [vectorSpan_sweep hP n,
        sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using hn))]
      omega
    · exact (finrank_sweep hP hn).le
  intro htop
  rw [← direction_affineSpan, htop, AffineSubspace.direction_top,
    finrank_top] at hle
  exact (not_le_of_gt (hdim hP)) hle

end Mei.Convex

namespace Mei.ExceptionalArrangement

open Mei.Convex

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The affine spans of all sweeps of the given cells along the given vectors.
Repeated spans are identified. Empty cells and zero vectors are permitted. -/
def ofSweeps (cells : Finset (Set V)) (vectors : Finset V)
    (hdim : ∀ P ∈ cells, P.Nonempty →
      Module.finrank ℝ (vectorSpan ℝ P) + 1 < Module.finrank ℝ V) :
    ExceptionalArrangement V := by
  classical
  refine ⟨(cells ×ˢ vectors).image (fun z => affineSpan ℝ (sweep z.1 z.2)), ?_⟩
  rintro A hA
  obtain ⟨⟨P, n⟩, hPn, rfl⟩ := Finset.mem_image.mp hA
  exact affineSpan_sweep_ne_top P n (hdim P (Finset.mem_product.mp hPn).1)

open Classical in
/-- The exception set is the image of the cell-vector pairs under swept affine span. -/
@[simp]
theorem exceptions_ofSweeps (cells : Finset (Set V)) (vectors : Finset V)
    (hdim : ∀ P ∈ cells, P.Nonempty →
      Module.finrank ℝ (vectorSpan ℝ P) + 1 < Module.finrank ℝ V) :
    (ofSweeps cells vectors hdim).exceptions =
      (cells ×ˢ vectors).image (fun z => affineSpan ℝ (sweep z.1 z.2)) := (rfl)

/-- Genericity for sweep exceptions is equivalent to avoidance by every full
line in one of the specified directions. -/
@[simp]
theorem isGeneric_ofSweeps_iff (cells : Finset (Set V)) (vectors : Finset V)
    (hdim : ∀ P ∈ cells, P.Nonempty →
      Module.finrank ℝ (vectorSpan ℝ P) + 1 < Module.finrank ℝ V) (y : V) :
    (ofSweeps cells vectors hdim).IsGeneric y ↔
      ∀ P ∈ cells, ∀ n ∈ vectors, ∀ t : ℝ, y + t • n ∉ affineSpan ℝ P := by
  classical
  rw [isGeneric_iff, exceptions_ofSweeps]
  constructor
  · intro hy P hP n hn t ht
    exact hy _ (Finset.mem_image.mpr ⟨(P, n), Finset.mem_product.mpr ⟨hP, hn⟩, rfl⟩)
      ((mem_affineSpan_sweep_iff P n y).mpr ⟨t, ht⟩)
  · intro hy A hA hyA
    obtain ⟨⟨P, n⟩, hPn, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨t, ht⟩ := (mem_affineSpan_sweep_iff P n y).mp hyA
    exact hy P (Finset.mem_product.mp hPn).1 n (Finset.mem_product.mp hPn).2 t ht

end Mei.ExceptionalArrangement
