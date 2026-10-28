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
