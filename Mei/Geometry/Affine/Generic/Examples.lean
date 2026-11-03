/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Affine.Arrangement

/-!
# An example of countably many arrangements

Countably many arrangements have a dense common generic locus
(`ExceptionalArrangement.dense_iInter_isGeneric`), but this locus need not be open,
and a common generic point need not have a generic neighbourhood. The points
`1 / (j + 1)` accumulate at the common generic point `0`
(`ExceptionalArrangement.isGeneric_pointArrangement_zero`,
`ExceptionalArrangement.not_isOpen_setOf_forall_isGeneric_pointArrangement`).
-/

public section

open Set Filter Topology

namespace Mei.ExceptionalArrangement

/-- The arrangement of the single point `1 / (j + 1)` of the line. -/
noncomputable def pointArrangement (j : ℕ) : ExceptionalArrangement ℝ :=
  ofAffineForms (fun _ : Unit =>
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap + AffineMap.const ℝ ℝ (-(1 / ((j : ℝ) + 1))))

/-- A point is generic for `pointArrangement j` when it differs from `1 / (j + 1)`. -/
@[simp]
theorem isGeneric_pointArrangement_iff (j : ℕ) (x : ℝ) :
    (pointArrangement j).IsGeneric x ↔ x ≠ 1 / ((j : ℝ) + 1) := by
  have hid : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ≠ 0 := fun h0 => by simpa using LinearMap.congr_fun h0 1
  simp [pointArrangement, isGeneric_ofAffineForms_iff, hid, sub_eq_zero, ← sub_eq_add_neg]

/-- The origin is generic for every arrangement of the family. -/
theorem isGeneric_pointArrangement_zero (j : ℕ) : (pointArrangement j).IsGeneric 0 := by
  simp only [isGeneric_pointArrangement_iff]
  positivity

/-- No neighbourhood of the common generic point `0` is generic for all arrangements
`pointArrangement j`: the exceptional points `1 / (j + 1)` accumulate at `0`. -/
theorem exists_not_isGeneric_pointArrangement_of_mem_nhds {U : Set ℝ} (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ j : ℕ, ∃ x ∈ U, ¬ (pointArrangement j).IsGeneric x := by
  have hlim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨j, hj⟩ := (hlim.eventually hU).exists
  exact ⟨j, _, hj, by simp⟩

/-- The common generic locus of the family `pointArrangement` contains `0` but is not
open, in contrast to the finite case (`isOpen_isGeneric`). -/
theorem not_isOpen_setOf_forall_isGeneric_pointArrangement :
    ¬ IsOpen {x : ℝ | ∀ j, (pointArrangement j).IsGeneric x} := by
  intro hopen
  obtain ⟨j, x, hx, hxj⟩ := exists_not_isGeneric_pointArrangement_of_mem_nhds
    (hopen.mem_nhds (fun j => isGeneric_pointArrangement_zero j))
  exact hxj (hx j)

end Mei.ExceptionalArrangement
