/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Completion
public import Mei.RingTheory.FilteredAlgebra.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Units in filtered ring completions

An element congruent to one in the first quotient has a compatible inverse.
-/

public section

namespace TauCeti.AlgFiltration

open Opposite

variable {A : Type*} [Ring A] (F : AlgFiltration A)

/-- Every element congruent to one modulo the first completion ideal is a unit. -/
theorem isUnit_of_sub_one_mem {u : F.completion}
    (hu : u - 1 ∈ F.completionIdeal 1) : IsUnit u := by
  have hunit (k : ℕ) : IsUnit (F.projection k u) := by
    simpa only [map_sub, map_one, sub_add_cancel] using
      (F.isNilpotent_projection hu k).isUnit_add_one
  let w : ∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1) := fun k => ↑(hunit k.unop).unit⁻¹
  have hw : w ∈ F.completion := (F.mem_completion_iff w).mpr fun {k l} h => by
    have hmap : Units.map (Ideal.Quotient.factor
        (F.antitone (Nat.add_le_add_right h 1))).toMonoidHom (hunit l).unit =
        (hunit k).unit :=
      Units.ext (F.factor_projection h u)
    simp only [w, ← hmap, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass]
  let v : F.completion := ⟨w, hw⟩
  refine ⟨⟨u, v, ?_, ?_⟩, rfl⟩
  · exact F.completion_ext fun k => by
      rw [map_mul, map_one, F.projection_apply k v]
      exact (hunit k).mul_val_inv
  · exact F.completion_ext fun k => by
      rw [map_mul, map_one, F.projection_apply k v]
      exact (hunit k).val_inv_mul

end TauCeti.AlgFiltration
