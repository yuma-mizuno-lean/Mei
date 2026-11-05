/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3.1 Pro
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Reparametrization of affine lines

`AffineMap.lineMap` has an elementary form using the terminal displacement from
an endpoint. When a positive scalar multiple of a nonzero displacement is used,
interior ray parameters have an explicit unit-interval parameter. These lemmas
keep the conversion in one place for crossing-time constructions.
-/

public section

namespace Mei.Convex

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A point on an affine line is expressed by its terminal displacement from the
final endpoint. -/
theorem lineMap_eq_add_smul {x y w : V} {T t : ℝ} (hxy : x - y = T • w) :
    AffineMap.lineMap x y t = y + (T * (1 - t)) • w := by
  calc
    AffineMap.lineMap x y t = y + (1 - t) • (x - y) := by
      rw [AffineMap.lineMap_apply_module']
      module
    _ = _ := by rw [hxy]; module

/-- A positive ray point before `T` gives a unit-interval affine parameter, the
corresponding positive multiple, and its value on the segment. -/
theorem lineMap_eq_add_smul_of_pos_of_lt {x y w : V} {T u : ℝ}
    (hT : 0 < T) (hxy : x - y = T • w) (hu : 0 < u) (huT : u < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      u = T * (1 - t) ∧ y + u • w = AffineMap.lineMap x y t := by
  let t := 1 - u / T
  have ht0 : 0 < t := sub_pos.mpr ((div_lt_one hT).mpr huT)
  have ht1 : t < 1 := by
    have hup : 0 < u / T := div_pos hu hT
    dsimp only [t]
    linarith
  have htu : u = T * (1 - t) := by dsimp only [t]; field_simp; ring
  refine ⟨t, ⟨ht0, ht1⟩, htu, ?_⟩
  calc
    y + u • w = y + (T * (1 - t)) • w := by rw [htu]
    _ = _ := (lineMap_eq_add_smul (t := t) hxy).symm

end Mei.Convex
