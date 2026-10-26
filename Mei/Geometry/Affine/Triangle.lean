/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Generic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
public import Mathlib.Tactic.Module

/-!
# Small triangles transverse to countable linear arrangements

In a real normed plane, choose a small triangle centered at zero whose vertices
avoid a countable arrangement of proper linear subspaces and whose edges are
transverse to every member. The vertices are `u`, `v`, and `-u-v`.
The construction uses `AffineSubspace.exists_dist_lt_genericLocus`: after choosing
`v`, only countably many translates of the forbidden directions and the line
through `u` have to be excluded when choosing `u`.

The same construction in an affine slice treats sets whose supporting spans
contain the center, ignoring sets that miss the prescribed ball. These triangles
provide polygonal boundaries around isolated singular points.
-/

public section

open Set

namespace LinearIndependent

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two independent vectors form a nondegenerate triangle together with the
negative of their sum. -/
theorem affineIndependent_centeredTriangle {u v : V} (huv : LinearIndependent ℝ ![u, v]) :
    AffineIndependent ℝ ![u, v, -u-v] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hs
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hw hs
  have hzero : ∑ j : Fin 2, ![w 0 - w 2, w 1 - w 2] j • ![u, v] j = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    convert hs using 1
    module
  have hc := Fintype.linearIndependent_iff.mp huv _ hzero
  have h0 := hc 0
  have h1 := hc 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  intro j
  fin_cases j <;> dsimp at * <;> linarith

end LinearIndependent

namespace Affine.Triangle

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The centroid of a triangle lies on none of the affine lines through pairs
of its vertices, including outside the edges. -/
theorem centroid_ne_lineMap (s : Affine.Triangle ℝ V) (j k : Fin 3) (t : ℝ) :
    s.centroid ≠ AffineMap.lineMap (s.points j) (s.points k) t := by
  have hp : ({j, k} : Set (Fin 3)) ≠ Set.univ := by
    intro he
    have ha := Set.ext_iff.mp he
    fin_cases j <;> fin_cases k <;> simp_all [Set.ext_iff, Fin.forall_fin_succ]
  have hc := s.centroid_notMem_affineSpan_of_ne_univ hp
  rw [Set.image_pair] at hc
  intro he
  apply hc
  rw [he]
  exact AffineMap.lineMap_mem _ (subset_affineSpan ℝ _ (by simp))
    (subset_affineSpan ℝ _ (by simp))

end Affine.Triangle

namespace Mei

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Countable ι]

/-- There are arbitrarily small centered nondegenerate triangles avoiding a
countable linear arrangement, with every edge transverse to every forbidden
direction. The dimension need only be at least two. -/
theorem exists_small_transverse_triangle (D : ι → Submodule ℝ V)
    (hD : ∀ j, D j ≠ ⊤) (hdim : 2 ≤ Module.finrank ℝ V)
    {r : ℝ} (hr : 0 < r) :
    ∃ u v : V, LinearIndependent ℝ ![u, v] ∧
      ‖u‖ < r ∧ ‖v‖ < r ∧ ‖-u-v‖ < r ∧
      ∀ j, u ∉ D j ∧ v ∉ D j ∧ -u-v ∉ D j ∧
        v-u ∉ D j ∧ (-u-v)-v ∉ D j ∧ u-(-u-v) ∉ D j := by
  classical
  -- First choose a small nonzero vector outside all forbidden directions.
  let A : Option ι → AffineSubspace ℝ V :=
    fun j => (j.elim (⊥ : Submodule ℝ V) D).toAffineSubspace
  have hA : ∀ j, A j ≠ ⊤ := by
    intro j
    cases j with
    | none =>
      intro he
      have he' : (⊥ : Submodule ℝ V) = ⊤ := by
        simpa only [A, Option.elim_none, Submodule.toAffineSubspace_direction,
          AffineSubspace.direction_top] using congrArg AffineSubspace.direction he
      have : Module.finrank ℝ V = 0 := by
        simpa only [finrank_bot, finrank_top] using
          congrArg (fun S : Submodule ℝ V => Module.finrank ℝ S) he'.symm
      omega
    | some j =>
      intro he
      apply hD j
      simpa only [A, Option.elim_some, Submodule.toAffineSubspace_direction,
        AffineSubspace.direction_top] using congrArg AffineSubspace.direction he
  obtain ⟨v, hvnorm, hv⟩ := AffineSubspace.exists_dist_lt_genericLocus A hA
    0 (by linarith : 0 < r / 3)
  have hv0 : v ≠ 0 := by simpa [A] using hv none
  -- These five translates exclude the remaining vertex and edge coincidences.
  let c : Fin 5 → ℝ := ![0, -1, 1, -(1/2), -2]
  let B : Option (ι × Fin 5) → AffineSubspace ℝ V := fun j =>
    j.elim (Submodule.span ℝ {v}).toAffineSubspace
      (fun a => AffineSubspace.mk' (c a.2 • v) (D a.1))
  have hB : ∀ j, B j ≠ ⊤ := by
    intro j
    cases j with
    | none =>
      intro he
      have he' : Submodule.span ℝ {v} = ⊤ := by
        simpa only [B, Option.elim_none, Submodule.toAffineSubspace_direction,
          AffineSubspace.direction_top] using congrArg AffineSubspace.direction he
      have := congrArg (fun S : Submodule ℝ V => Module.finrank ℝ S) he'
      rw [finrank_span_singleton hv0, finrank_top] at this
      omega
    | some a =>
      intro he
      have he' := congrArg AffineSubspace.direction he
      simp only [B, Option.elim_some, AffineSubspace.direction_mk',
        AffineSubspace.direction_top] at he'
      exact hD a.1 he'
  obtain ⟨u, hunorm, hu⟩ := AffineSubspace.exists_dist_lt_genericLocus B hB
    0 (by linarith : 0 < r / 3)
  have hlin : LinearIndependent ℝ ![u, v] := by
    apply linearIndependent_fin2.mpr
    refine ⟨hv0, fun a ha => hu none ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
    simp only [B, Option.elim_none, Submodule.mem_toAffineSubspace]
    rw [← ha]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton v))
  have havoid (j : ι) (k : Fin 5) : u - c k • v ∉ D j := by
    simpa only [B, Option.elim_some, AffineSubspace.mem_mk', vsub_eq_sub] using
      hu (some (j, k))
  -- The two small choices also keep their negative sum inside the prescribed ball.
  simp only [dist_zero_right] at hvnorm hunorm
  refine ⟨u, v, hlin, by linarith, by linarith, ?_, fun j => ?_⟩
  · calc
      ‖-u-v‖ ≤ ‖-u‖ + ‖v‖ := norm_sub_le _ _
      _ < r := by rw [norm_neg]; linarith
  · have huD : u ∉ D j := by simpa [c] using havoid j 0
    have hvD : v ∉ D j := by simpa [A] using hv (some j)
    refine ⟨huD, hvD, ?_, ?_, ?_, ?_⟩
    · intro he
      apply havoid j 1
      convert (D j).neg_mem he using 1
      simp [c]
      module
    · intro he
      apply havoid j 2
      simpa [c] using (D j).neg_mem he
    · intro he
      apply havoid j 4
      convert (D j).neg_mem he using 1
      simp [c]
      module
    · intro he
      apply havoid j 3
      convert (D j).smul_mem (1/2 : ℝ) he using 1
      simp [c]
      module

section Slice

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Countable ι]
  (W : ι → Set V) (T : Submodule ℝ V) [FiniteDimensional ℝ T]
  {p : V} {r : ℝ}

/-- Inside a finite-dimensional affine slice of dimension at least two, there
is an arbitrarily small centered nondegenerate triangle whose vertices miss
countably many prescribed sets and whose edges are transverse to their affine
spans. Only the sets meeting the ball must have span through its center and
proper direction after restriction to the slice. -/
theorem exists_small_transverse_triangle_in_slice (hdim : 2 ≤ Module.finrank ℝ T) (hr : 0 < r)
    (hwall : ∀ j, (W j ∩ Metric.ball p r).Nonempty →
      p ∈ affineSpan ℝ (W j) ∧ ¬ T ≤ (affineSpan ℝ (W j)).direction) :
    ∃ s : Affine.Triangle ℝ V, s.centroid = p ∧
      (∀ j, s.points j ∈ Metric.ball p r ∩ (AffineSubspace.mk' p T : Set V)) ∧
      (∀ j k, j ≠ k → ∀ a, (W a ∩ Metric.ball p r).Nonempty →
        s.points k - s.points j ∉ (affineSpan ℝ (W a)).direction) ∧
      (∀ j a, s.points j ∉ W a) := by
  classical
  -- Only sets meeting the ball matter; pull their directions back to the slice.
  let J := {a : ι // (W a ∩ Metric.ball p r).Nonempty}
  let D : J → Submodule ℝ T := fun a =>
    (affineSpan ℝ (W a.val)).direction.comap T.subtype
  have hD : ∀ a, D a ≠ ⊤ := by
    intro a he
    apply (hwall a.val a.property).2
    intro v hv
    have hm : (⟨v, hv⟩ : T) ∈ D a := he ▸ Submodule.mem_top
    exact hm
  obtain ⟨u, v, huv, hu, hv, huvnorm, havoid⟩ :=
    Mei.exists_small_transverse_triangle D hD hdim hr
  -- Construct the centered triangle in the slice, then embed and translate it.
  let t : Affine.Triangle ℝ T := ⟨![u, v, -u-v], huv.affineIndependent_centeredTriangle⟩
  let f : T →ᵃ[ℝ] V := (AffineEquiv.constVAdd ℝ V p).toAffineMap.comp T.subtype.toAffineMap
  have hf : Function.Injective f := (add_right_injective p).comp Subtype.coe_injective
  let s := t.map f hf
  have hs (j : Fin 3) : s.points j = p + (t.points j : V) := (rfl)
  have ht0 : t.centroid = 0 := by
    have he := t.centroid_vsub_eq 0
    simpa [t, Fin.sum_univ_three, add_assoc] using he
  have hsp : s.centroid = p := by
    rw [Affine.Simplex.centroid_map, ht0]
    simp [f]
  have hnorm (j : Fin 3) : ‖t.points j‖ < r := by
    fin_cases j
    · exact hu
    · exact hv
    · exact huvnorm
  have hmem (j : Fin 3) :
      s.points j ∈ Metric.ball p r ∩ (AffineSubspace.mk' p T : Set V) := by
    rw [hs]
    constructor
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Submodule.norm_coe] using
        hnorm j
    · apply AffineSubspace.mem_mk'.mpr
      simpa only [vsub_eq_sub, add_sub_cancel_left] using (t.points j).property
  have hvertex (j : Fin 3) (a : J) : t.points j ∉ D a := by
    have hh := havoid a
    fin_cases j
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2.1
  -- The three cyclic edge conditions also give all reversed edges.
  have hedge (j k : Fin 3) (hjk : j ≠ k) (a : J) : t.points k - t.points j ∉ D a := by
    have hh := havoid a
    have h01 : t.points 1 - t.points 0 ∉ D a := hh.2.2.2.1
    have h12 : t.points 2 - t.points 1 ∉ D a := hh.2.2.2.2.1
    have h20 : t.points 0 - t.points 2 ∉ D a := hh.2.2.2.2.2
    have h10 : t.points 0 - t.points 1 ∉ D a := by
      simpa only [neg_sub] using (not_congr (D a).neg_mem_iff).mpr h01
    have h21 : t.points 1 - t.points 2 ∉ D a := by
      simpa only [neg_sub] using (not_congr (D a).neg_mem_iff).mpr h12
    have h02 : t.points 2 - t.points 0 ∉ D a := by
      simpa only [neg_sub] using (not_congr (D a).neg_mem_iff).mpr h20
    fin_cases j <;> fin_cases k
    all_goals
      first
      | exact (hjk rfl).elim
      | exact h01
      | exact h12
      | exact h20
      | exact h10
      | exact h21
      | exact h02
  refine ⟨s, hsp, hmem, ?_, ?_⟩
  · intro j k hjk a ha he
    apply hedge j k hjk ⟨a, ha⟩
    -- The subtype inclusion is linear; translate both vertices by the same center.
    simpa only [D, Submodule.mem_comap, Submodule.coe_sub, Submodule.subtype_apply,
      hs, add_sub_add_left_eq_sub] using he
  · intro j a ha
    let a' : J := ⟨a, s.points j, ha, (hmem j).1⟩
    apply hvertex j a'
    have he := (affineSpan ℝ (W a)).vsub_mem_direction
      (subset_affineSpan ℝ _ ha) (hwall a a'.property).1
    simpa only [D, Submodule.mem_comap, Submodule.subtype_apply, hs,
      vsub_eq_sub, add_sub_cancel_left] using he

end Slice

end Mei
