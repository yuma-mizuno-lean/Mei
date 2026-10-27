/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Analysis.Convex.Intrinsic

/-!
# Small transverse simplices

At a point of a finite-codimensional affine subspace, a complementary simplex
can be chosen inside any prescribed ball. Its filled support meets the affine
subspace exactly at that point. These simplices provide local intersection tests.

The construction uses Mathlib's `exists_mem_interior_convexHull_affineBasis`
in a linear complement and then translates the simplex to the chosen point.
-/

public section

open Set Module

namespace AffineSubspace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {k : ℕ}

/-- An arbitrarily small simplex complementary to an affine subspace at a
specified point. Its filled support meets the subspace in precisely that point. -/
theorem exists_small_transverse_simplex (A : AffineSubspace ℝ V)
    (hdim : finrank ℝ (V ⧸ A.direction) = k) {p : V} (hp : p ∈ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Affine.Simplex ℝ V k,
      IsCompl A.direction (vectorSpan ℝ (range s.points)) ∧
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε ∧
      convexHull ℝ (range s.points) ∩ A = {p} ∧
      p ∈ intrinsicInterior ℝ (convexHull ℝ (range s.points)) := by
  -- Work in a linear complement, where the desired test has full dimension.
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl A.direction
  have hdimT : finrank ℝ T = k := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hT
    have hquot := A.direction.finrank_quotient_add_finrank
    omega
  obtain ⟨b, hb0, hbball⟩ := exists_mem_interior_convexHull_affineBasis
    (Metric.ball_mem_nhds (0 : T) hε)
  let e := finCongr (congrArg (· + 1) hdimT)
  let t : Affine.Simplex ℝ T k := ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding⟩
  have hrange : range t.points = range b := e.symm.surjective.range_comp b
  let f : T →ᵃ[ℝ] V := (AffineEquiv.constVAdd ℝ V p).toAffineMap.comp T.subtype.toAffineMap
  have hf : Function.Injective f := (add_right_injective p).comp Subtype.coe_injective
  let s := t.map f hf
  have hs (j : Fin (k + 1)) : s.points j = p + (t.points j : V) := (rfl)
  have hhull : convexHull ℝ (range s.points) = f '' convexHull ℝ (range t.points) := by
    rw [f.image_convexHull, ← range_comp]
    rfl
  let g : T →ᵃⁱ[ℝ] V := { f with norm_map := fun _ => rfl }
  have hpInterior : p ∈ intrinsicInterior ℝ (convexHull ℝ (range s.points)) := by
    -- Identify the affine map with its isometric enrichment for intrinsic interiors.
    have hg : (g : T → V) = f := (rfl)
    rw [hhull, ← hg, g.intrinsicInterior_image]
    exact ⟨0, interior_subset_intrinsicInterior (hrange ▸ hb0), by rw [hg]; simp [f]⟩
  -- The mapped simplex spans the complement and meets the original subspace only at its center.
  have hspan : vectorSpan ℝ (range s.points) = T := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [← direction_affineSpan, ← AffineSubspace.direction_mk' p T]
      apply AffineSubspace.direction_le
      apply affineSpan_le.mpr
      rintro _ ⟨j, rfl⟩
      apply AffineSubspace.mem_mk'.mpr
      simpa only [hs, vsub_eq_sub, add_sub_cancel_left] using (t.points j).property
    · rw [s.independent.finrank_vectorSpan (Fintype.card_fin (k + 1)), hdimT]
  refine ⟨s, hspan ▸ hT, ?_, ?_, hpInterior⟩
  · rintro y hy
    obtain ⟨z, hz, rfl⟩ := hhull ▸ hy
    have hzball := hbball (hrange ▸ hz)
    simpa only [f, AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
      AffineEquiv.constVAdd_apply, LinearMap.coe_toAffineMap, Submodule.subtype_apply,
      vadd_eq_add, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      Submodule.norm_coe, sub_zero] using hzball
  · apply Set.Subset.antisymm
    · rintro y ⟨hy, hyA⟩
      apply Set.mem_singleton_iff.mpr
      apply sub_eq_zero.mp
      have hyT : y - p ∈ T := by
        obtain ⟨z, _, rfl⟩ := hhull ▸ hy
        simpa only [f, AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
          AffineEquiv.constVAdd_apply, LinearMap.coe_toAffineMap, Submodule.subtype_apply,
          vadd_eq_add, add_sub_cancel_left] using z.property
      exact (Submodule.disjoint_def.mp hT.disjoint) _
        (by simpa only [vsub_eq_sub] using A.vsub_mem_direction hyA hp) hyT
    · rintro y (rfl : y = p)
      exact ⟨intrinsicInterior_subset hpInterior, hp⟩

end AffineSubspace
