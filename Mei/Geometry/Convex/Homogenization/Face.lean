/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Homogenization.Inequalities
public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import Mathlib.Analysis.Convex.Exposed

/-!
# Exposed faces and homogenization

Intersecting a closed convex set with a nonempty affine zero slice commutes
with closed homogenization. Consequently, nonempty exposed faces homogenize
to faces of the closed homogenized cone, including its height-zero directions.
-/

public section

open Set ContinuousAffineMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

namespace Convex

/-- Intersecting a closed convex base with a nonempty affine zero slice commutes
with actual homogenization, including at height zero. -/
theorem homogenization_inter_zero_eq_inf_ker {P : Set V}
    (hconv : Convex ℝ P)
    (hclosed : IsClosed P) (g : V →ᴬ[ℝ] ℝ)
    (hne : {x ∈ P | g x = 0}.Nonempty) :
    homogenization {x ∈ P | g x = 0} = homogenization P ⊓
      PointedCone.ofSubmodule (LinearMap.ker (homogenizedInequality g).toLinearMap) := by
  let D := homogenization P ⊓
    PointedCone.ofSubmodule (LinearMap.ker (homogenizedInequality g).toLinearMap)
  have hDclosed : IsClosed (D : Set (V × ℝ)) :=
    (isClosed_homogenization P).inter
      (isClosed_eq (homogenizedInequality g).continuous continuous_const)
  have hslice : {x : V | (x, (1 : ℝ)) ∈ D} = {x ∈ P | g x = 0} := by
    ext x
    simp only [D, Set.mem_ofPred_eq, Submodule.mem_inf, PointedCone.mem_ofSubmodule_iff,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      hconv.mem_homogenization_one_iff hclosed, homogenizedInequality_one]
  have hDne : {x : V | (x, (1 : ℝ)) ∈ D}.Nonempty := by rwa [hslice]
  have hrec := D.homogenization_slice_one hDclosed
    (fun z hz => homogenization_height_nonneg hz.1) hDne
  rwa [hslice] at hrec

/-- A nonpositive affine support cuts out a genuine cone face after actual homogenization. -/
theorem homogenization_zeroFace_isFaceOf {P : Set V}
    (hconv : Convex ℝ P)
    (hclosed : IsClosed P) (g : V →ᴬ[ℝ] ℝ) (hg : ∀ x ∈ P, g x ≤ 0)
    (hne : {x ∈ P | g x = 0}.Nonempty) :
    (homogenization {x ∈ P | g x = 0}).IsFaceOf (homogenization P) := by
  rw [hconv.homogenization_inter_zero_eq_inf_ker hclosed g hne]
  have hf : ∀ z ∈ homogenization P, 0 ≤ (-(homogenizedInequality g).toLinearMap) z :=
    fun z hz => neg_nonneg.mpr (homogenizedInequality_nonpos g hg hz)
  have hface := PointedCone.isFaceOf_inf_ker hf
  have hker : LinearMap.ker (-(homogenizedInequality g).toLinearMap) =
      LinearMap.ker (homogenizedInequality g).toLinearMap := by ext z; simp
  rwa [hker] at hface

end Convex

namespace IsExposed

/-- Every nonempty exposed face of a closed convex set homogenizes to a face
of its actual closed homogenization. -/
theorem homogenization_isFaceOf {P F : Set V} (hF : IsExposed ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (Set.homogenization F).IsFaceOf (Set.homogenization P) := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨l, hl⟩ := hF ⟨p, hp⟩
  have hpmax : p ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by rwa [← hl]
  let g := l.toContinuousAffineMap - ContinuousAffineMap.const ℝ V (l p)
  have hg : ∀ x ∈ P, g x ≤ 0 := by
    intro x hx
    simpa [g] using sub_nonpos.mpr (hpmax.2 x hx)
  have hzero : F = {x ∈ P | g x = 0} := by
    ext x
    rw [hl]
    constructor
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, ?_⟩
      simpa [g] using sub_eq_zero.mpr
        (le_antisymm (hpmax.2 x hx) (hmax p hpmax.1))
    · rintro ⟨hx, hzero⟩
      have heq : l x = l p := sub_eq_zero.mp hzero
      exact ⟨hx, fun y hy => (hpmax.2 y hy).trans_eq heq.symm⟩
  rw [hzero]
  exact hconv.homogenization_zeroFace_isFaceOf hclosed g hg (hzero ▸ ⟨p, hp⟩)

end IsExposed

