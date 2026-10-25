/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Algebra.Affine

/-!
# Affine transport of exposed subsets

An affine equivalence with continuous inverse carries exposed subsets to
exposed subsets. Composing an exposing linear functional with the inverse
linear part preserves all comparisons: the inverse translation contributes
the same additive constant at every point.
-/

public section

namespace IsExposed

variable {R V W : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W] {P F : Set V}

/-- An affine equivalence with continuous inverse preserves exposed subsets,
including empty subsets, without any convexity assumption. -/
theorem image_affineEquiv (hF : IsExposed R P F) (e : V ≃ᵃ[R] W)
    (he : Continuous e.symm) : IsExposed R (e '' P) (e '' F) := by
  intro hne
  have hFne : F.Nonempty := by
    obtain ⟨y, x, hx, _⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hF hFne
  let T : W →L[R] V := ⟨e.symm.toAffineMap.linear, AffineMap.continuous_linear_iff.mpr he⟩
  let k := l.comp T
  have hval (y : W) : l (e.symm y) = k y + l (e.symm 0) := by
    have hd := congrFun e.symm.toAffineMap.decomp y
    have heq : e.symm y = e.symm.toAffineMap.linear y + e.symm 0 := by
      simpa only [AffineEquiv.coe_toAffineMap, Pi.add_apply] using hd
    rw [heq, map_add]
    rfl
  have hcompare (x y : W) : k x ≤ k y ↔ l (e.symm x) ≤ l (e.symm y) := by
    rw [hval x, hval y, add_le_add_iff_right]
  refine ⟨k, Set.ext fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' := hl ▸ hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    apply (hcompare (e w) (e x)).mpr
    simpa only [e.symm_apply_apply] using hx'.2 w hw
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, fun w hw => ?_⟩
    have hm := (hcompare (e w) (e x)).mp (hmax (e w) ⟨w, hw, rfl⟩)
    simpa only [e.symm_apply_apply] using hm

/-- An affine equivalence continuous in both directions preserves and reflects
exposure of subsets. -/
theorem image_affineEquiv_iff {e : V ≃ᵃ[R] W}
    (he : Continuous e) (hes : Continuous e.symm) :
    IsExposed R (e '' P) (e '' F) ↔ IsExposed R P F := by
  constructor
  · intro hF
    have hback := hF.image_affineEquiv e.symm he
    have hP : e.symm '' (e '' P) = P := e.toEquiv.symm_image_image P
    have hFset : e.symm '' (e '' F) = F := e.toEquiv.symm_image_image F
    rwa [hP, hFset] at hback
  · intro hF
    exact hF.image_affineEquiv e hes

end IsExposed
