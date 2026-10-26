/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.CrossingEvents

/-!
# Additive sums of signed wall crossings

Assign an element of an abelian group to each indexed wall. Summing its signed
contributions along a polygonal path retains coincident walls and repeated visits.
For full affine hyperplanes this sum is an endpoint difference, so every closed
path has sum zero. Only walls with nonzero coefficients need be full hyperplanes.

This is the linear cancellation in the logarithm of a joint product: initial
full hyperplanes contribute zero around a loop, and a homogeneous projection
killing the other wall logarithms removes their contributions. Nonlinear Lie
brackets are not discarded by this statement.

The sums use `WallComplement.signedCrossingEvent` and its ordered event lists.
The cancellation is the elementary telescoping of the indicator of a half-space.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Quiver.Path

variable {V ι E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [AddCommGroup E] {W : ι → Set V}
  {x y z : WallComplement W}

/-- Sum the signed coefficients of all indexed crossings, retaining simultaneous
walls and repeated visits. Positive normal velocity contributes the negative coefficient. -/
def wallCrossingSum (p : AdmissiblePLPath x y) (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E) : E :=
  ((p.signedCrossingEvents ν).map (fun S => ∑ a ∈ S, a.2 • c a.1)).sum

/-- The signed event list computes the additive crossing sum. -/
theorem wallCrossingSum_def (p : AdmissiblePLPath x y) (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E) :
    p.wallCrossingSum ν c =
      ((p.signedCrossingEvents ν).map (fun S => ∑ a ∈ S, a.2 • c a.1)).sum := (rfl)

@[simp]
theorem wallCrossingSum_nil (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E) :
    (Quiver.Path.nil : AdmissiblePLPath x x).wallCrossingSum ν c = 0 := by
  simp [wallCrossingSum]

/-- Concatenation adds the crossing sums. -/
@[simp]
theorem wallCrossingSum_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E) :
    (p.comp q).wallCrossingSum ν c = p.wallCrossingSum ν c + q.wallCrossingSum ν c := by
  simp [wallCrossingSum]

/-- Reversal negates the crossing sum. -/
@[simp]
theorem wallCrossingSum_reverse (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, LinearMap.ker (ν j) = (affineSpan ℝ (W j)).direction) :
    p.reverse.wallCrossingSum ν c = -p.wallCrossingSum ν c := by
  classical
  simp [wallCrossingSum, signedCrossingEvents_reverse, hν, Finset.sum_map,
    List.map_map, Function.comp_def, Finset.sum_neg_distrib, List.sum_neg]

end Quiver.Path

namespace AddMonoidHom

variable {V ι E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [AddCommGroup E] [AddCommGroup F] {W : ι → Set V} {x y : WallComplement W}

/-- Additive coefficient maps commute with crossing sums. -/
@[simp]
theorem map_wallCrossingSum (f : E →+ F) (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E) :
    f (p.wallCrossingSum ν c) = p.wallCrossingSum ν (fun j => f (c j)) := by
  simp [Quiver.Path.wallCrossingSum_def, map_list_sum, map_sum, map_zsmul,
    List.map_map, Function.comp_def]

end AddMonoidHom

namespace Mei.Convex.WallComplement

variable {V ι E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [AddCommGroup E] {W : ι → Set V} {x y : WallComplement W}

open Classical in
/-- On a segment each wall contributes once if crossed, and zero otherwise. -/
theorem wallCrossingSum_toPath (e : x ⟶ y) (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E) :
    let _ := Fintype.ofFinite ι
    e.toPath.wallCrossingSum ν c =
      ∑ j, (if ∃ t, (j, t) ∈ crossings x y then
        (if 0 < ν j (y.val - x.val) then -1 else 1 : ℤ) else 0) • c j := by
  classical
  let := Fintype.ofFinite ι
  have hevent (t : ℝ) :
      (∑ a ∈ signedCrossingEvent ν x y t, a.2 • c a.1) =
        ∑ j, if j ∈ crossingWalls x y t then
          (if 0 < ν j (y.val - x.val) then -1 else 1 : ℤ) • c j else 0 := by
    rw [signedCrossingEvent_def, Finset.sum_image]
    · rw [← Finset.sum_filter, Finset.filter_univ_mem]
    · intro a _ b _ hab
      exact (Prod.mk.inj hab).1
  have hn := (pairwise_orderedCrossingTimes e).nodup
  simp only [Quiver.Path.wallCrossingSum_def, Quiver.Hom.toPath,
    Quiver.Path.signedCrossingEvents_cons,
    Quiver.Path.signedCrossingEvents_nil, List.nil_append, segmentCrossingEvents_def,
    List.map_map, Function.comp_def, hevent]
  rw [← List.sum_toFinset _ hn, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ∃ t, (j, t) ∈ crossings x y
  · obtain ⟨t, ht⟩ := hj
    have htmem : t ∈ (orderedCrossingTimes e).toFinset := by
      simpa using (mem_orderedCrossingTimes e t).mpr ⟨j, ht⟩
    have hjt : ∃ t, (j, t) ∈ crossings x y := ⟨t, ht⟩
    simp only [hjt, ↓reduceIte]
    rw [Finset.sum_eq_single t]
    · simp only [mem_crossingWalls, ht, ↓reduceIte]
    · intro s _ hst
      have hs : (j, s) ∉ crossings x y := fun hs => hst
        (e.down.subsingleton_crossing j ((mem_crossings x y j s).mp hs)
          ((mem_crossings x y j t).mp ht))
      simp only [mem_crossingWalls, hs, ↓reduceIte]
    · exact fun hn => (hn htmem).elim
  · simp only [hj, ↓reduceIte, zero_zsmul]
    apply Finset.sum_eq_zero
    intro t _
    have hjt : (j, t) ∉ crossings x y := fun ht => hj ⟨t, ht⟩
    simp only [mem_crossingWalls, hjt, ↓reduceIte]

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V ι κ E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι] [Finite κ]
  [AddCommGroup E] {W : ι → Set V}

/-- An injective restriction retaining every nonzero coefficient preserves crossing sums. -/
@[simp]
theorem wallCrossingSum_restrict (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E) (f : κ → ι)
    (hf : Function.Injective f) (hc : ∀ j, j ∉ range f → c j = 0)
    {x y : WallComplement W} (p : AdmissiblePLPath x y) :
    ((restrictPrefunctor W f).mapPath p).wallCrossingSum (ν ∘ f) (c ∘ f) =
      p.wallCrossingSum ν c := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, ← comp_toPath_eq_cons, ← comp_toPath_eq_cons,
      wallCrossingSum_comp, wallCrossingSum_comp, ih, wallCrossingSum_toPath,
      wallCrossingSum_toPath]
    congr 1
    exact Fintype.sum_of_injective f hf _ _ (fun j hj => by simp [hc j hj])
      fun _ => by simp only [mem_crossings, restrictPrefunctor_obj_val, Function.comp_apply]

end Quiver.Path

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y : WallComplement W}

open Classical in
/-- For a full hyperplane the signed crossing exponent is the drop of the
positive-half-space indicator. -/
theorem crossingExponent_eq_side_sub (x y : WallComplement W)
    (ν : V →ₗ[ℝ] ℝ) (b : ℝ) (j : ι)
    (hW : W j = {v | ν v = b}) :
    (if ∃ t, (j, t) ∈ crossings x y then
      (if 0 < ν (y.val - x.val) then -1 else 1 : ℤ) else 0) =
      (if b < ν x.val then 1 else 0 : ℤ) - (if b < ν y.val then 1 else 0) := by
  have hx : ν x.val ≠ b := fun he => x.notMem j (by simpa only [hW, mem_ofPred_eq] using he)
  have hy : ν y.val ≠ b := fun he => y.notMem j (by simpa only [hW, mem_ofPred_eq] using he)
  have himage : ν '' segment ℝ x.val y.val = uIcc (ν x.val) (ν y.val) := by
    rw [← segment_eq_uIcc]
    exact image_segment ℝ ν.toAffineMap x.val y.val
  have hc : (∃ t, (j, t) ∈ crossings x y) ↔ b ∈ uIcc (ν x.val) (ν y.val) := by
    rw [← himage, segment_eq_image_lineMap, image_image]
    simp only [mem_crossings, hW, mem_ofPred_eq, mem_image]
  rw [hc, map_sub]
  simp only [mem_uIcc]
  split_ifs <;> norm_num at * <;> grind

end Mei.Convex.WallComplement

namespace Quiver.Path

variable {V ι E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [AddCommGroup E] {W : ι → Set V} {x y : WallComplement W}

open Classical in
/-- The crossing sum is an endpoint difference when all walls with nonzero
coefficients are full affine hyperplanes. Zero-coefficient walls may have any supports. -/
theorem wallCrossingSum_eq_sum_side_sub (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : ι → E)
    (hW : ∀ j, c j ≠ 0 → W j = {v | ν j v = b j}) :
    let _ := Fintype.ofFinite ι
    p.wallCrossingSum ν c = ∑ j,
      ((if b j < ν j x.val then 1 else 0 : ℤ) -
        (if b j < ν j y.val then 1 else 0)) • c j := by
  classical
  let := Fintype.ofFinite ι
  have he {u v : WallComplement W} (e : u ⟶ v) :
      e.toPath.wallCrossingSum ν c = ∑ j,
        ((if b j < ν j u.val then 1 else 0 : ℤ) -
          (if b j < ν j v.val then 1 else 0)) • c j := by
    rw [wallCrossingSum_toPath]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : c j = 0
    · simp [hj]
    · rw [crossingExponent_eq_side_sub u v (ν j) (b j) j (hW j hj)]
  induction p with
  | nil => simp
  | @cons y z p e ih =>
    rw [← comp_toPath_eq_cons, wallCrossingSum_comp, ih, he, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← add_zsmul]
    congr 1
    omega

/-- Linear contributions of full affine hyperplanes cancel around every
closed admissible polygonal path, even among arbitrary zero-coefficient walls. -/
theorem wallCrossingSum_loop_eq_zero (p : AdmissiblePLPath x x)
    (ν : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : ι → E)
    (hW : ∀ j, c j ≠ 0 → W j = {v | ν j v = b j}) :
    p.wallCrossingSum ν c = 0 := by
  rw [wallCrossingSum_eq_sum_side_sub p ν b c hW]
  simp

end Quiver.Path
