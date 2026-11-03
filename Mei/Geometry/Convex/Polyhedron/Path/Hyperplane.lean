/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product

/-!
# Commutative transport across full hyperplanes

For commutative labels, transport across full affine hyperplanes is determined by
the sides of the endpoints. Each indexed hyperplane contributes its label to the
power `side(source) - side(target)`, where the positive side has value one.
Consequently every closed polygonal path has trivial transport. Identity labels
may have arbitrary supports, and coincident hyperplanes retain separate indices.

Taking the label group to be the multiplicative version of an additive group
gives cancellation of the signed linear contributions of full hyperplanes. This
is the linear cancellation used in the obstruction argument for scattering
completion; it does not assert cancellation of noncommutative wall products.

The construction uses `WallComplement.signedCrossingEvent`, its uniqueness of a
wall crossing on a segment, and Mathlib's finite-product interchange. The
completion argument using this cancellation appears in Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}
  {x y : WallComplement W}

/-- If a wall agrees with an affine hyperplane along the segment, a crossing
occurs exactly when the endpoints lie on opposite sides of that hyperplane. -/
theorem exists_crossing_iff_of_hyperplane (x y : WallComplement W) (f : V →ᵃ[ℝ] ℝ) {j : ι}
    (hW : ∀ z ∈ segment ℝ x.val y.val, z ∈ W j ↔ f z = 0) :
    (∃ t, (j, t) ∈ crossings x y) ↔ ((0 < f x.val) ≠ (0 < f y.val)) := by
  have hx : f x.val ≠ 0 := fun hz =>
    x.notMem j ((hW _ (left_mem_segment ℝ _ _)).mpr hz)
  have hy : f y.val ≠ 0 := fun hz =>
    y.notMem j ((hW _ (right_mem_segment ℝ _ _)).mpr hz)
  have he : (∃ t, (j, t) ∈ crossings x y) ↔
      (0 : ℝ) ∈ segment ℝ (f x.val) (f y.val) := by
    rw [← image_segment ℝ f, segment_eq_image_lineMap]
    simp only [mem_crossings, mem_image]
    constructor
    · rintro ⟨t, ht, he⟩
      exact ⟨_, ⟨t, ht, rfl⟩, (hW _ (lineMap_mem_segment ℝ _ _ ht)).mp he⟩
    · rintro ⟨z, ⟨t, ht, rfl⟩, he⟩
      exact ⟨t, ht, (hW _ (lineMap_mem_segment ℝ _ _ ht)).mpr he⟩
  rw [he, segment_eq_Icc', mem_Icc, min_le_iff, le_max_iff]
  constructor <;> intro hh <;> grind

variable {G : Type*} [Fintype ι] [CommGroup G]
  (f : ι → V →ᵃ[ℝ] ℝ) (label : ι → G)
  (hW : ∀ j, label j ≠ 1 → W j = {z | f j z = 0})

include hW in
/-- Commutative segment transport across full hyperplanes depends only on the
endpoint sides. Identity-labelled supports are unrestricted. -/
theorem segmentPathProduct_eq_prod_of_hyperplanes (e : x ⟶ y) :
    segmentPathProduct (fun j => (f j).linear) label (fun _ _ _ => Commute.all _ _) e =
      ∏ j, label j ^ ((if 0 < f j x.val then 1 else 0 : ℤ) -
        (if 0 < f j y.val then 1 else 0 : ℤ)) := by
  rw [segmentPathProduct_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : label j = 1
  · simp [hj]
  · have hc := exists_crossing_iff_of_hyperplane x y (f j) (j := j)
      (fun z _ => by simp [hW j hj])
    have hd : (f j).linear (y.val - x.val) = f j y.val - f j x.val :=
      (f j).linear_apply_vsub _ _
    rw [hd]
    split_ifs <;> norm_num <;> grind

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Fintype ι] [CommGroup G] {W : ι → Set V}
  (f : ι → V →ᵃ[ℝ] ℝ) (label : ι → G)
  (hW : ∀ j, label j ≠ 1 → W j = {z | f j z = 0})
  {x y : WallComplement W}

include hW in
/-- The commutative transport of a polygonal path through full hyperplanes is
the product of the endpoint-side contributions. Repeated visits cancel. -/
theorem wallPathProduct_eq_prod_of_hyperplanes (p : AdmissiblePLPath x y) :
    p.wallPathProduct (fun j => (f j).linear) label (fun _ _ _ => Commute.all _ _) =
      ∏ j, label j ^ ((if 0 < f j x.val then 1 else 0 : ℤ) -
        (if 0 < f j y.val then 1 else 0 : ℤ)) := by
  induction p with
  | nil => simp
  | @cons y z p e ih =>
    rw [wallPathProduct_cons, segmentPathProduct_eq_prod_of_hyperplanes f label hW e, ih,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [← zpow_add]
    congr 1
    omega

omit [Fintype ι] in
include hW in
/-- Full affine hyperplanes have zero total linear contribution around a loop:
in every commutative label group their signed product is the identity. -/
@[simp]
theorem wallPathProduct_loop_eq_one_of_hyperplanes [Finite ι] (p : AdmissiblePLPath x x) :
    p.wallPathProduct (fun j => (f j).linear) label (fun _ _ _ => Commute.all _ _) = 1 := by
  let := Fintype.ofFinite ι
  rw [wallPathProduct_eq_prod_of_hyperplanes f label hW p]
  simp

end Quiver.Path

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V ι E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Fintype ι] [AddCommGroup E] {W : ι → Set V}
  {x y : WallComplement W}

/-- The signed sum of additive wall contributions is the difference of endpoint
potentials when every nonzero contribution is supported on a full hyperplane.
Zero contributions may have arbitrary supports; lower-degree wall data qualify
when their coefficient in the degree under consideration vanishes. -/
theorem sum_signedCrossingEvents_eq_sub_of_hyperplanes (p : AdmissiblePLPath x y)
    (f : ι → V →ᵃ[ℝ] ℝ) (c : ι → E)
    (hW : ∀ j, c j ≠ 0 → W j = {z | f j z = 0}) :
    ((p.signedCrossingEvents (fun j => (f j).linear)).map
      (fun S => ∑ a ∈ S, a.2 • c a.1)).sum =
        (∑ j, if 0 < f j x.val then c j else 0) -
          ∑ j, if 0 < f j y.val then c j else 0 := by
  have hp := wallPathProduct_eq_prod_of_hyperplanes f
    (fun j => Multiplicative.ofAdd (c j))
    (fun j hj => hW j (fun hc => hj (by simp [hc]))) p
  rw [wallPathProduct_eq_prod_signedCrossingEvents] at hp
  have he := congrArg Multiplicative.toAdd hp
  simp only [toAdd_list_sum, List.map_reverse, List.map_map,
    Function.comp_def, List.sum_reverse, toAdd_zpow, toAdd_prod] at he
  convert he using 1
  · simp
  · simp [sub_smul, Finset.sum_sub_distrib]

omit [Fintype ι] in
/-- The linear contributions of full hyperplanes cancel on every closed
admissible polygonal path, with all simultaneous walls and repeated visits retained. -/
@[simp]
theorem sum_signedCrossingEvents_loop_eq_zero_of_hyperplanes [Finite ι] (p : AdmissiblePLPath x x)
    (f : ι → V →ᵃ[ℝ] ℝ) (c : ι → E)
    (hW : ∀ j, c j ≠ 0 → W j = {z | f j z = 0}) :
    ((p.signedCrossingEvents (fun j => (f j).linear)).map
      (fun S => ∑ a ∈ S, a.2 • c a.1)).sum = 0 := by
  let := Fintype.ofFinite ι
  rw [sum_signedCrossingEvents_eq_sub_of_hyperplanes p f c hW, sub_self]

end Quiver.Path
