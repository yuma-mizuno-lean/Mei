/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalProduct
public import Mei.Topology.Order.Sign
public import Mei.Algebra.BigOperators.Group.List.Basic

/-!
# Consistency of rank-two fan configurations

Let `ℓ₁, ℓ₂` be the real extensions of two integral normals `μ₁, μ₂`, neither of whose kernels
contains the other. A directed diagram is in *fan configuration*
(`DirectedDiagram.IsFanConfiguration`) when it has two walls `j₁, j₂`, the hyperplanes
`{ℓ₁ = 0}` and `{ℓ₂ = 0}` cooriented by `μ₁` and `μ₂`, and every other wall `j` is a
half-hyperplane `{ℓⱼ = 0, ℓ₁ ≥ 0}` whose normal has real extension `ℓⱼ = p ℓ₁ + q ℓ₂` with
`p, q > 0`. Up to exchanging the two hyperplanes, this is the shape of the consistent completion
of two initial hyperplane walls: the other walls are rays of the quadrant `{ℓ₁ ≥ 0, ℓ₂ ≤ 0}` of the
plane `(ℓ₁, ℓ₂)`, around the joint `{ℓ₁ = ℓ₂ = 0}`. Infinitely many walls are allowed, and several
walls may share a support.

Write `A`, `B` and `Cⱼ` for the labels at order `k`. Suppose the walls active at order `k` other
than `j₁, j₂` are listed without repetition by a list `l`, sorted so that on `{ℓ₁ > 0}` the
positive side of each wall contains that of every later wall (equivalently, the slopes `p / q`
weakly decrease), and that `B A = A (∏_{j ∈ l} Cⱼ) B`. The chamber function `fanTransport` is
`A^[ℓ₁ > 0] (∏_{j ∈ l} Cⱼ^[ℓ₁ > 0, ℓⱼ > 0]) B^[ℓ₂ > 0]`, where `X^[P]` is `X` if `P` holds and `1`
otherwise. It is locally constant off the active walls
(`DirectedDiagram.IsFanConfiguration.eventually_fanTransport_eq`), and crossing a wall changes it
by the signed combined label of the crossing
(`DirectedDiagram.IsFanConfiguration.eventually_inv_mul_eq_combinedLabel`). Hence every admissible
path from `x` to `y` has order-`k` product `(fanTransport y)⁻¹ * fanTransport x`
(`DirectedDiagram.IsFanConfiguration.levelPathProduct_eq`), and the diagram is consistent at
order `k` (`DirectedDiagram.IsFanConfiguration.levelConsistent`). If such a list exists at every
order, the diagram is consistent (`DirectedDiagram.IsFanConfiguration.consistent`).

The relation `B A = A (∏ Cⱼ) B` rewrites the product `B A` of the initial labels as a product
sorted by slope. Such rank-two factorizations are studied in Nakanishi, *Cluster algebras and
scattering diagrams, Part III*, §5 (arXiv:2111.00800v6), whose ordering convention is opposite to
the one used here. For the pentagon identity there is one outgoing wall, and the
configuration is the consistent scattering diagram of type `A₂` (Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1, arXiv:1411.1394v2); see
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon`. The consistency is derived from the
local criterion `DirectedDiagram.levelConsistent_of_local` applied to the chamber function.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

section Transport

variable {G V κ : Type*} [Group G] [AddCommGroup V] [Module ℝ V]

section Def

variable (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ) (ℓ : κ → V →ₗ[ℝ] ℝ) (A B : G) (C : κ → G) (l : List κ)

/-- The ordered product, over the list `l` of outgoing walls `j`, of the labels `Cⱼ` of those
walls on whose positive side `{ℓ₁ > 0, ℓⱼ > 0}` the point `x` lies. -/
def fanProduct (x : V) : G :=
  (l.map fun j => if 0 < ℓ₁ x ∧ 0 < ℓ j x then C j else 1).prod

/-- The defining formula of `fanProduct`. -/
theorem fanProduct_def (x : V) :
    fanProduct ℓ₁ ℓ C l x = (l.map fun j => if 0 < ℓ₁ x ∧ 0 < ℓ j x then C j else 1).prod :=
  (rfl)

/-- The chamber function of a fan configuration: the product
`A^[ℓ₁ > 0] (∏_{j ∈ l} Cⱼ^[ℓ₁ > 0, ℓⱼ > 0]) B^[ℓ₂ > 0]`, where `X^[P]` is `X` if `P` holds and
`1` otherwise. -/
def fanTransport (x : V) : G :=
  (if 0 < ℓ₁ x then A else 1) * fanProduct ℓ₁ ℓ C l x * (if 0 < ℓ₂ x then B else 1)

/-- The defining formula of `fanTransport`. -/
theorem fanTransport_def (x : V) :
    fanTransport ℓ₁ ℓ₂ ℓ A B C l x =
      (if 0 < ℓ₁ x then A else 1) * fanProduct ℓ₁ ℓ C l x * (if 0 < ℓ₂ x then B else 1) :=
  (rfl)

end Def

variable {ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ} {ℓ : κ → V →ₗ[ℝ] ℝ} {A B : G} {C : κ → G} {l : List κ}

/-- Off `{ℓ₁ > 0}` the fan product is `1`. -/
theorem fanProduct_eq_one_of_nonpos {x : V} (hx : ℓ₁ x ≤ 0) : fanProduct ℓ₁ ℓ C l x = 1 :=
  List.prod_map_ite_eq_one fun _ _ h => absurd h.1 (not_lt.mpr hx)

/-- If `x` lies on the negative side of every outgoing wall, the fan product is `1`. -/
theorem fanProduct_eq_one_of_forall_nonpos {x : V} (hx : ∀ j ∈ l, ℓ j x ≤ 0) :
    fanProduct ℓ₁ ℓ C l x = 1 :=
  List.prod_map_ite_eq_one fun j hj h => absurd h.2 (not_lt.mpr (hx j hj))

/-- On `{ℓ₁ > 0}`, if `x` lies on the positive side of every outgoing wall, the fan product is
the product of all their labels. -/
theorem fanProduct_eq_prod_of_forall_pos {x : V} (hx₁ : 0 < ℓ₁ x) (hx : ∀ j ∈ l, 0 < ℓ j x) :
    fanProduct ℓ₁ ℓ C l x = (l.map C).prod :=
  List.prod_map_ite_eq_prod_map fun j hj h => absurd ⟨hx₁, hx j hj⟩ h

/-- If every outgoing label is `1`, the fan product is `1`. -/
theorem fanProduct_eq_one_of_forall_eq_one {x : V} (hC : ∀ j ∈ l, C j = 1) :
    fanProduct ℓ₁ ℓ C l x = 1 :=
  List.prod_map_ite_eq_one fun j hj _ => hC j hj

/-- Along a line through a point where a linear form is negative, it stays negative on both
sides for all small parameters. -/
private theorem eventually_neg_line {f : V →ₗ[ℝ] ℝ} {θ : V} (hf : f θ < 0) (w : V) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f (θ + s • w) < 0 ∧ f (θ - s • w) < 0 := by
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  filter_upwards [hle (eventually_add_mul_neg hf (f w)), hle (eventually_add_mul_neg hf (-f w))]
    with s h₁ h₂
  rw [mul_neg, ← sub_eq_add_neg] at h₂
  simpa only [map_add, map_sub, map_smul, smul_eq_mul] using ⟨h₁, h₂⟩

/-- Along a line through a point where a linear form is positive, it stays positive on both
sides for all small parameters. -/
private theorem eventually_pos_line {f : V →ₗ[ℝ] ℝ} {θ : V} (hf : 0 < f θ) (w : V) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < f (θ + s • w) ∧ 0 < f (θ - s • w) := by
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  filter_upwards [hle (eventually_pos_add_mul hf (f w)), hle (eventually_pos_add_mul hf (-f w))]
    with s h₁ h₂
  rw [mul_neg, ← sub_eq_add_neg] at h₂
  simpa only [map_add, map_sub, map_smul, smul_eq_mul] using ⟨h₁, h₂⟩

/-- Crossing the kernel of a linear form `f` in a direction `w` with `f w > 0`, the form is
positive after and negative before the crossing. -/
private theorem eventually_pos_neg_line {f : V →ₗ[ℝ] ℝ} {θ w : V} (hf : f θ = 0)
    (hw : 0 < f w) : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < f (θ + s • w) ∧ f (θ - s • w) < 0 := by
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have := mul_pos hs hw
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hf]
  constructor <;> linarith

/-- Two linear forms `p ℓ₁ + q ℓ₂` and `p' ℓ₁ + q' ℓ₂` with `q, q' > 0` vanishing at a common
point off the joint `{ℓ₁ = ℓ₂ = 0}` are positive multiples of each other. -/
private theorem exists_pos_mul_of_apply_eq_zero {f g : V →ₗ[ℝ] ℝ}
    (hf : ∃ p q : ℝ, 0 < q ∧ ∀ x, f x = p * ℓ₁ x + q * ℓ₂ x)
    (hg : ∃ p q : ℝ, 0 < q ∧ ∀ x, g x = p * ℓ₁ x + q * ℓ₂ x) {z : V}
    (hz : ℓ₁ z ≠ 0 ∨ ℓ₂ z ≠ 0) (hfz : f z = 0) (hgz : g z = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, f x = c * g x := by
  obtain ⟨p, q, hq, hf⟩ := hf
  obtain ⟨p', q', hq', hg⟩ := hg
  rw [hf] at hfz
  rw [hg] at hgz
  -- The determinant `p q' - p' q` vanishes, since `(ℓ₁ z, ℓ₂ z) ≠ 0` lies in both kernels.
  have hdet : p * q' = p' * q := by
    have h₁ : (p * q' - p' * q) * ℓ₁ z = 0 := by linear_combination q' * hfz - q * hgz
    have h₂ : (p * q' - p' * q) * ℓ₂ z = 0 := by linear_combination p * hgz - p' * hfz
    rcases hz with hz | hz
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_right hz)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_right hz)
  refine ⟨q / q', div_pos hq hq', fun x => ?_⟩
  rw [hf, hg]
  field_simp
  linear_combination ℓ₁ x * hdet

/-- Crossing `{ℓ₁ = 0}` in a direction with `ℓ₁ w > 0`, at a point with `ℓ₂ θ ≠ 0` or where `B`
and all outgoing labels are `1`, multiplies the chamber function on the right by `A`, provided
`B A = A (∏ Cⱼ) B`. -/
theorem eventually_fanTransport_fst
    (hshape : ∀ j ∈ l, ∃ p q : ℝ, 0 < q ∧ ∀ x, ℓ j x = p * ℓ₁ x + q * ℓ₂ x)
    (hrel : B * A = A * (l.map C).prod * B) {θ w : V} (hθ : ℓ₁ θ = 0)
    (hθ₂ : ℓ₂ θ ≠ 0 ∨ B = 1 ∧ ∀ j ∈ l, C j = 1) (hw : 0 < ℓ₁ w) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), fanTransport ℓ₁ ℓ₂ ℓ A B C l (θ + s • w) =
      fanTransport ℓ₁ ℓ₂ ℓ A B C l (θ - s • w) * A := by
  have h₁ := eventually_pos_neg_line hθ hw
  rcases hθ₂ with hθ₂ | ⟨rfl, hC⟩
  · rcases hθ₂.lt_or_gt with hθ₂ | hθ₂
    · -- Below the joint, every outgoing form is negative near `θ`.
      have hl : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ j ∈ {x | x ∈ l},
          ℓ j (θ + s • w) < 0 ∧ ℓ j (θ - s • w) < 0 :=
        (List.finite_toSet l).eventually_all.mpr fun j hj => eventually_neg_line (by
          obtain ⟨p, q, hq, he⟩ := hshape j hj
          rw [he, hθ]
          nlinarith) w
      filter_upwards [h₁, eventually_neg_line hθ₂ w, hl] with s h₁ h₂ h₃
      rw [fanTransport_def, fanTransport_def,
        fanProduct_eq_one_of_forall_nonpos fun j hj => (h₃ j hj).1.le,
        fanProduct_eq_one_of_forall_nonpos fun j hj => (h₃ j hj).2.le, ite_eq_left h₁.1,
        ite_eq_right (lt_asymm h₁.2), ite_eq_right (lt_asymm h₂.1), ite_eq_right (lt_asymm h₂.2)]
      group
    · -- Above the joint, every outgoing form is positive near `θ`.
      have hl : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ j ∈ {x | x ∈ l},
          0 < ℓ j (θ + s • w) ∧ 0 < ℓ j (θ - s • w) :=
        (List.finite_toSet l).eventually_all.mpr fun j hj => eventually_pos_line (by
          obtain ⟨p, q, hq, he⟩ := hshape j hj
          rw [he, hθ]
          nlinarith) w
      filter_upwards [h₁, eventually_pos_line hθ₂ w, hl] with s h₁ h₂ h₃
      rw [fanTransport_def, fanTransport_def,
        fanProduct_eq_prod_of_forall_pos h₁.1 fun j hj => (h₃ j hj).1,
        fanProduct_eq_one_of_nonpos h₁.2.le, ite_eq_left h₁.1, ite_eq_right (lt_asymm h₁.2),
        ite_eq_left h₂.1, ite_eq_left h₂.2, ← hrel]
      group
  · filter_upwards [h₁] with s h₁
    rw [fanTransport_def, fanTransport_def, fanProduct_eq_one_of_forall_eq_one hC,
      fanProduct_eq_one_of_forall_eq_one hC, ite_eq_left h₁.1, ite_eq_right (lt_asymm h₁.2)]
    simp

/-- Crossing `{ℓ₂ = 0}` in a direction with `ℓ₂ w > 0`, at a point with `ℓ₁ θ ≠ 0` or where `A`
and all outgoing labels are `1`, multiplies the chamber function on the right by `B`. -/
theorem eventually_fanTransport_snd
    (hshape : ∀ j ∈ l, ∃ p q : ℝ, 0 < p ∧ ∀ x, ℓ j x = p * ℓ₁ x + q * ℓ₂ x)
    {θ w : V} (hθ : ℓ₂ θ = 0) (hθ₁ : ℓ₁ θ ≠ 0 ∨ A = 1 ∧ ∀ j ∈ l, C j = 1) (hw : 0 < ℓ₂ w) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), fanTransport ℓ₁ ℓ₂ ℓ A B C l (θ + s • w) =
      fanTransport ℓ₁ ℓ₂ ℓ A B C l (θ - s • w) * B := by
  have h₂ := eventually_pos_neg_line hθ hw
  rcases hθ₁ with hθ₁ | ⟨rfl, hC⟩
  · rcases hθ₁.lt_or_gt with hθ₁ | hθ₁
    · filter_upwards [h₂, eventually_neg_line hθ₁ w] with s h₂ h₁
      rw [fanTransport_def, fanTransport_def, fanProduct_eq_one_of_nonpos h₁.1.le,
        fanProduct_eq_one_of_nonpos h₁.2.le, ite_eq_right (lt_asymm h₁.1),
        ite_eq_right (lt_asymm h₁.2), ite_eq_left h₂.1, ite_eq_right (lt_asymm h₂.2)]
      group
    · -- To the right of the joint, every outgoing form is positive near `θ`.
      have hl : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ j ∈ {x | x ∈ l},
          0 < ℓ j (θ + s • w) ∧ 0 < ℓ j (θ - s • w) :=
        (List.finite_toSet l).eventually_all.mpr fun j hj => eventually_pos_line (by
          obtain ⟨p, q, hp, he⟩ := hshape j hj
          rw [he, hθ]
          nlinarith) w
      filter_upwards [h₂, eventually_pos_line hθ₁ w, hl] with s h₂ h₁ h₃
      rw [fanTransport_def, fanTransport_def,
        fanProduct_eq_prod_of_forall_pos h₁.1 fun j hj => (h₃ j hj).1,
        fanProduct_eq_prod_of_forall_pos h₁.2 fun j hj => (h₃ j hj).2, ite_eq_left h₁.1,
        ite_eq_left h₁.2, ite_eq_left h₂.1, ite_eq_right (lt_asymm h₂.2)]
      group
  · filter_upwards [h₂] with s h₂
    rw [fanTransport_def, fanTransport_def, fanProduct_eq_one_of_forall_eq_one hC,
      fanProduct_eq_one_of_forall_eq_one hC, ite_eq_left h₂.1, ite_eq_right (lt_asymm h₂.2)]
    simp

/-- Crossing a common support of outgoing walls at a point `θ` with `ℓ₁ θ > 0` and `ℓ₂ θ < 0`, in
a direction `w` on whose positive side all walls through `θ` lie, multiplies the chamber function
on the right by the product of the labels of the walls through `θ`, provided no wall through `θ`
precedes a wall on whose positive side `θ` lies. -/
theorem eventually_fanTransport_outgoing {θ w : V} (hθ₁ : 0 < ℓ₁ θ) (hθ₂ : ℓ₂ θ < 0)
    (hsort : l.Pairwise fun i j => 0 < ℓ j θ → 0 < ℓ i θ)
    (htie : ∀ j ∈ l, ℓ j θ = 0 → 0 < ℓ j w) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), fanTransport ℓ₁ ℓ₂ ℓ A B C l (θ + s • w) =
      fanTransport ℓ₁ ℓ₂ ℓ A B C l (θ - s • w) *
        (l.map fun j => if ℓ j θ = 0 then C j else 1).prod := by
  -- Near `θ`, a wall `j` is crossed exactly when `ℓⱼ θ = 0`.
  have hl : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ j ∈ {x | x ∈ l},
      (0 < ℓ j (θ + s • w) ↔ 0 < ℓ j θ ∨ ℓ j θ = 0) ∧ (0 < ℓ j (θ - s • w) ↔ 0 < ℓ j θ) := by
    refine (List.finite_toSet l).eventually_all.mpr fun j hj => ?_
    rcases lt_trichotomy (ℓ j θ) 0 with hj' | hj' | hj'
    · filter_upwards [eventually_neg_line hj' w] with s hs
      exact ⟨iff_of_false (lt_asymm hs.1) (by rintro (h | h) <;> linarith),
        iff_of_false (lt_asymm hs.2) (lt_asymm hj')⟩
    · filter_upwards [eventually_pos_neg_line hj' (htie j hj hj')] with s hs
      exact ⟨iff_of_true hs.1 (Or.inr hj'), iff_of_false (lt_asymm hs.2) hj'.not_gt⟩
    · filter_upwards [eventually_pos_line hj' w] with s hs
      exact ⟨iff_of_true hs.1 (Or.inl hj'), iff_of_true hs.2 hj'⟩
  filter_upwards [eventually_pos_line hθ₁ w, eventually_neg_line hθ₂ w, hl] with s h₁ h₂ h₃
  rw [fanTransport_def, fanTransport_def, ite_eq_left h₁.1, ite_eq_left h₁.2,
    ite_eq_right (lt_asymm h₂.1), ite_eq_right (lt_asymm h₂.2), fanProduct_def, fanProduct_def,
    List.prod_map_ite_congr (q := fun j => 0 < ℓ j θ ∨ ℓ j θ = 0) fun j hj =>
      Or.inr ((and_iff_right h₁.1).trans (h₃ j hj).1),
    List.prod_map_ite_congr (q := fun j => 0 < ℓ j θ) fun j hj =>
      Or.inr ((and_iff_right h₁.2).trans (h₃ j hj).2),
    List.prod_map_ite_or C (fun j _ h he => h.ne' he)
      (hsort.imp fun hij hi hj => hi.not_gt (hij hj))]
  group

/-- If `A`, `B` and the product of the outgoing labels are `1`, and every outgoing wall with a
nontrivial label has the same positive side as a fixed form `ℓ₀`, the chamber function is `1`. -/
theorem fanTransport_eq_one {ℓ₀ : V →ₗ[ℝ] ℝ} (hC : (l.map C).prod = 1)
    (hl : ∀ j ∈ l, C j = 1 ∨ ∀ x, (0 < ℓ j x ↔ 0 < ℓ₀ x)) (x : V) :
    fanTransport ℓ₁ ℓ₂ ℓ 1 1 C l x = 1 := by
  rw [fanTransport_def, ite_self, ite_self, one_mul, mul_one, fanProduct_def,
    List.prod_map_ite_congr (q := fun _ => 0 < ℓ₁ x ∧ 0 < ℓ₀ x) fun j hj =>
      (hl j hj).imp_right fun h => and_congr_right' (h x)]
  by_cases hx : 0 < ℓ₁ x ∧ 0 < ℓ₀ x
  · rw [List.prod_map_ite_eq_prod_map fun _ _ h => absurd hx h, hC]
  · exact List.prod_map_ite_eq_one fun _ _ h => absurd h hx

end Transport

section Crossing

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]

/-- Let `T` be a function on `V` such that, near `θ`, crossing in every direction `w` with
`ℓ w > 0` multiplies `T` on the right by `X`. Then crossing in any direction `v` with
`ℓ v ≠ 0` gives `T (θ + s • v)⁻¹ * T (θ - s • v) = X⁻¹` if `ℓ v > 0` and `X` if `ℓ v < 0`,
for all small `s > 0`. -/
theorem eventually_inv_mul_eq_zpow {T : V → G} {θ v : V} {ℓ : V →ₗ[ℝ] ℝ} {X : G}
    (hT : ∀ w, 0 < ℓ w → ∀ᶠ s in 𝓝[>] (0 : ℝ), T (θ + s • w) = T (θ - s • w) * X)
    (hv : ℓ v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (T (θ + s • v))⁻¹ * T (θ - s • v) =
      X ^ (if 0 < ℓ v then -1 else 1 : ℤ) := by
  rcases hv.lt_or_gt with hv | hv
  · filter_upwards [hT (-v) (by simpa using hv)] with s hs
    rw [smul_neg, ← sub_eq_add_neg, sub_neg_eq_add] at hs
    rw [hs, ite_eq_right (not_lt.mpr hv.le)]
    group
  · filter_upwards [hT v hv] with s hs
    rw [hs, ite_eq_left hv]
    group

end Crossing

section Diagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- A directed diagram is in *fan configuration* with walls `j₁, j₂` and integral normals
`μ₁, μ₂`, with real extensions `ℓ₁, ℓ₂`, when the walls `j₁` and `j₂` are the hyperplanes
`{ℓ₁ = 0}` and `{ℓ₂ = 0}` cooriented by `μ₁` and `μ₂`, every other wall `j` is the
half-hyperplane `{ℓⱼ = 0, ℓ₁ ≥ 0}` of the real extension `ℓⱼ` of its normal, with
`ℓⱼ = p ℓ₁ + q ℓ₂` for some `p, q > 0`, and each of the kernels of `ℓ₁` and `ℓ₂` contains a
vector outside the other. -/
structure IsFanConfiguration (j₁ j₂ : ι) (μ₁ μ₂ : Λ →+ ℤ) : Prop where
  /-- The first wall is cooriented by `μ₁`. -/
  normal_fst : (D.wall j₁).normal = μ₁
  /-- The second wall is cooriented by `μ₂`. -/
  normal_snd : (D.wall j₂).normal = μ₂
  /-- The first wall is the hyperplane `{ℓ₁ = 0}`. -/
  support_fst : (D.wall j₁).support = {x | h.realCharacter μ₁ x = 0}
  /-- The second wall is the hyperplane `{ℓ₂ = 0}`. -/
  support_snd : (D.wall j₂).support = {x | h.realCharacter μ₂ x = 0}
  /-- The normal of every other wall extends to `p ℓ₁ + q ℓ₂` with `p, q > 0`. -/
  exists_apply_eq_of_ne (j : ι) (hj₁ : j ≠ j₁) (hj₂ : j ≠ j₂) : ∃ p q : ℝ, 0 < p ∧ 0 < q ∧
    ∀ x, h.realCharacter (D.wall j).normal x =
      p * h.realCharacter μ₁ x + q * h.realCharacter μ₂ x
  /-- Every other wall is the half-hyperplane `{ℓⱼ = 0, ℓ₁ ≥ 0}`. -/
  support_of_ne (j : ι) (hj₁ : j ≠ j₁) (hj₂ : j ≠ j₂) : (D.wall j).support =
    {x | h.realCharacter (D.wall j).normal x = 0 ∧ 0 ≤ h.realCharacter μ₁ x}
  /-- The kernel of `ℓ₁` is not contained in that of `ℓ₂`. -/
  exists_fst : ∃ x, h.realCharacter μ₁ x = 0 ∧ h.realCharacter μ₂ x ≠ 0
  /-- The kernel of `ℓ₂` is not contained in that of `ℓ₁`. -/
  exists_snd : ∃ x, h.realCharacter μ₂ x = 0 ∧ h.realCharacter μ₁ x ≠ 0

namespace IsFanConfiguration

variable {D} {j₁ j₂ : ι} {μ₁ μ₂ : Λ →+ ℤ} (hD : D.IsFanConfiguration j₁ j₂ μ₁ μ₂)
include hD

local notation "ℓ₁" => h.realCharacter μ₁
local notation "ℓ₂" => h.realCharacter μ₂

/-- The two hyperplane walls are distinct. -/
theorem fst_ne_snd : j₁ ≠ j₂ := by
  rintro rfl
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  rw [← hD.normal_fst, hD.normal_snd] at hx₁
  exact hx₂ hx₁

/-- Every outgoing wall vanishes at a point off `{ℓ₁ = 0}`. -/
private theorem exists_apply_eq_zero {j : ι} (hj₁ : j ≠ j₁) (hj₂ : j ≠ j₂) :
    ∃ z, ℓ₁ z ≠ 0 ∧ h.realCharacter (D.wall j).normal z = 0 := by
  obtain ⟨p, q, -, hq, he⟩ := hD.exists_apply_eq_of_ne j hj₁ hj₂
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  obtain ⟨y, hy₂, hy₁⟩ := hD.exists_snd
  -- The point `z` with `(ℓ₁ z, ℓ₂ z) = (q, -p)`.
  refine ⟨(q / ℓ₁ y) • y - (p / ℓ₂ x) • x, ?_, ?_⟩
  · simp only [map_sub, map_smul, smul_eq_mul, hx₁, mul_zero, sub_zero, ne_eq,
      div_mul_cancel₀ q hy₁]
    exact hq.ne'
  · rw [he]
    simp only [map_sub, map_smul, smul_eq_mul, hx₁, hy₂, mul_zero, sub_zero, zero_sub,
      div_mul_cancel₀ q hy₁, div_mul_cancel₀ p hx₂]
    ring

omit hD in
/-- Active walls through a point outside the singular support of the active walls have the
same kernel. -/
private theorem apply_eq_zero_iff_of_mem_support {k : ℕ} {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {a b : ι}
    (ha : a ∈ D.active k) (hb : b ∈ D.active k) (hθa : θ ∈ (D.wall a).support)
    (hθb : θ ∈ (D.wall b).support) (x : V) :
    h.realCharacter (D.wall a).normal x = 0 ↔ h.realCharacter (D.wall b).normal x = 0 := by
  have hker : LinearMap.ker (h.realCharacter (D.wall a).normal) =
      LinearMap.ker (h.realCharacter (D.wall b).normal) := by
    rw [← (D.wall a).direction_support, ← (D.wall b).direction_support]
    exact congrArg AffineSubspace.direction (affineSpan_eq_of_notMem_singularSupport
      (W := fun j : D.active k => (D.wall j).support) (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) hθ hθa hθb)
  simpa only [LinearMap.mem_ker] using SetLike.ext_iff.mp hker x

/-- An active wall through a point of the active first wall outside the singular support of the
active walls is the first wall. -/
theorem eq_fst_of_mem_support {k : ℕ} {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {b : ι}
    (hb : b ∈ D.active k) (hθb : θ ∈ (D.wall b).support) (h₁ : j₁ ∈ D.active k)
    (hθ₁ : θ ∈ (D.wall j₁).support) : b = j₁ := by
  obtain ⟨x, hx₁, hx₂⟩ := hD.exists_fst
  have hx := (apply_eq_zero_iff_of_mem_support hθ h₁ hb hθ₁ hθb x).mp (by
    rw [hD.normal_fst]
    exact hx₁)
  by_contra hb₁
  by_cases hb₂ : b = j₂
  · subst hb₂
    rw [hD.normal_snd] at hx
    exact hx₂ hx
  · obtain ⟨p, q, -, hq, he⟩ := hD.exists_apply_eq_of_ne b hb₁ hb₂
    rw [he, hx₁, mul_zero, zero_add] at hx
    exact hx₂ ((mul_eq_zero.mp hx).resolve_left hq.ne')

/-- An active wall through a point of the active second wall outside the singular support of
the active walls is the second wall. -/
theorem eq_snd_of_mem_support {k : ℕ} {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {b : ι}
    (hb : b ∈ D.active k) (hθb : θ ∈ (D.wall b).support) (h₂ : j₂ ∈ D.active k)
    (hθ₂ : θ ∈ (D.wall j₂).support) : b = j₂ := by
  obtain ⟨y, hy₂, hy₁⟩ := hD.exists_snd
  have hy := (apply_eq_zero_iff_of_mem_support hθ h₂ hb hθ₂ hθb y).mp (by
    rw [hD.normal_snd]
    exact hy₂)
  by_contra hb₂
  by_cases hb₁ : b = j₁
  · subst hb₁
    rw [hD.normal_fst] at hy
    exact hy₁ hy
  · obtain ⟨p, q, hp, -, he⟩ := hD.exists_apply_eq_of_ne b hb₁ hb₂
    rw [he, hy₂, mul_zero, add_zero] at hy
    exact hy₁ ((mul_eq_zero.mp hy).resolve_left hp.ne')

/-- Two active outgoing walls through a point outside the singular support of the active walls
have normals with positively proportional real extensions. -/
private theorem exists_pos_mul_of_mem_support {k : ℕ} {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {a b : ι}
    (ha : a ∈ D.active k) (ha₁ : a ≠ j₁) (ha₂ : a ≠ j₂) (hb : b ∈ D.active k) (hb₁ : b ≠ j₁)
    (hb₂ : b ≠ j₂) (hθa : θ ∈ (D.wall a).support) (hθb : θ ∈ (D.wall b).support) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, h.realCharacter (D.wall a).normal x =
      c * h.realCharacter (D.wall b).normal x := by
  obtain ⟨z, hz₁, hz⟩ := hD.exists_apply_eq_zero hb₁ hb₂
  exact exists_pos_mul_of_apply_eq_zero
    ((hD.exists_apply_eq_of_ne a ha₁ ha₂).imp fun _ ⟨q, _, hq, he⟩ => ⟨q, hq, he⟩)
    ((hD.exists_apply_eq_of_ne b hb₁ hb₂).imp fun _ ⟨q, _, hq, he⟩ => ⟨q, hq, he⟩) (Or.inl hz₁)
    ((apply_eq_zero_iff_of_mem_support hθ ha hb hθa hθb z).mpr hz) hz

variable (k : ℕ) {l : List ι} (hj₁ : j₁ ∉ l) (hj₂ : j₂ ∉ l)

local notation "𝒜" => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall D j₁))
local notation "ℬ" => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall D j₂))
local notation "𝒞" => fun j => CompletedGroup.projection k
  (DirectedWall.label (DirectedDiagram.wall D j))
local notation "𝓁" => fun j => h.realCharacter (DirectedWall.normal (DirectedDiagram.wall D j))
local notation "𝒯" => fanTransport ℓ₁ ℓ₂ 𝓁 𝒜 ℬ 𝒞 l

include hj₁ hj₂

omit hD in
/-- The walls of the list are neither of the hyperplane walls. -/
private theorem ne_of_mem {j : ι} (hj : j ∈ l) : j ≠ j₁ ∧ j ≠ j₂ :=
  ⟨fun he => hj₁ (he ▸ hj), fun he => hj₂ (he ▸ hj)⟩

/-- The normals of the walls of the list extend to positive combinations of `ℓ₁` and `ℓ₂`. -/
private theorem shape : ∀ j ∈ l, ∃ p q : ℝ, 0 < p ∧ 0 < q ∧
    ∀ x, h.realCharacter (D.wall j).normal x = p * ℓ₁ x + q * ℓ₂ x := fun j hj =>
  hD.exists_apply_eq_of_ne j (ne_of_mem hj₁ hj₂ hj).1 (ne_of_mem hj₁ hj₂ hj).2

/-- The walls of the list are the half-hyperplanes `{ℓⱼ = 0, ℓ₁ ≥ 0}`. -/
private theorem support_of_mem {j : ι} (hj : j ∈ l) :
    (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = 0 ∧ 0 ≤ ℓ₁ x} :=
  hD.support_of_ne j (ne_of_mem hj₁ hj₂ hj).1 (ne_of_mem hj₁ hj₂ hj).2

/-- Every wall of the list contains the joint `{ℓ₁ = ℓ₂ = 0}`. -/
private theorem mem_support_of_mem {θ : V} (hθ₁ : ℓ₁ θ = 0) (hθ₂ : ℓ₂ θ = 0) {j : ι}
    (hj : j ∈ l) : θ ∈ (D.wall j).support := by
  obtain ⟨p, q, -, -, he⟩ := hD.shape hj₁ hj₂ j hj
  rw [hD.support_of_mem hj₁ hj₂ hj]
  exact ⟨by rw [he, hθ₁, hθ₂]; ring, hθ₁.ge⟩

variable (hrel : CompletedGroup.projection k (D.wall j₂).label *
    CompletedGroup.projection k (D.wall j₁).label =
  CompletedGroup.projection k (D.wall j₁).label *
    (l.map fun j => CompletedGroup.projection k (D.wall j).label).prod *
    CompletedGroup.projection k (D.wall j₂).label)
include hrel

/-- Off the active walls, the fan product of the order-`k` labels is locally constant. -/
private theorem eventually_fanProduct_eq {θ : V}
    (hθ : ∀ j : D.active k, θ ∉ (D.wall j).support) :
    ∀ᶠ φ in 𝓝 θ, fanProduct ℓ₁ 𝓁 𝒞 l φ = fanProduct ℓ₁ 𝓁 𝒞 l θ := by
  let := h.finiteDimensional
  have hc (f : V →ₗ[ℝ] ℝ) : ContinuousAt f θ :=
    (LinearMap.continuous_of_finiteDimensional f).continuousAt
  have hneg {f : V →ₗ[ℝ] ℝ} (hf : f θ < 0) : ∀ᶠ φ in 𝓝 θ, f φ < 0 :=
    (hc f).eventually_lt continuousAt_const hf
  have hpos {f : V →ₗ[ℝ] ℝ} (hf : 0 < f θ) : ∀ᶠ φ in 𝓝 θ, 0 < f φ :=
    continuousAt_const.eventually_lt (hc f) hf
  -- A wall with a nonvanishing projected label does not contain `θ`.
  have hoff (j : ι) (hj : CompletedGroup.projection k (D.wall j).label ≠ 1) :
      θ ∉ (D.wall j).support := hθ ⟨j, (D.mem_active k j).mpr hj⟩
  rcases lt_trichotomy (ℓ₁ θ) 0 with h₁ | h₁ | h₁
  · filter_upwards [hneg h₁] with φ hφ
    rw [fanProduct_eq_one_of_nonpos hφ.le, fanProduct_eq_one_of_nonpos h₁.le]
  · -- On `{ℓ₁ = 0}` the first wall is inactive, so the outgoing labels have product `1`.
    have hA : 𝒜 = 1 := not_not.mp fun hA => hoff j₁ hA (by rw [hD.support_fst]; exact h₁)
    rw [hA, one_mul, mul_one] at hrel
    have hprod := mul_eq_right.mp hrel.symm
    rcases lt_trichotomy (ℓ₂ θ) 0 with h₂ | h₂ | h₂
    · have hl : ∀ᶠ φ in 𝓝 θ, ∀ j ∈ {x | x ∈ l}, h.realCharacter (D.wall j).normal φ < 0 :=
        (List.finite_toSet l).eventually_all.mpr fun j hj => hneg (by
          obtain ⟨p, q, -, hq, he⟩ := hD.shape hj₁ hj₂ j hj
          rw [he, h₁]
          nlinarith)
      filter_upwards [hl] with φ hφ
      rw [fanProduct_eq_one_of_forall_nonpos fun j hj => (hφ j hj).le,
        fanProduct_eq_one_of_nonpos h₁.le]
    · -- On the joint every wall of the list contains `θ`, so all of their labels vanish.
      have hC : ∀ j ∈ l, CompletedGroup.projection k (D.wall j).label = 1 := fun j hj =>
        not_not.mp fun hne => hoff j hne (hD.mem_support_of_mem hj₁ hj₂ h₁ h₂ hj)
      exact Eventually.of_forall fun φ => by
        rw [fanProduct_eq_one_of_forall_eq_one hC, fanProduct_eq_one_of_forall_eq_one hC]
    · have hl : ∀ᶠ φ in 𝓝 θ, ∀ j ∈ {x | x ∈ l}, 0 < h.realCharacter (D.wall j).normal φ :=
        (List.finite_toSet l).eventually_all.mpr fun j hj => hpos (by
          obtain ⟨p, q, -, hq, he⟩ := hD.shape hj₁ hj₂ j hj
          rw [he, h₁]
          nlinarith)
      filter_upwards [hl] with φ hφ
      rw [fanProduct_eq_one_of_nonpos h₁.le]
      by_cases hφ₁ : 0 < ℓ₁ φ
      · rw [fanProduct_eq_prod_of_forall_pos hφ₁ fun j hj => hφ j hj, hprod]
      · exact fanProduct_eq_one_of_nonpos (not_lt.mp hφ₁)
  · -- To the right of `{ℓ₁ = 0}`, each wall with a nontrivial label keeps its side.
    have hl : ∀ᶠ φ in 𝓝 θ, ∀ j ∈ {x | x ∈ l}, CompletedGroup.projection k (D.wall j).label = 1 ∨
        (0 < h.realCharacter (D.wall j).normal φ ↔ 0 < h.realCharacter (D.wall j).normal θ) := by
      refine (List.finite_toSet l).eventually_all.mpr fun j hj => ?_
      by_cases hj' : CompletedGroup.projection k (D.wall j).label = 1
      · exact Eventually.of_forall fun _ => Or.inl hj'
      · have hz : h.realCharacter (D.wall j).normal θ ≠ 0 := fun hz =>
          hoff j hj' (by rw [hD.support_of_mem hj₁ hj₂ hj]; exact ⟨hz, h₁.le⟩)
        rcases hz.lt_or_gt with hz | hz
        · exact (hneg hz).mono fun _ hφ => Or.inr (iff_of_false (lt_asymm hφ) (lt_asymm hz))
        · exact (hpos hz).mono fun _ hφ => Or.inr (iff_of_true hφ hz)
    filter_upwards [hpos h₁, hl] with φ hφ₁ hφ
    exact List.prod_map_ite_congr fun j hj => (hφ j hj).imp_right fun hj' =>
      and_congr (iff_of_true hφ₁ h₁) hj'

/-- Off the active walls, the chamber function of the order-`k` labels is locally constant,
provided the list `l` avoids the hyperplane walls and `B A = A (∏_{j ∈ l} Cⱼ) B`. -/
theorem eventually_fanTransport_eq {θ : V} (hθ : ∀ j : D.active k, θ ∉ (D.wall j).support) :
    ∀ᶠ φ in 𝓝 θ, 𝒯 φ = 𝒯 θ := by
  let := h.finiteDimensional
  have key {X : (d.groupTower ℒ).obj (Opposite.op k)} {f : V →ₗ[ℝ] ℝ}
      (hX : X = 1 ∨ f θ ≠ 0) :
      ∀ᶠ φ in 𝓝 θ, (if 0 < f φ then X else 1) = if 0 < f θ then X else 1 := by
    rcases hX with rfl | hX
    · exact Eventually.of_forall fun _ => by simp
    · have hc := (LinearMap.continuous_of_finiteDimensional f).continuousAt (x := θ)
      rcases hX.lt_or_gt with hX | hX
      · filter_upwards [hc.eventually_lt continuousAt_const hX] with φ hφ
        rw [ite_eq_right (lt_asymm hφ), ite_eq_right (lt_asymm hX)]
      · filter_upwards [continuousAt_const.eventually_lt hc hX] with φ hφ
        rw [ite_eq_left hφ, ite_eq_left hX]
  -- A hyperplane wall with a nonvanishing projected label does not contain `θ`.
  have hA : 𝒜 = 1 ∨ ℓ₁ θ ≠ 0 := or_iff_not_imp_left.mpr fun hA hz =>
    hθ ⟨j₁, (D.mem_active k j₁).mpr hA⟩ (by rw [hD.support_fst]; exact hz)
  have hB : ℬ = 1 ∨ ℓ₂ θ ≠ 0 := or_iff_not_imp_left.mpr fun hB hz =>
    hθ ⟨j₂, (D.mem_active k j₂).mpr hB⟩ (by rw [hD.support_snd]; exact hz)
  filter_upwards [key hA, key hB, hD.eventually_fanProduct_eq k hj₁ hj₂ hrel hθ]
    with φ h₁ h₂ h₃
  rw [fanTransport_def, fanTransport_def, h₃]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) h₁ rfl) h₂

omit hrel in
/-- At a point of the active first wall outside the singular support of the active walls,
crossing in a transverse direction changes the chamber function by the combined label. -/
private theorem eventually_inv_mul_fst {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) (h₁ : j₁ ∈ D.active k)
    (hθ₁ : θ ∈ (D.wall j₁).support) {v : V}
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0)
    (hrel : CompletedGroup.projection k (D.wall j₂).label *
        CompletedGroup.projection k (D.wall j₁).label =
      CompletedGroup.projection k (D.wall j₁).label *
        (l.map fun j => CompletedGroup.projection k (D.wall j).label).prod *
        CompletedGroup.projection k (D.wall j₂).label) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (𝒯 (θ + s • v))⁻¹ * 𝒯 (θ - s • v) = D.combinedLabel k θ v hθ := by
  have hθ₁' : ℓ₁ θ = 0 := by simpa [hD.support_fst] using hθ₁
  rw [D.combinedLabel_eq_prod k θ v hθ [⟨j₁, h₁⟩] (List.nodup_singleton _) fun b =>
    ⟨fun hb => List.eq_of_mem_singleton hb ▸ hθ₁, fun hb => List.mem_singleton.mpr
      (Subtype.ext (hD.eq_fst_of_mem_support hθ b.2 hb h₁ hθ₁))⟩]
  simp only [List.map_cons, List.map_nil, List.prod_singleton]
  have hvj := hv ⟨j₁, h₁⟩ hθ₁
  rw [hD.normal_fst] at hvj ⊢
  refine eventually_inv_mul_eq_zpow (fun w hw =>
    eventually_fanTransport_fst
      (fun j hj => (hD.shape hj₁ hj₂ j hj).imp fun _ ⟨q, _, hq, he⟩ => ⟨q, hq, he⟩) hrel hθ₁' ?_
      hw) hvj
  -- On the joint, the second wall and the walls of the list are inactive.
  refine or_iff_not_imp_left.mpr fun hθ₂ => ?_
  have hθ₂ : ℓ₂ θ = 0 := not_not.mp hθ₂
  refine ⟨?_, fun j hj => ?_⟩ <;> by_contra hne
  · exact hD.fst_ne_snd (hD.eq_fst_of_mem_support hθ ((D.mem_active k j₂).mpr hne)
      (by rw [hD.support_snd]; exact hθ₂) h₁ hθ₁).symm
  · exact (ne_of_mem hj₁ hj₂ hj).1 (hD.eq_fst_of_mem_support hθ ((D.mem_active k j).mpr hne)
      (hD.mem_support_of_mem hj₁ hj₂ hθ₁' hθ₂ hj) h₁ hθ₁)

omit hrel in
/-- At a point of the active second wall outside the singular support of the active walls,
crossing in a transverse direction changes the chamber function by the combined label. -/
private theorem eventually_inv_mul_snd {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) (h₂ : j₂ ∈ D.active k)
    (hθ₂ : θ ∈ (D.wall j₂).support) {v : V}
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (𝒯 (θ + s • v))⁻¹ * 𝒯 (θ - s • v) = D.combinedLabel k θ v hθ := by
  have hθ₂' : ℓ₂ θ = 0 := by simpa [hD.support_snd] using hθ₂
  rw [D.combinedLabel_eq_prod k θ v hθ [⟨j₂, h₂⟩] (List.nodup_singleton _) fun b =>
    ⟨fun hb => List.eq_of_mem_singleton hb ▸ hθ₂, fun hb => List.mem_singleton.mpr
      (Subtype.ext (hD.eq_snd_of_mem_support hθ b.2 hb h₂ hθ₂))⟩]
  simp only [List.map_cons, List.map_nil, List.prod_singleton]
  have hvj := hv ⟨j₂, h₂⟩ hθ₂
  rw [hD.normal_snd] at hvj ⊢
  refine eventually_inv_mul_eq_zpow (fun w hw =>
    eventually_fanTransport_snd
      (fun j hj => (hD.shape hj₁ hj₂ j hj).imp fun _ ⟨q, hp, _, he⟩ => ⟨q, hp, he⟩) hθ₂' ?_
      hw) hvj
  -- On the joint, the first wall and the walls of the list are inactive.
  refine or_iff_not_imp_left.mpr fun hθ₁ => ?_
  have hθ₁ : ℓ₁ θ = 0 := not_not.mp hθ₁
  refine ⟨?_, fun j hj => ?_⟩ <;> by_contra hne
  · exact hD.fst_ne_snd (hD.eq_snd_of_mem_support hθ ((D.mem_active k j₁).mpr hne)
      (by rw [hD.support_fst]; exact hθ₁) h₂ hθ₂)
  · exact (ne_of_mem hj₁ hj₂ hj).2 (hD.eq_snd_of_mem_support hθ ((D.mem_active k j).mpr hne)
      (hD.mem_support_of_mem hj₁ hj₂ hθ₁ hθ₂' hj) h₂ hθ₂)

variable (hl : l.Nodup) (hact : ∀ j ∈ D.active k, j ≠ j₁ → j ≠ j₂ → j ∈ l)
include hl hact

omit hrel in
/-- At a point of an active outgoing wall outside the singular support of the active walls,
the combined label in a transverse direction is the product of the labels of the walls of the
list through that point, inverted if the direction points to their positive side. -/
private theorem combinedLabel_eq_zpow {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {j₀ : ι}
    (hj₀ : j₀ ∈ D.active k) (hj₀₁ : j₀ ≠ j₁) (hj₀₂ : j₀ ≠ j₂) (hθj₀ : θ ∈ (D.wall j₀).support)
    {v : V}
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0) :
    D.combinedLabel k θ v hθ =
      (l.map fun j => if h.realCharacter (D.wall j).normal θ = 0 then
        CompletedGroup.projection k (D.wall j).label else 1).prod ^
        (if 0 < h.realCharacter (D.wall j₀).normal v then -1 else 1 : ℤ) := by
  classical
  have hθ₁ : 0 ≤ ℓ₁ θ := by
    rw [hD.support_of_ne j₀ hj₀₁ hj₀₂] at hθj₀
    exact hθj₀.2
  -- The active walls through `θ` are the active walls of the list vanishing at `θ`.
  have hinc (b : D.active k) : θ ∈ (D.wall b).support ↔
      (b : ι) ∈ l ∧ h.realCharacter (D.wall b).normal θ = 0 := by
    constructor
    · intro hb
      have hb₁ : (b : ι) ≠ j₁ := fun he =>
        hj₀₁ (hD.eq_fst_of_mem_support hθ hj₀ hθj₀ (he ▸ b.2) (he ▸ hb))
      have hb₂ : (b : ι) ≠ j₂ := fun he =>
        hj₀₂ (hD.eq_snd_of_mem_support hθ hj₀ hθj₀ (he ▸ b.2) (he ▸ hb))
      rw [hD.support_of_ne b hb₁ hb₂] at hb
      exact ⟨hact b b.2 hb₁ hb₂, hb.1⟩
    · rintro ⟨hbl, hb⟩
      rw [hD.support_of_mem hj₁ hj₂ hbl]
      exact ⟨hb, hθ₁⟩
  -- The walls through `θ` lie on the same side of every direction as `j₀`.
  have hsign (b : D.active k) (hb : θ ∈ (D.wall b).support) (x : V) :
      (0 < h.realCharacter (D.wall b).normal x ↔ 0 < h.realCharacter (D.wall j₀).normal x) := by
    have hbl := ((hinc b).mp hb).1
    obtain ⟨c, hc, he⟩ := hD.exists_pos_mul_of_mem_support hθ b.2 (ne_of_mem hj₁ hj₂ hbl).1
      (ne_of_mem hj₁ hj₂ hbl).2 hj₀ hj₀₁ hj₀₂ hb hθj₀
    rw [he, mul_pos_iff_of_pos_left hc]
  -- It suffices to treat directions pointing to the negative side of `j₀`.
  have key (v : V)
      (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0)
      (hneg : h.realCharacter (D.wall j₀).normal v < 0) :
      D.combinedLabel k θ v hθ = (l.map fun j => if h.realCharacter (D.wall j).normal θ = 0 then
        CompletedGroup.projection k (D.wall j).label else 1).prod := by
    let P : ι → Prop := fun j => j ∈ D.active k ∧ h.realCharacter (D.wall j).normal θ = 0
    let m : List (D.active k) := (l.filter fun j => P j).pmap Subtype.mk fun j hj =>
      (of_decide_eq_true (List.mem_filter.mp hj).2).1
    have hm (b : D.active k) : b ∈ m ↔ θ ∈ (D.wall b).support := by
      rw [hinc b, List.mem_pmap]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨(List.mem_filter.mp ha).1, (of_decide_eq_true (List.mem_filter.mp ha).2).2⟩
      · rintro ⟨hbl, hb⟩
        exact ⟨b, List.mem_filter.mpr ⟨hbl, decide_eq_true ⟨b.2, hb⟩⟩, rfl⟩
    have hnodup : m.Nodup :=
      (hl.filter _).pmap fun _ _ _ _ he => congrArg Subtype.val he
    refine (D.combinedLabel_eq_prod k θ v hθ m hnodup hm).trans ?_
    rw [List.map_congr_left
        (g := fun b : D.active k => CompletedGroup.projection k (D.wall b).label) fun b hb => by
          rw [ite_eq_right (by rw [hsign b ((hm b).mp hb)]; exact lt_asymm hneg), zpow_one]]
    simp only [m, List.map_pmap, List.pmap_eq_map]
    rw [List.prod_map_filter_eq_prod_map_ite]
    refine List.prod_map_ite_congr fun j _ => ?_
    by_cases hj : j ∈ D.active k
    · exact Or.inr (and_iff_right hj)
    · exact Or.inl (not_not.mp ((D.mem_active k j).not.mp hj))
  rcases (hv ⟨j₀, hj₀⟩ hθj₀).lt_or_gt with hneg | hpos
  · rw [ite_eq_right (lt_asymm hneg), zpow_one]
    exact key v hv hneg
  · have hv' : ∀ j : D.active k, θ ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal (-v) ≠ 0 := fun j hj => by
      rw [map_neg, neg_ne_zero]
      exact hv j hj
    rw [ite_eq_left hpos, zpow_neg_one]
    have hk := (key (-v) hv' (by rw [map_neg]; exact neg_neg_of_pos hpos)).symm.trans
      (D.combinedLabel_neg k θ v hθ hv)
    exact (inv_eq_iff_eq_inv.mpr hk).symm

variable (hsort : l.Pairwise fun i j => ∀ x, 0 < h.realCharacter μ₁ x →
  0 < h.realCharacter (D.wall j).normal x → 0 < h.realCharacter (D.wall i).normal x)
include hsort

/-- At a point of an active outgoing wall outside the singular support of the active walls,
crossing in a transverse direction changes the chamber function by the combined label. -/
private theorem eventually_inv_mul_outgoing {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {j₀ : ι}
    (hj₀ : j₀ ∈ D.active k) (h₀₁ : j₀ ≠ j₁) (h₀₂ : j₀ ≠ j₂) (hθj₀ : θ ∈ (D.wall j₀).support)
    {v : V}
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (𝒯 (θ + s • v))⁻¹ * 𝒯 (θ - s • v) = D.combinedLabel k θ v hθ := by
  have hshape := hD.shape hj₁ hj₂
  rw [hD.combinedLabel_eq_zpow k hj₁ hj₂ hl hact hθ hj₀ h₀₁ h₀₂ hθj₀ hv]
  have hvj := hv ⟨j₀, hj₀⟩ hθj₀
  have hθj₀' := hθj₀
  rw [hD.support_of_ne j₀ h₀₁ h₀₂] at hθj₀'
  obtain ⟨p₀, q₀, hp₀, hq₀, he₀⟩ := hD.exists_apply_eq_of_ne j₀ h₀₁ h₀₂
  rcases hθj₀'.2.lt_or_eq with hθ₁ | hθ₁
  · -- Away from the joint the crossing multiplies by the labels of the walls through `θ`.
    have hθ₂ : ℓ₂ θ < 0 := by
      have := hθj₀'.1
      rw [he₀] at this
      nlinarith
    refine eventually_inv_mul_eq_zpow (fun w hw =>
      eventually_fanTransport_outgoing hθ₁ hθ₂ (hsort.imp fun hij => hij θ hθ₁)
        fun j hj hjθ => ?_) hvj
    obtain ⟨c, hc, he⟩ := exists_pos_mul_of_apply_eq_zero
      ((hshape j hj).imp fun _ ⟨q, _, hq, he⟩ => ⟨q, hq, he⟩)
      ((hD.exists_apply_eq_of_ne j₀ h₀₁ h₀₂).imp fun _ ⟨q, _, hq, he⟩ => ⟨q, hq, he⟩)
      (Or.inl hθ₁.ne') hjθ hθj₀'.1
    rw [he]
    exact mul_pos hc hw
  · -- At the joint, `A`, `B` and the product of the outgoing labels are `1`, and so are the
    -- chamber function and the combined label.
    have hθ₂ : ℓ₂ θ = 0 := by
      have := hθj₀'.1
      rw [he₀, ← hθ₁, mul_zero, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hq₀.ne'
    have hA : 𝒜 = 1 := by
      by_contra hne
      exact h₀₁ (hD.eq_fst_of_mem_support hθ hj₀ hθj₀ ((D.mem_active k j₁).mpr hne)
        (by rw [hD.support_fst]; exact hθ₁.symm))
    have hB : ℬ = 1 := by
      by_contra hne
      exact h₀₂ (hD.eq_snd_of_mem_support hθ hj₀ hθj₀ ((D.mem_active k j₂).mpr hne)
        (by rw [hD.support_snd]; exact hθ₂))
    simp only [hA, hB, one_mul, mul_one] at hrel
    have hprod := hrel.symm
    have hT (x : V) : 𝒯 x = 1 := by
      rw [hA, hB]
      refine fanTransport_eq_one (ℓ₀ := h.realCharacter (D.wall j₀).normal) hprod
        (fun j hj => ?_) x
      by_cases hne : CompletedGroup.projection k (D.wall j).label = 1
      · exact Or.inl hne
      · refine Or.inr fun x => ?_
        have hjθ := hD.mem_support_of_mem hj₁ hj₂ hθ₁.symm hθ₂ hj
        obtain ⟨c, hc, he⟩ := hD.exists_pos_mul_of_mem_support hθ ((D.mem_active k j).mpr hne)
          (ne_of_mem hj₁ hj₂ hj).1 (ne_of_mem hj₁ hj₂ hj).2 hj₀ h₀₁ h₀₂ hjθ hθj₀
        rw [he, mul_pos_iff_of_pos_left hc]
    have hX : (l.map fun j => if h.realCharacter (D.wall j).normal θ = 0 then
        CompletedGroup.projection k (D.wall j).label else 1).prod = 1 := by
      rw [List.prod_map_ite_eq_prod_map fun j hj hne => absurd (by
        obtain ⟨p, q, -, -, he⟩ := hshape j hj
        rw [he, ← hθ₁, hθ₂]
        ring) hne]
      exact hprod
    refine Eventually.of_forall fun s => ?_
    rw [hT, hT, hX, inv_one, one_mul, one_zpow]

/-- At a point `θ` outside the singular support of the walls active at order `k`, crossing in a
direction transverse to these walls changes the chamber function by the combined label,
provided the list `l` contains the active outgoing walls without repetition, sorted as in
`DirectedDiagram.IsFanConfiguration.levelConsistent`, and `B A = A (∏_{j ∈ l} Cⱼ) B`. -/
theorem eventually_inv_mul_eq_combinedLabel {θ : V}
    (hθ : θ ∉ singularSupport fun j : D.active k => (D.wall j).support) {v : V}
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support → h.realCharacter (D.wall j).normal v ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (𝒯 (θ + s • v))⁻¹ * 𝒯 (θ - s • v) = D.combinedLabel k θ v hθ := by
  by_cases hoff : ∀ j : D.active k, θ ∉ (D.wall j).support
  · -- Off the walls, the chamber function is constant near `θ`.
    rw [D.combinedLabel_eq_one_of_forall_notMem k θ v hθ hoff]
    have ht : ∀ w : V, Tendsto (fun s : ℝ => θ + s • w) (𝓝[>] 0) (𝓝 θ) := fun w =>
      tendsto_nhdsWithin_of_tendsto_nhds (by
        simpa using (show Continuous fun s : ℝ => θ + s • w by fun_prop).tendsto 0)
    have he := hD.eventually_fanTransport_eq k hj₁ hj₂ hrel hoff
    filter_upwards [ht v he, ht (-v) he] with s h₁ h₂
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, smul_neg, ← sub_eq_add_neg] at h₁ h₂
    rw [h₁, h₂]
    exact inv_mul_cancel _
  simp only [not_forall, not_not] at hoff
  obtain ⟨⟨j₀, hj₀⟩, hθj₀⟩ := hoff
  by_cases h₀₁ : j₀ = j₁
  · subst h₀₁
    exact hD.eventually_inv_mul_fst k hj₁ hj₂ hθ hj₀ hθj₀ hv hrel
  by_cases h₀₂ : j₀ = j₂
  · subst h₀₂
    exact hD.eventually_inv_mul_snd k hj₁ hj₂ hθ hj₀ hθj₀ hv
  exact hD.eventually_inv_mul_outgoing k hj₁ hj₂ hrel hl hact hsort hθ hj₀ h₀₁ h₀₂ hθj₀ hv

/-- Every admissible path from `x` to `y` has order-`k` product
`(fanTransport y)⁻¹ * fanTransport x`, under the hypotheses of
`DirectedDiagram.IsFanConfiguration.levelConsistent`. -/
theorem levelPathProduct_eq {x y : WallComplement fun j : D.active k => (D.wall j).support}
    (p : AdmissiblePLPath x y) : D.levelPathProduct k p = (𝒯 y.val)⁻¹ * 𝒯 x.val := by
  rw [D.levelPathProduct_eq_mul_inv_of_local k (F := fun x => (𝒯 x)⁻¹)
    (fun _ hθ => (hD.eventually_fanTransport_eq k hj₁ hj₂ hrel hθ).mono fun _ hφ =>
      congrArg (·⁻¹) hφ)
    (fun _ hθ _ hv => (hD.eventually_inv_mul_eq_combinedLabel k hj₁ hj₂ hrel hl hact hsort hθ
      hv).mono fun _ hs => (congrArg (_ * ·) (inv_inv _)).trans hs) p]
  exact congrArg (_ * ·) (inv_inv _)

/-- **Consistency of a fan configuration at order `k`.** A directed diagram in fan configuration
is consistent at order `k` if the walls active at order `k` other than the hyperplane walls are
listed without repetition, in an order in which no wall has positive side on `{ℓ₁ > 0}` larger
than that of an earlier wall, by a list `l` such that the labels `A, B` of `{ℓ₁ = 0}` and
`{ℓ₂ = 0}` and `Cⱼ` of the walls `j` of `l` satisfy `B A = A (∏_{j ∈ l} Cⱼ) B` at order `k`. -/
theorem levelConsistent : D.LevelConsistent k :=
  (D.levelConsistent_iff_loops k).mpr fun _ p => by
    rw [hD.levelPathProduct_eq k hj₁ hj₂ hrel hl hact hsort p, inv_mul_cancel]
    rfl

end IsFanConfiguration

variable {D} in
/-- **Consistency of a fan configuration.** A directed diagram in fan configuration is consistent
if at every order `k` the walls active at order `k` other than the hyperplane walls are listed
without repetition, in an order in which no wall has positive side on `{ℓ₁ > 0}` larger than that
of an earlier wall, by a list `l` such that the labels `A, B` of `{ℓ₁ = 0}` and `{ℓ₂ = 0}` and
`Cⱼ` of the walls `j` of `l` satisfy `B A = A (∏_{j ∈ l} Cⱼ) B` at order `k`. -/
theorem IsFanConfiguration.consistent {j₁ j₂ : ι} {μ₁ μ₂ : Λ →+ ℤ}
    (hD : D.IsFanConfiguration j₁ j₂ μ₁ μ₂)
    (hfac : ∀ k, ∃ l : List ι, l.Nodup ∧ j₁ ∉ l ∧ j₂ ∉ l ∧
      (∀ j ∈ D.active k, j ≠ j₁ → j ≠ j₂ → j ∈ l) ∧
      l.Pairwise (fun i j => ∀ x, 0 < h.realCharacter μ₁ x →
        0 < h.realCharacter (D.wall j).normal x → 0 < h.realCharacter (D.wall i).normal x) ∧
      CompletedGroup.projection k (D.wall j₂).label *
          CompletedGroup.projection k (D.wall j₁).label =
        CompletedGroup.projection k (D.wall j₁).label *
          (l.map fun j => CompletedGroup.projection k (D.wall j).label).prod *
          CompletedGroup.projection k (D.wall j₂).label) :
    D.Consistent :=
  D.consistent_iff.mpr fun k => by
    obtain ⟨l, hl, hj₁, hj₂, hact, hsort, hrel⟩ := hfac k
    exact hD.levelConsistent k hj₁ hj₂ hrel hl hact hsort

end Diagram

end Mei.DirectedDiagram
