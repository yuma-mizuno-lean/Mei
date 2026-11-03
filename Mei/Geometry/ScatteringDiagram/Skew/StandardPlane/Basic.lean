/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Examples
public import Mei.Geometry.ScatteringDiagram.Skew.LieAlgebra

/-!
# The standard plane with weighted positive degrees

On the lattice `ℤ²` with the skew form `{e₁, e₂} = 1` (the unimodular rank-two skew lattice
datum `unimodularRankTwo`), every pair `w = (w₁, w₂)` of positive integer weights defines
positive degrees: the allowed monoid is the first quadrant `ℕ²` and the degree of `(a, b)` is
`w₁ a + w₂ b`. A nonzero vector of the quadrant is a `PlaneDegree w`; it lies on the
*boundary* when a coordinate vanishes and in the *open quadrant* otherwise. Two plane degrees
`m, m'` are *ordered* when `{m, m'} ≥ 0` and form an *inversion* when `{m, m'} < 0`.

Weighted degrees are needed because rescaling the plane along two plane degrees `x, y`, the
change of basis `e₁ ↦ y`, `e₂ ↦ x`, carries the weights `(w₁, w₂)` to `(δ y, δ x)`.
-/

public section

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples

/-- The standard unimodular skew lattice datum on `ℤ²`. -/
abbrev E : SkewLatticeDatum (ℤ × ℤ) := unimodularRankTwo

/-- The lattice `ℤ²` of the standard plane, as the unfrozen lattice of its datum. -/
abbrev Γ : Type := E.unfrozen

/-- A pair of positive integer weights for the two coordinates. -/
structure Weight where
  /-- The weight of the first coordinate. -/
  fst : ℕ
  /-- The weight of the second coordinate. -/
  snd : ℕ
  fst_pos : 0 < fst
  snd_pos : 0 < snd

namespace Weight

/-- The weighted degree of a vector of the plane. -/
def degreeHom (w : Weight) : Γ →+ ℤ where
  toFun v := w.fst * v.1.1 + w.snd * v.1.2
  map_zero' := by simp
  map_add' v v' := by
    simp only [AddMemClass.coe_add, Prod.fst_add, Prod.snd_add]
    ring

@[simp]
theorem degreeHom_apply (w : Weight) (v : Γ) : w.degreeHom v = w.fst * v.1.1 + w.snd * v.1.2 :=
  (rfl)

end Weight

/-- The first quadrant `ℕ²` of the plane with the weighted degree: nonzero vectors have
positive degree and only finitely many have degree at most any cutoff. -/
def plane (w : Weight) : PositiveDegrees Γ where
  monoid :=
    { carrier := {v | 0 ≤ v.1.1 ∧ 0 ≤ v.1.2}
      add_mem' := fun {v v'} hv hv' => ⟨add_nonneg hv.1 hv'.1, add_nonneg hv.2 hv'.2⟩
      zero_mem' := ⟨le_rfl, le_rfl⟩ }
  degree := w.degreeHom
  degree_pos {v} hv hne := by
    have h1 : (0 : ℤ) < w.fst := by exact_mod_cast w.fst_pos
    have h2 : (0 : ℤ) < w.snd := by exact_mod_cast w.snd_pos
    have : v.1 ≠ 0 := fun h => hne (Subtype.ext h)
    have hne' : v.1.1 ≠ 0 ∨ v.1.2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact this (Prod.ext hc.1 hc.2)
    rw [Weight.degreeHom_apply]
    rcases hne' with h | h
    · have := lt_of_le_of_ne hv.1 (Ne.symm h)
      nlinarith [hv.2]
    · have := lt_of_le_of_ne hv.2 (Ne.symm h)
      nlinarith [hv.1]
  finite_le k := by
    have hfin : Set.Finite {v : ℤ × ℤ | 0 ≤ v.1 ∧ v.1 ≤ k ∧ 0 ≤ v.2 ∧ v.2 ≤ k} :=
      (Set.finite_Icc ((0 : ℤ), (0 : ℤ)) ((k : ℤ), (k : ℤ))).subset fun v hv =>
        ⟨⟨hv.1, hv.2.2.1⟩, hv.2.1, hv.2.2.2⟩
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    rintro v ⟨⟨h1, h2⟩, h3⟩
    have hw1 := w.fst_pos
    have hw2 := w.snd_pos
    simp only [Weight.degreeHom_apply] at h3
    refine ⟨h1, ?_, h2, ?_⟩ <;> nlinarith

@[simp]
theorem mem_plane_monoid {w : Weight} {v : Γ} :
    v ∈ (plane w).monoid ↔ 0 ≤ v.1.1 ∧ 0 ≤ v.1.2 := Iff.rfl

@[simp]
theorem plane_degree {w : Weight} (v : Γ) :
    (plane w).degree v = w.fst * v.1.1 + w.snd * v.1.2 := (rfl)

/-- The skew form of the plane in coordinates. -/
theorem form_apply (v v' : Γ) :
    E.form v v' = ((v.1.1 * v'.1.2 - v.1.2 * v'.1.1 : ℤ) : ℚ) := by
  rw [show E.form = rankTwoForm from unimodularRankTwo_form]
  exact rankTwoForm_apply v.1 v'.1

/-- The skew form of the plane with rational coefficients, in coordinates. -/
theorem coefficientForm_apply (v v' : Γ) :
    E.coefficientForm ℚ v v' = ((v.1.1 * v'.1.2 - v.1.2 * v'.1.1 : ℤ) : ℚ) := by
  rw [SkewLatticeDatum.coefficientForm_apply, form_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

/-- The nonzero degrees of the plane for the weight `w`. -/
@[ext]
structure PlaneDegree (w : Weight) where
  /-- The underlying vector of the plane. -/
  vec : Γ
  /-- The vector lies in the first quadrant. -/
  mem : vec ∈ (plane w).monoid
  /-- The vector is nonzero. -/
  ne_zero : vec ≠ 0

namespace PlaneDegree

variable {w : Weight}

/-- The first coordinate of a plane degree. -/
abbrev fst (m : PlaneDegree w) : ℤ := m.vec.1.1

/-- The second coordinate of a plane degree. -/
abbrev snd (m : PlaneDegree w) : ℤ := m.vec.1.2

theorem fst_nonneg (m : PlaneDegree w) : 0 ≤ m.fst := m.mem.1

theorem snd_nonneg (m : PlaneDegree w) : 0 ≤ m.snd := m.mem.2

theorem fst_ne_zero_or (m : PlaneDegree w) : m.fst ≠ 0 ∨ m.snd ≠ 0 := by
  by_contra hc
  push Not at hc
  exact m.ne_zero (Subtype.ext (Prod.ext hc.1 hc.2))

/-- The weighted degree of a nonzero plane degree, as a natural number. -/
def deg (m : PlaneDegree w) : ℕ := ((plane w).degree m.vec).toNat

theorem deg_eq_degree (m : PlaneDegree w) : (m.deg : ℤ) = (plane w).degree m.vec :=
  Int.toNat_of_nonneg ((plane w).degree_nonneg m.mem)

theorem deg_eq (m : PlaneDegree w) : (m.deg : ℤ) = w.fst * m.fst + w.snd * m.snd := by
  rw [deg_eq_degree, plane_degree]

theorem deg_pos (m : PlaneDegree w) : 0 < m.deg := by
  have := (plane w).degree_pos m.mem m.ne_zero
  have := m.deg_eq_degree
  omega

/-- Plane degrees on the boundary of the quadrant: those with a vanishing coordinate. -/
def Boundary (m : PlaneDegree w) : Prop := m.fst = 0 ∨ m.snd = 0

theorem boundary_iff (m : PlaneDegree w) : m.Boundary ↔ m.fst = 0 ∨ m.snd = 0 := Iff.rfl

instance : DecidablePred (Boundary (w := w)) := fun m =>
  inferInstanceAs (Decidable (m.fst = 0 ∨ m.snd = 0))

/-- A pair of plane degrees is an *inversion* when its skew pairing `{m, m'}` is negative: it is
out of order and needs an exchange. -/
def Inverted (m m' : PlaneDegree w) : Prop := E.coefficientForm ℚ m.vec m'.vec < 0

private theorem mem_unfrozen (v : ℤ × ℤ) : v ∈ E.unfrozen := by
  simp only [E, unimodularRankTwo_unfrozen]
  exact Submodule.mem_top

/-- The first basis vector of the plane. -/
def e₁ (w : Weight) : PlaneDegree w where
  vec := ⟨(1, 0), mem_unfrozen _⟩
  mem := ⟨by simp, le_rfl⟩
  ne_zero h := by simpa using congrArg (fun v : Γ => v.1.1) h

/-- The second basis vector of the plane. -/
def e₂ (w : Weight) : PlaneDegree w where
  vec := ⟨(0, 1), mem_unfrozen _⟩
  mem := ⟨le_rfl, by simp⟩
  ne_zero h := by simpa using congrArg (fun v : Γ => v.1.2) h

@[simp] theorem e₁_fst : (e₁ w).fst = 1 := (rfl)
@[simp] theorem e₁_snd : (e₁ w).snd = 0 := (rfl)
@[simp] theorem e₂_fst : (e₂ w).fst = 0 := (rfl)
@[simp] theorem e₂_snd : (e₂ w).snd = 1 := (rfl)

/-- The integer `{y, x} = y₁ x₂ - y₂ x₁` of a pair of plane degrees. -/
def det (x y : PlaneDegree w) : ℤ := y.fst * x.snd - y.snd * x.fst

theorem det_eq (x y : PlaneDegree w) : x.det y = y.fst * x.snd - y.snd * x.fst := (rfl)

@[simp]
theorem deg_e₁ (w : Weight) : (e₁ w).deg = w.fst := by
  apply Nat.cast_injective (R := ℤ)
  rw [deg_eq]
  simp

@[simp]
theorem deg_e₂ (w : Weight) : (e₂ w).deg = w.snd := by
  apply Nat.cast_injective (R := ℤ)
  rw [deg_eq]
  simp

theorem inverted_def (m m' : PlaneDegree w) :
    Inverted m m' ↔ E.coefficientForm ℚ m.vec m'.vec < 0 := Iff.rfl

theorem inverted_iff (m m' : PlaneDegree w) : Inverted m m' ↔ m.fst * m'.snd < m.snd * m'.fst := by
  rw [Inverted, coefficientForm_apply]
  have : ((m.fst * m'.snd - m.snd * m'.fst : ℤ) : ℚ) < 0 ↔ m.fst * m'.snd - m.snd * m'.fst < 0 :=
    Int.cast_lt_zero
  rw [this]
  omega

theorem inverted_iff_det_pos (x y : PlaneDegree w) : Inverted x y ↔ 0 < x.det y := by
  rw [inverted_iff, det_eq]
  constructor <;> intro h <;> nlinarith

theorem form_det (x y : PlaneDegree w) : E.form y.vec x.vec = (x.det y : ℚ) := by
  rw [form_apply, det_eq]

theorem form_neg_det (x y : PlaneDegree w) : E.form ↑(-x.vec) y.vec = (x.det y : ℚ) := by
  rw [NegMemClass.coe_neg, map_neg, LinearMap.neg_apply, E.form_swap, neg_neg]
  exact form_det x y

/-- If `{y, x} > 0`, then `y` has a positive first and `x` a positive second coordinate. -/
theorem one_le_fst_and_one_le_snd {x y : PlaneDegree w} (h : 0 < x.det y) :
    1 ≤ y.fst ∧ 1 ≤ x.snd := by
  rw [det_eq] at h
  have := y.fst_nonneg
  have := x.snd_nonneg
  have := x.fst_nonneg
  have := y.snd_nonneg
  constructor
  · by_contra hc
    have h0 : y.fst = 0 := by omega
    rw [h0] at h
    nlinarith
  · by_contra hc
    have h0 : x.snd = 0 := by omega
    rw [h0] at h
    nlinarith

theorem coefficientForm_det (x y : PlaneDegree w) :
    E.coefficientForm ℚ y.vec x.vec = (x.det y : ℚ) := by
  rw [coefficientForm_apply, det_eq]

end PlaneDegree

end Mei.StandardPlane
