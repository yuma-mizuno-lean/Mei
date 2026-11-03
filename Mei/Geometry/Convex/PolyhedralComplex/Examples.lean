/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CoordinateAxes
public import Mei.Geometry.Convex.Polyhedron.Rational.Cone
public import Mei.Geometry.Convex.Recession
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Complexes with lineality and with an irrational vertex

Two small families of finite polyhedral complexes in the plane `ℝ × ℝ` with its standard
lattice show how far the definition of `FinitePolyhedralComplex` reaches beyond the conical
complexes cut out by linear arrangements.

* `horizontalLineComplex h c` has the single cell `horizontalLine c = {p | p.2 = c}`. An affine
  line has no proper nonempty exposed face (`isExposed_horizontalLine_iff`), so this one cell is
  closed under faces. The cell is unbounded in both directions, so its lineality space is
  nonzero (`lineal_recessionCone_horizontalLine_ne_bot`), and for `c ≠ 0` it is not a cone
  (`not_isConical_horizontalLineComplex`).
* `rayComplex h a` has the two cells `horizontalRay a = {p | p.2 = 0 ∧ a ≤ p.1}` and `{(a, 0)}`:
  a ray and its vertex (`isExposed_horizontalRay_iff`). Offsets of rational-normal polyhedra are
  arbitrary reals, so `a` may be irrational, for instance `√2`
  (`exists_singleton_mem_rayComplex_cells_irrational`). Its cells have trivial lineality
  (`lineal_recessionCone_eq_bot_of_mem_rayComplex_cells`).
-/

public section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

/-- The horizontal line `{p | p.2 = c}` in the plane. -/
def horizontalLine (c : ℝ) : Set (ℝ × ℝ) := {p | p.2 = c}

/-- A point lies on the horizontal line at height `c` when its second coordinate is `c`. -/
@[simp]
theorem mem_horizontalLine {c : ℝ} {p : ℝ × ℝ} : p ∈ horizontalLine c ↔ p.2 = c := (Iff.rfl)

/-- The closed horizontal ray `{p | p.2 = 0 ∧ a ≤ p.1}` with vertex `(a, 0)` in direction
`(1, 0)`. -/
def horizontalRay (a : ℝ) : Set (ℝ × ℝ) := {p | p.2 = 0 ∧ a ≤ p.1}

/-- A point lies on the ray from `(a, 0)` when it is on the axis at or to the right of `a`. -/
@[simp]
theorem mem_horizontalRay {a : ℝ} {p : ℝ × ℝ} : p ∈ horizontalRay a ↔ p.2 = 0 ∧ a ≤ p.1 :=
  (Iff.rfl)

/-- A continuous linear functional on the plane is determined by its values on the basis. -/
private theorem apply_eq (l : (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    l p = p.1 * l (1, 0) + p.2 * l (0, 1) := by
  have hp : p = p.1 • ((1, 0) : ℝ × ℝ) + p.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  calc l p = l (p.1 • ((1, 0) : ℝ × ℝ) + p.2 • ((0, 1) : ℝ × ℝ)) := congrArg l hp
    _ = _ := by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- An affine line has no proper nonempty exposed face. -/
theorem isExposed_horizontalLine_iff {c : ℝ} {F : Set (ℝ × ℝ)} :
    IsExposed ℝ (horizontalLine c) F ↔ F = ∅ ∨ F = horizontalLine c := by
  refine ⟨fun hF => ?_, ?_⟩
  · rcases F.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact Or.inl rfl
    right
    obtain ⟨l, hl⟩ := hF ⟨x₀, hx₀⟩
    have hx₀' := hl ▸ hx₀
    -- the reflection of a point of the line through `x₀` is again on the line
    have hconst : ∀ y ∈ horizontalLine c, l y = l x₀ := by
      intro y hy
      have hx₀c : x₀.2 = c := hF.subset hx₀
      have h₁ := hx₀'.2 y hy
      have h₂ := hx₀'.2 ((2 : ℝ) • x₀ - y) (by simp [hx₀c, mem_horizontalLine.mp hy]; ring)
      rw [map_sub, map_smul, smul_eq_mul] at h₂
      linarith
    refine Set.Subset.antisymm hF.subset fun p hp => ?_
    rw [hl]
    exact ⟨hp, fun z hz => by rw [hconst z hz, hconst p hp]⟩
  · rintro (rfl | rfl)
    · exact isExposed_empty
    · exact IsExposed.refl _

/-- The faces of a ray are the empty face, the ray itself and its vertex. -/
theorem isExposed_horizontalRay_iff {a : ℝ} {F : Set (ℝ × ℝ)} :
    IsExposed ℝ (horizontalRay a) F ↔ F = ∅ ∨ F = horizontalRay a ∨ F = {(a, 0)} := by
  refine ⟨fun hF => ?_, ?_⟩
  · rcases F.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact Or.inl rfl
    right
    obtain ⟨l, hl⟩ := hF ⟨x₀, hx₀⟩
    have hx₀' := hl ▸ hx₀
    have hlp : ∀ p ∈ horizontalRay a, l p = p.1 * l (1, 0) := by
      intro p hp
      rw [apply_eq l p, (mem_horizontalRay.mp hp).1, zero_mul, add_zero]
    have hstep : (x₀.1 + 1, 0) ∈ horizontalRay a := by
      simpa using (mem_horizontalRay.mp hx₀'.1).2.trans (le_add_of_nonneg_right zero_le_one)
    have hle := hx₀'.2 _ hstep
    rw [hlp _ hstep, hlp _ hx₀'.1] at hle
    have hneg : l (1, 0) ≤ 0 := by simp only at hle; nlinarith
    rcases hneg.lt_or_eq with hlt | h0
    · -- a strictly decreasing functional is maximal exactly at the vertex
      right
      rw [hl]
      ext p
      refine ⟨fun ⟨hp, hmax⟩ => ?_, ?_⟩
      · have hv := hmax (a, 0) (by simp)
        rw [hlp _ hp, hlp (a, 0) (by simp)] at hv
        have hp1 : p.1 ≤ a := by simp only at hv; nlinarith
        exact Prod.ext (le_antisymm hp1 (mem_horizontalRay.mp hp).2) (mem_horizontalRay.mp hp).1
      · rintro rfl
        refine ⟨by simp, fun y hy => ?_⟩
        rw [hlp _ hy, hlp (a, 0) (by simp)]
        nlinarith [(mem_horizontalRay.mp hy).2]
    · -- a functional vanishing on the axis does not cut the ray
      left
      refine Set.Subset.antisymm hF.subset fun p hp => ?_
      rw [hl]
      exact ⟨hp, fun z hz => by rw [hlp z hz, hlp p hp, h0, mul_zero, mul_zero]⟩
  · rintro (rfl | rfl | rfl)
    · exact isExposed_empty
    · exact IsExposed.refl _
    · intro _
      refine ⟨-ContinuousLinearMap.fst ℝ ℝ ℝ, ?_⟩
      ext p
      refine ⟨?_, fun ⟨hp, hmax⟩ => ?_⟩
      · rintro rfl
        exact ⟨by simp, fun y hy => by simpa using (mem_horizontalRay.mp hy).2⟩
      · have hv := hmax (a, 0) (by simp)
        simp only [neg_apply, ContinuousLinearMap.coe_fst'] at hv
        exact Prod.ext (le_antisymm (by linarith) (mem_horizontalRay.mp hp).2)
          (mem_horizontalRay.mp hp).1

section Complexes

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The affine function `p ↦ f p + c` on the plane. -/
private def affineRow (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ) : (ℝ × ℝ) →ᴬ[ℝ] ℝ :=
  f.toContinuousAffineMap + ContinuousAffineMap.const ℝ _ c

private theorem affineRow_apply (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ) (p : ℝ × ℝ) :
    affineRow f c p = f p + c := (rfl)

private theorem linear_affineRow (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ) :
    (affineRow f c).toAffineMap.linear = f.toLinearMap := by
  refine LinearMap.ext fun p => ?_
  simpa [affineRow_apply] using AffineMap.linear_apply_vsub (affineRow f c).toAffineMap p 0

/-- Finitely many inequalities `f j p + c j ≤ 0` with rational `f j` define a rational-normal
polyhedron. -/
private theorem isRationalNormalPolyhedron_setOf_forall_affineRow {ι : Type*} [Finite ι]
    (f : ι → (ℝ × ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap) :
    IsRationalNormalPolyhedron h {p | ∀ j, f j p + c j ≤ 0} := by
  simpa only [affineRow_apply] using isRationalNormalPolyhedron_setOf_forall (h := h)
    (fun j => affineRow (f j) (c j)) (fun j => by rw [linear_affineRow]; exact hf j)

private theorem isRationalNormalPolyhedron_horizontalLine (c : ℝ) :
    IsRationalNormalPolyhedron h (horizontalLine c) := by
  have hrow := isRationalFunctional_axisRow h true
  convert isRationalNormalPolyhedron_setOf_forall_affineRow h
    (fun b : Bool => cond b (axisRow true) (-axisRow true)) (fun b => cond b (-c) c)
    (fun b => by cases b; exacts [by simpa using hrow.neg, by simpa using hrow]) using 1
  ext p
  simp only [horizontalLine, mem_ofPred_eq, Bool.forall_bool, Bool.cond_false, Bool.cond_true,
    neg_apply, axisRow_true_apply]
  constructor
  · intro hp
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    linarith

private theorem isRationalNormalPolyhedron_horizontalRay (a : ℝ) :
    IsRationalNormalPolyhedron h (horizontalRay a) := by
  have hrow := fun j => isRationalFunctional_axisRow h j
  convert isRationalNormalPolyhedron_setOf_forall_affineRow h
    ![axisRow true, -axisRow true, -axisRow false] ![0, 0, a] (fun j => by
      fin_cases j
      · simpa using hrow true
      · simpa using (hrow true).neg
      · simpa using (hrow false).neg) using 1
  ext p
  simp only [horizontalRay, mem_ofPred_eq, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, neg_apply, axisRow_true_apply,
    axisRow_false_apply]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨by linarith, by linarith⟩

/-- The complex whose only cell is the horizontal line at height `c`. The cell has nonzero
lineality (`lineal_recessionCone_horizontalLine_ne_bot`). -/
def horizontalLineComplex (c : ℝ) : FinitePolyhedralComplex h where
  cells := {horizontalLine c}
  nonempty P hP := by
    obtain rfl := Finset.mem_singleton.mp hP
    exact ⟨(0, c), rfl⟩
  rational P hP := by
    obtain rfl := Finset.mem_singleton.mp hP
    exact isRationalNormalPolyhedron_horizontalLine h c
  face_closed P hP F hF := by
    obtain rfl := Finset.mem_singleton.mp hP
    obtain ⟨hFne, hFexp⟩ := isPolyhedralFace_iff.mp hF
    rcases isExposed_horizontalLine_iff.mp hFexp with rfl | rfl
    · exact absurd hFne (by simp)
    · exact hP
  inter_face P hP Q hQ _ := by
    obtain rfl := Finset.mem_singleton.mp hP
    obtain rfl := Finset.mem_singleton.mp hQ
    rw [inter_self]
    exact IsExposed.refl _

/-- The cells of `horizontalLineComplex h c` are exactly the line. -/
@[simp]
theorem mem_horizontalLineComplex_cells {c : ℝ} {P : Set (ℝ × ℝ)} :
    P ∈ (horizontalLineComplex h c).cells ↔ P = horizontalLine c :=
  Finset.mem_singleton

/-- The support of `horizontalLineComplex h c` is the line itself. -/
@[simp]
theorem support_horizontalLineComplex (c : ℝ) :
    (horizontalLineComplex h c).support = horizontalLine c := by
  ext p
  simp [mem_support]

/-- A horizontal line that misses the origin is not a cone, so its complex is not conical. -/
theorem not_isConical_horizontalLineComplex {c : ℝ} (hc : c ≠ 0) :
    ¬ (horizontalLineComplex h c).IsConical := by
  rintro hcon
  obtain ⟨σ, hσ⟩ := (isConical_iff _).mp hcon (horizontalLine c)
    ((mem_horizontalLineComplex_cells h).mpr rfl)
  have h0 : (0 : ℝ × ℝ) ∈ horizontalLine c := hσ ▸ σ.zero_mem
  exact hc (mem_horizontalLine.mp h0).symm

/-- The horizontal line has nonzero lineality: it is preserved by translations in both
directions along itself. -/
theorem lineal_recessionCone_horizontalLine_ne_bot (c : ℝ) :
    (recessionCone (horizontalLine c)).lineal ≠ ⊥ := by
  intro hbot
  have hmem : ((1, 0) : ℝ × ℝ) ∈ (recessionCone (horizontalLine c)).lineal := by
    rw [PointedCone.mem_lineal]
    constructor <;> (rw [mem_recessionCone]; intro x hx t _; simpa using hx)
  rw [hbot] at hmem
  simp at hmem

open Classical in
/-- The complex consisting of the ray from `(a, 0)` in direction `(1, 0)` and its vertex.
The vertex `a` is an arbitrary real number. -/
noncomputable def rayComplex (a : ℝ) : FinitePolyhedralComplex h where
  cells := {horizontalRay a, {(a, 0)}}
  nonempty P hP := by
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact ⟨(a, 0), by simp⟩
    · obtain rfl := Finset.mem_singleton.mp hP
      exact singleton_nonempty _
  rational P hP := by
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact isRationalNormalPolyhedron_horizontalRay h a
    · obtain rfl := Finset.mem_singleton.mp hP
      exact isRationalNormalPolyhedron_singleton h _
  face_closed P hP F hF := by
    rcases Finset.mem_insert.mp hP with rfl | hP
    · obtain ⟨hFne, hFexp⟩ := isPolyhedralFace_iff.mp hF
      rcases isExposed_horizontalRay_iff.mp hFexp with rfl | rfl | rfl
      · exact absurd hFne (by simp)
      · exact hP
      · simp
    · obtain rfl := Finset.mem_singleton.mp hP
      obtain ⟨hFne, hFexp⟩ := isPolyhedralFace_iff.mp hF
      rw [hFne.subset_singleton_iff.mp hFexp.subset]
      simp
  inter_face P hP Q hQ hne := by
    rcases Finset.mem_insert.mp hP with rfl | hP <;> rcases Finset.mem_insert.mp hQ with rfl | hQ
    · rw [inter_self]
      exact IsExposed.refl _
    · obtain rfl := Finset.mem_singleton.mp hQ
      rw [inter_eq_right.mpr (singleton_subset_iff.mpr (by simp))]
      exact isExposed_horizontalRay_iff.mpr (Or.inr (Or.inr rfl))
    · obtain rfl := Finset.mem_singleton.mp hP
      rw [inter_eq_left.mpr (singleton_subset_iff.mpr (by simp))]
      exact IsExposed.refl _
    · obtain rfl := Finset.mem_singleton.mp hP
      obtain rfl := Finset.mem_singleton.mp hQ
      rw [inter_self]
      exact IsExposed.refl _

/-- The cells of `rayComplex h a` are the ray and its vertex. -/
@[simp]
theorem mem_rayComplex_cells {a : ℝ} {P : Set (ℝ × ℝ)} :
    P ∈ (rayComplex h a).cells ↔ P = horizontalRay a ∨ P = {(a, 0)} := by
  simp [rayComplex]

/-- The support of `rayComplex h a` is the ray. -/
@[simp]
theorem support_rayComplex (a : ℝ) : (rayComplex h a).support = horizontalRay a := by
  ext p
  simp only [mem_support, mem_rayComplex_cells]
  constructor
  · rintro ⟨P, rfl | rfl, hp⟩
    · exact hp
    · obtain rfl := hp
      simp
  · exact fun hp => ⟨_, Or.inl rfl, hp⟩

/-- Every cell of `rayComplex h a` has trivial lineality: the ray and its vertex contain no
line. -/
theorem lineal_recessionCone_eq_bot_of_mem_rayComplex_cells {a : ℝ} {P : Set (ℝ × ℝ)}
    (hP : P ∈ (rayComplex h a).cells) : (recessionCone P).lineal = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [PointedCone.mem_lineal, mem_recessionCone, mem_recessionCone] at hv
  obtain ⟨hv₁, hv₂⟩ := hv
  rcases (mem_rayComplex_cells h).mp hP with rfl | rfl
  · have h₁ := hv₁ (a, 0) (by simp) 1 zero_le_one
    have h₂ := hv₂ (a, 0) (by simp) 1 zero_le_one
    simp only [mem_horizontalRay, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst,
      Prod.snd_neg, Prod.fst_neg, smul_eq_mul] at h₁ h₂
    exact Prod.ext (by rw [Prod.fst_zero]; linarith [h₁.2, h₂.2])
      (by rw [Prod.snd_zero]; linarith [h₁.1])
  · have h₁ := hv₁ (a, 0) rfl 1 zero_le_one
    simpa using h₁

/-- The vertex of `rayComplex h √2` is a zero-dimensional cell with an irrational coordinate,
so it is not a rational point of the plane. -/
theorem exists_singleton_mem_rayComplex_cells_irrational :
    ∃ x : ℝ × ℝ, {x} ∈ (rayComplex h (√2)).cells ∧ Irrational x.1 :=
  ⟨(√2, 0), (mem_rayComplex_cells h).mpr (Or.inr rfl), irrational_sqrt_two⟩

end Complexes

end Mei.FinitePolyhedralComplex
