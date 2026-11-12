/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Plane.Basic
public import Mei.Geometry.Convex.PolyhedralComplex.OfPolyhedron.Basic
public import TauCeti.Analysis.Convex.Recession.Basic
public import Mei.Geometry.Convex.Sweep.Face
public import Mei.LinearAlgebra.Plane

/-!
# Complexes with a line and with a ray at a real offset

In the plane `ℝ²` with the standard lattice `ℤ²`, consider

* the line `H = {y = c}`. Its only nonempty exposed face is itself, so its complex has the single
  cell `H` (`mem_cells_ofPolyhedron_lineAtHeight_iff`), and this cell has nonzero lineality
  (`lineal_recessionCone_lineAtHeight_ne_bot`);
* the ray `r = {(x, 0) | a ≤ x}` with endpoint `(a, 0)` for an arbitrary real `a`, for instance
  `a = √2`. Its nonempty exposed faces are `r` and `{(a, 0)}`, so its complex has these two cells
  (`mem_cells_ofPolyhedron_rightRay_iff`), and the ray has trivial lineality
  (`lineal_recessionCone_rightRay_eq_bot`).

Both are complexes of rational-normal polyhedra: the normals are coordinate functionals, while
the offset `a` of the ray is not required to be rational. They are the complexes
`FinitePolyhedralComplex.ofPolyhedron` of the line and of the ray.
-/

public section

open TauCeti (IsRationalNormalPolyhedron)

open Set

namespace Mei.FinitePolyhedralComplex.Examples

/-- The horizontal line `{y = c}` in the plane. -/
def lineAtHeight (c : ℝ) : Set (ℝ × ℝ) := {p | p.2 = c}

/-- The horizontal ray `{(x, 0) | a ≤ x}` with endpoint `(a, 0)`. -/
def rightRay (a : ℝ) : Set (ℝ × ℝ) := {p | p.2 = 0 ∧ a ≤ p.1}

/-- A point lies on the horizontal line `{y = c}` exactly when its second coordinate is `c`. -/
@[simp]
theorem mem_lineAtHeight {c : ℝ} {p : ℝ × ℝ} : p ∈ lineAtHeight c ↔ p.2 = c := Iff.rfl

/-- A point lies on the ray with endpoint `(a, 0)` exactly when its second coordinate is `0` and
its first coordinate is at least `a`. -/
@[simp]
theorem mem_rightRay {a : ℝ} {p : ℝ × ℝ} : p ∈ rightRay a ↔ p.2 = 0 ∧ a ≤ p.1 := Iff.rfl

end Mei.FinitePolyhedralComplex.Examples

namespace Mei.FinitePolyhedralComplex.Examples

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- A horizontal line is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_lineAtHeight (c : ℝ) :
    IsRationalNormalPolyhedron h (lineAtHeight c) := by
  convert Plane.isRationalNormalPolyhedron_setOf_snd_eq h c using 1
  ext p
  simp

/-- A horizontal ray with any real endpoint is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_rightRay (a : ℝ) :
    IsRationalNormalPolyhedron h (rightRay a) := by
  have h₁ := Plane.isRationalNormalPolyhedron_horizontalLine h
  have h₂ := TauCeti.isRationalNormalPolyhedron_setOf_le (h := h) (-axisRow false)
    (by simpa using (isRationalFunctional_axisRow h false).neg) (-a)
  convert h₁.inter h₂ using 1
  ext p
  simp [rightRay, and_comm, neg_le_neg_iff]

/-- The endpoint of a ray lies on it. -/
theorem endpoint_mem_rightRay (a : ℝ) : (a, (0 : ℝ)) ∈ rightRay a := ⟨rfl, le_rfl⟩

/-- The line has nonzero lineality: both directions along it preserve it. -/
@[simp]
theorem lineal_recessionCone_lineAtHeight_ne_bot (c : ℝ) :
    (recessionCone ℝ (lineAtHeight c)).lineal ≠ ⊥ := by
  intro hbot
  have hmem : ((1 : ℝ), (0 : ℝ)) ∈ (recessionCone ℝ (lineAtHeight c)).lineal := by
    rw [PointedCone.mem_lineal, mem_recessionCone, mem_recessionCone]
    constructor <;> intro x hx t _ <;> simpa [lineAtHeight] using hx
  rw [hbot, Submodule.mem_bot] at hmem
  exact one_ne_zero (congrArg Prod.fst hmem)

/-- The ray has trivial lineality: it is pointed. -/
@[simp]
theorem lineal_recessionCone_rightRay_eq_bot (a : ℝ) :
    (recessionCone ℝ (rightRay a)).lineal = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  obtain ⟨h₁, h₂⟩ := PointedCone.mem_lineal.mp hv
  rw [mem_recessionCone] at h₁ h₂
  have a₁ := h₁ (a, 0) (endpoint_mem_rightRay a) 1 zero_le_one
  have a₂ := h₂ (a, 0) (endpoint_mem_rightRay a) 1 zero_le_one
  simp only [rightRay, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, one_mul, zero_add, Prod.fst_neg, Prod.snd_neg] at a₁ a₂
  ext <;> simp <;> linarith [a₁.1, a₁.2, a₂.1, a₂.2]

/-- The only nonempty exposed face of a horizontal line is the line itself. -/
@[simp]
theorem isPolyhedralFace_lineAtHeight_iff (c : ℝ) (F : Set (ℝ × ℝ)) :
    IsPolyhedralFace (lineAtHeight c) F ↔ F = lineAtHeight c := by
  rw [isPolyhedralFace_iff]
  constructor
  · rintro ⟨⟨x, hxF⟩, hexp⟩
    obtain ⟨l, rfl⟩ := hexp ⟨x, hxF⟩
    obtain ⟨hx, hmax⟩ := hxF
    ext y
    refine Set.mem_sep_iff.trans ⟨fun hy => hy.1, fun hy => ⟨hy, fun z hz => ?_⟩⟩
    have hlin : ∀ {p q : ℝ × ℝ}, q.2 = p.2 → l q = l p + (q.1 - p.1) * l (1, 0) :=
      fun hpq => l.toLinearMap.apply_eq_of_snd_eq hpq
    have h10 : l (1, 0) = 0 :=
      l.toLinearMap.apply_one_zero_eq_zero fun y hy => hmax y (hy.trans hx)
    rw [hlin (hz.trans hx.symm), hlin (hy.trans hx.symm), h10]
    simp
  · rintro rfl
    exact ⟨⟨(0, c), rfl⟩, IsExposed.refl _⟩

/-- The ray with endpoint `(a, 0)` is the sweep of its endpoint along `(-1, 0)`. -/
theorem rightRay_eq_sweep (a : ℝ) :
    rightRay a = Set.sweep ℝ {((a : ℝ), (0 : ℝ))} (-1, 0) := by
  ext p
  simp only [mem_rightRay, Set.mem_sweep_iff_exists, mem_singleton_iff, exists_eq_left]
  constructor
  · rintro ⟨hp, hap⟩
    exact ⟨p.1 - a, sub_nonneg.mpr hap, Prod.ext (by simp) (by simp [hp])⟩
  · rintro ⟨t, ht, rfl⟩
    simpa using ht

/-- The nonempty exposed faces of the ray with endpoint `(a, 0)` are the ray and its endpoint.
For `a = √2` the endpoint has an irrational coordinate. -/
@[simp]
theorem isPolyhedralFace_rightRay_iff (a : ℝ) (F : Set (ℝ × ℝ)) :
    IsPolyhedralFace (rightRay a) F ↔ F = rightRay a ∨ F = {(a, 0)} := by
  have hn : ((-1 : ℝ), (0 : ℝ)) ∉ vectorSpan ℝ {((a : ℝ), (0 : ℝ))} := by
    simp [vectorSpan_singleton]
  have hpt : IsExposed ℝ (Set.sweep ℝ {((a : ℝ), (0 : ℝ))} (-1, 0)) {(a, 0)} :=
    (IsExposed.refl _).in_sweep_of_transverse hn
  rw [isPolyhedralFace_iff, rightRay_eq_sweep]
  constructor
  · rintro ⟨hne, hexp⟩
    obtain ⟨F₀, hF₀, hF₀exp, rfl | rfl⟩ := (Mei.Convex.isExposed_sweep_iff hn hne).mp hexp
    · exact Or.inr (hF₀.subset_singleton_iff.mp hF₀exp.subset)
    · exact Or.inl (by rw [hF₀.subset_singleton_iff.mp hF₀exp.subset])
  · rintro (rfl | rfl)
    · exact ⟨(singleton_nonempty _).mono (Set.subset_sweep (𝕜 := ℝ) _ _), IsExposed.refl _⟩
    · exact ⟨singleton_nonempty _, hpt⟩

/-- The complex of a horizontal line has the single cell `H`. -/
theorem mem_cells_ofPolyhedron_lineAtHeight_iff (c : ℝ) (F : Set (ℝ × ℝ)) :
    F ∈ (ofPolyhedron h (lineAtHeight c) (isRationalNormalPolyhedron_lineAtHeight h c)).cells
      ↔ F = lineAtHeight c := by
  simp

/-- The complex of the ray with endpoint `(a, 0)` has the two cells `r` and `{(a, 0)}`. -/
theorem mem_cells_ofPolyhedron_rightRay_iff (a : ℝ) (F : Set (ℝ × ℝ)) :
    F ∈ (ofPolyhedron h (rightRay a) (isRationalNormalPolyhedron_rightRay h a)).cells
      ↔ F = rightRay a ∨ F = {(a, 0)} := by
  simp

end Mei.FinitePolyhedralComplex.Examples
