/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Basic
public import Mei.Algebra.Lie.Skew.Dilogarithm

/-!
# Unit factors of the standard plane

The dilogarithm label `Ψ[m]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jm} / j²)` of a nonzero plane
degree `m` and a rational exponent `c` is `dilogPow m c`. Its *unit factor*
`unitFactor m = Ψ[m]^{κ(m)}` uses the ray index `κ(m) = 1 / gcd m` of `ℤ²`, so a normalized
positive factor `Ψ[m]^{sκ(m)}` with `s ∈ ℕ` is the `s`-th power of a unit factor. Labels of
one degree multiply by adding exponents, and a label of degree `m` lies in the degree
filtration of order `deg m`.
-/

public section

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples PowerSeries

local notation "β" => E.coefficientForm ℚ
local notation "hβ" => E.isAlt_coefficientForm ℚ

/-- The completed label group of the plane with weight `w`: the completed BCH group of the
positive skew Lie algebra. -/
abbrev Label (w : Weight) : Type :=
  (plane w).completedBCHGroup (SkewLieAlgebra.positiveGrading β hβ (plane w))

/-- The ray index of `ℤ²` at a vector: the reciprocal of its gcd. -/
abbrev rayIndex (m : Γ) : ℚ := E.sublattice.toAddSubgroup.rayIndex m

variable {w : Weight}

theorem PlaneDegree.rayIndex_pos (m : PlaneDegree w) : 0 < rayIndex m.vec :=
  AddSubgroup.rayIndex_pos (H := E.sublattice.toAddSubgroup) fun h => m.ne_zero (Subtype.ext h)

/-- The dilogarithm label `Ψ[m]^c` of a nonzero plane degree. -/
def dilogPow (m : PlaneDegree w) (c : ℚ) : Label w :=
  SkewLieAlgebra.rayExp β hβ m.mem m.ne_zero (c • negDilogNeg ℚ)

/-- Unfolds `dilogPow`, which holds by definition. -/
theorem dilogPow_def (m : PlaneDegree w) (c : ℚ) :
    dilogPow m c = SkewLieAlgebra.rayExp β hβ m.mem m.ne_zero (c • negDilogNeg ℚ) := (rfl)

theorem dilogPow_add (m : PlaneDegree w) (c c' : ℚ) :
    dilogPow m (c + c') = dilogPow m c * dilogPow m c' := by
  rw [dilogPow, dilogPow, dilogPow, add_smul, SkewLieAlgebra.rayExp_add]

@[simp]
theorem dilogPow_zero (m : PlaneDegree w) : dilogPow m 0 = 1 := by
  rw [dilogPow, zero_smul, SkewLieAlgebra.rayExp_zero]

theorem dilogPow_neg (m : PlaneDegree w) (c : ℚ) : dilogPow m (-c) = (dilogPow m c)⁻¹ := by
  rw [dilogPow, dilogPow, neg_smul, SkewLieAlgebra.rayExp_neg]

theorem dilogPow_intCast_mul (m : PlaneDegree w) (s : ℤ) (c : ℚ) :
    dilogPow m (s * c) = dilogPow m c ^ s := by
  rw [dilogPow, dilogPow, ← SkewLieAlgebra.rayExp_zsmul, mul_smul, Int.cast_smul_eq_zsmul]

theorem dilogPow_natCast_mul (m : PlaneDegree w) (s : ℕ) (c : ℚ) :
    dilogPow m (s * c) = dilogPow m c ^ s := by
  simpa using dilogPow_intCast_mul m (s : ℤ) c

/-- The unit factor `Ψ[m]^{κ(m)}` of a nonzero plane degree. -/
def unitFactor (m : PlaneDegree w) : Label w := dilogPow m (rayIndex m.vec)

/-- Unfolds `unitFactor`, which holds by definition. -/
theorem unitFactor_def (m : PlaneDegree w) : unitFactor m = dilogPow m (rayIndex m.vec) := (rfl)

/-- The unit factor of a plane degree of ray index one is the dilogarithm element `Ψ[m]`. -/
theorem unitFactor_eq_dilogElement (m : PlaneDegree w) (h : rayIndex m.vec = 1) :
    unitFactor m = SkewLieAlgebra.dilogElement β hβ m.mem m.ne_zero := by
  rw [unitFactor_def, h, dilogPow_def, one_smul, SkewLieAlgebra.dilogElement_def]

/-- A vector of `ℤ²` that pairs to one with some vector has ray index one. -/
theorem rayIndex_eq_one_of_form_eq_one {n : Γ} (a : Γ) (h : E.form a n = 1) :
    rayIndex n = 1 :=
  E.rayIndex_eq_one_of_form_eq_one n.property (by simp [E]) h

theorem rayIndex_e₁ : rayIndex (PlaneDegree.e₁ w).vec = 1 :=
  rayIndex_eq_one_of_form_eq_one (-(PlaneDegree.e₂ w).vec) (by
    rw [PlaneDegree.form_neg_det]
    simp [PlaneDegree.det_eq])

theorem rayIndex_e₂ : rayIndex (PlaneDegree.e₂ w).vec = 1 :=
  rayIndex_eq_one_of_form_eq_one (PlaneDegree.e₁ w).vec (by
    rw [PlaneDegree.form_det]
    simp [PlaneDegree.det_eq])

/-- The ray index of a nonzero vector of `ℤ²` is the reciprocal of the gcd of its coordinates. -/
theorem rayIndex_eq_inv_gcd {m : Γ} (hm : m ≠ 0) :
    rayIndex m = ((Int.gcd m.1.1 m.1.2 : ℕ) : ℚ)⁻¹ := by
  have hne : m.1.1 ≠ 0 ∨ m.1.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (Subtype.ext (Prod.ext h.1 h.2))
  have hg : 0 < Int.gcd m.1.1 m.1.2 := Int.gcd_pos_iff.mpr hne
  obtain ⟨a, ha⟩ := Int.gcd_dvd_left (a := m.1.1) (b := m.1.2)
  obtain ⟨b, hb⟩ := Int.gcd_dvd_right (a := m.1.1) (b := m.1.2)
  set g := Int.gcd m.1.1 m.1.2 with hgdef
  have hcop : Int.gcd a b = 1 := by
    have h := Int.gcd_mul_left (g : ℤ) a b
    rw [← ha, ← hb, ← hgdef] at h
    simp only [Int.natAbs_natCast] at h
    nlinarith
  let m₀ : Γ := ⟨(a, b), mem_unfrozen _⟩
  have hm₀ : m = (g : ℤ) • m₀ :=
    Subtype.ext (Prod.ext (by simpa [m₀] using ha) (by simpa [m₀] using hb))
  have hbez : Int.gcdA a b * a + Int.gcdB a b * b = 1 := by
    have := Int.gcd_eq_gcd_ab a b
    rw [hcop] at this
    push_cast at this
    linarith
  have h1 : rayIndex m₀ = 1 := by
    refine rayIndex_eq_one_of_form_eq_one (⟨(Int.gcdB a b, -Int.gcdA a b), mem_unfrozen _⟩ : Γ) ?_
    rw [form_apply]
    simp only [m₀]
    exact_mod_cast (by linarith : Int.gcdB a b * b - -Int.gcdA a b * a = 1)
  have h2 : rayIndex m = rayIndex m₀ / ((g : ℤ) : ℚ) := by
    rw [hm₀]
    unfold rayIndex
    rw [Submodule.coe_smul]
    exact AddSubgroup.rayIndex_zsmul _ (by exact_mod_cast hg) _
  rw [h2, h1]
  simp

/-- A ray label of a plane degree lies in the degree filtration of its order. -/
theorem dilogPow_mem_degreeFiltration (m : PlaneDegree w) (c : ℚ) :
    dilogPow m c ∈ CompletedGroup.degreeFiltration
      ((plane w).groupTower (SkewLieAlgebra.positiveGrading β hβ (plane w))) m.deg := by
  have h := m.deg_pos
  obtain ⟨a, ha⟩ : ∃ a, m.deg = a + 1 := ⟨m.deg - 1, by omega⟩
  rw [ha]
  refine SkewLieAlgebra.rayExp_mem_degreeFiltration β hβ m.mem m.ne_zero _ ?_
  have h2 := m.deg_eq_degree
  rw [ha] at h2
  omega

theorem unitFactor_mem_degreeFiltration (m : PlaneDegree w) :
    unitFactor m ∈ CompletedGroup.degreeFiltration
      ((plane w).groupTower (SkewLieAlgebra.positiveGrading β hβ (plane w))) m.deg :=
  dilogPow_mem_degreeFiltration m _

end Mei.StandardPlane
