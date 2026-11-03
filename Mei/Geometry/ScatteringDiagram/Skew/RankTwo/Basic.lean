/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Integrality
public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Ordering

/-!
# Dilogarithm powers of a skew lattice datum

For a skew lattice datum `D` with positive degrees `d` on `D.unfrozen`, a nonzero allowed
degree `n` and a rational exponent `c`, `D.dilogPow d n c` is the label
`Ψ[n]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` of the completed skew group. Its *unit factor*
`D.unitFactor d n = Ψ[n]^{κ(n)}` uses the ray index `κ(n)` of `N°`, so the normalized positive
factors `Ψ[n]^{sκ(n)}` with `s ∈ ℕ` are the powers of unit factors
(`dilogPow_intCast_mul_rayIndex`). Labels of degree above a cutoff project to the identity at
that cutoff (`projection_prod_dilogPow_filter`), and a product of normalized positive factors is
a product of unit factors (`prod_unitFactor_flatten_replicate`).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open PowerSeries

variable {N : Type*} [AddCommGroup N] (D : SkewLatticeDatum N) (d : PositiveDegrees D.unfrozen)

local notation "βℚ" => D.coefficientForm ℚ
local notation "hβℚ" => D.isAlt_coefficientForm ℚ
local notation "𝓛ℚ" => SkewLieAlgebra.positiveGrading βℚ hβℚ d
local notation "κ" => D.sublattice.toAddSubgroup.rayIndex

/-- A nonzero allowed degree of the positive degrees `d` of a skew lattice datum. -/
abbrev NonzeroDegree : Type _ := {n : D.unfrozen // n ∈ d.monoid ∧ n ≠ 0}

variable [DecidableEq D.unfrozen]

/-- The dilogarithm label `Ψ[n]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` of a nonzero allowed
degree `n` and a rational exponent `c`, in the completed skew group. -/
def dilogPow (n : D.NonzeroDegree d) (c : ℚ) : d.completedBCHGroup 𝓛ℚ :=
  SkewLieAlgebra.rayExp βℚ hβℚ n.2.1 n.2.2 (c • negDilogNeg ℚ)

/-- Unfolds `dilogPow`, which holds by definition. -/
theorem dilogPow_def (n : D.NonzeroDegree d) (c : ℚ) :
    D.dilogPow d n c = SkewLieAlgebra.rayExp βℚ hβℚ n.2.1 n.2.2 (c • negDilogNeg ℚ) := (rfl)

/-- Integer multiples of the exponent give integer powers of the label. -/
theorem dilogPow_intCast_mul (n : D.NonzeroDegree d) (s : ℤ) (c : ℚ) :
    D.dilogPow d n (s * c) = D.dilogPow d n c ^ s := by
  rw [dilogPow_def, dilogPow_def, ← SkewLieAlgebra.rayExp_zsmul, mul_smul,
    Int.cast_smul_eq_zsmul]

/-- Natural multiples of the exponent give natural powers of the label. -/
theorem dilogPow_natCast_mul (n : D.NonzeroDegree d) (s : ℕ) (c : ℚ) :
    D.dilogPow d n (s * c) = D.dilogPow d n c ^ s := by
  simpa using D.dilogPow_intCast_mul d n s c

/-- Labels of degree above the cutoff `k` project to the identity at order `k`. -/
theorem projection_prod_dilogPow_filter {ι : Type*} (l : List ι) (δ : ι → D.NonzeroDegree d)
    (σ : ι → ℚ) (k : ℕ) :
    CompletedGroup.projection k (l.map fun i => D.dilogPow d (δ i) (σ i)).prod =
      CompletedGroup.projection k
        ((l.filter fun i => d.degree (δ i).1 ≤ k).map fun i => D.dilogPow d (δ i) (σ i)).prod := by
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  refine (List.prod_map_filter_of_ne l fun i _ hi => ?_).symm
  by_contra hik
  refine hi ?_
  rw [Function.comp_apply, dilogPow_def]
  exact SkewLieAlgebra.projection_rayExp_eq_one_of_lt _ _ _ _ _ (by omega)

variable [Module.Free ℤ N]

/-- The unit factor `Ψ[n]^{κ(n)}` of a nonzero allowed degree `n`, where `κ` is the ray index
of `N°`. The normalized positive factors `Ψ[n]^{sκ(n)}`, `s ∈ ℕ`, are the powers of unit
factors. -/
def unitFactor (n : D.NonzeroDegree d) : d.completedBCHGroup 𝓛ℚ :=
  D.dilogPow d n (κ (n.1 : N))

/-- Unfolds `unitFactor`, which holds by definition. -/
theorem unitFactor_def (n : D.NonzeroDegree d) :
    D.unitFactor d n = D.dilogPow d n (κ (n.1 : N)) := (rfl)

/-- A normalized positive factor `Ψ[n]^{sκ(n)}` with `s ≥ 0` is the `s`-th power of the unit
factor of `n`. -/
theorem dilogPow_intCast_mul_rayIndex (n : D.NonzeroDegree d) {s : ℤ} (hs : 0 ≤ s) :
    D.dilogPow d n (s * κ (n.1 : N)) = D.unitFactor d n ^ s.toNat := by
  rw [dilogPow_intCast_mul, unitFactor_def, ← zpow_natCast, Int.toNat_of_nonneg hs]

/-- If each label `Ψ[δ i]^{σ i}` is the `s i`-th power of the unit factor of `δ i`, then the unit
factors of the flattened list of `s i` copies of each `δ i` multiply to the product of the
labels. -/
theorem prod_unitFactor_flatten_replicate {ι : Type*} (l : List ι) (δ : ι → D.NonzeroDegree d)
    (s : ι → ℕ) (σ : ι → ℚ) (h : ∀ i ∈ l, D.dilogPow d (δ i) (σ i) = D.unitFactor d (δ i) ^ s i) :
    ((l.map fun i => List.replicate (s i) (δ i)).flatten.map (D.unitFactor d)).prod =
      (l.map fun i => D.dilogPow d (δ i) (σ i)).prod := by
  rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  simp only [Function.comp_apply, List.map_replicate, List.prod_replicate]
  exact (h i hi).symm

end Mei.SkewLatticeDatum
