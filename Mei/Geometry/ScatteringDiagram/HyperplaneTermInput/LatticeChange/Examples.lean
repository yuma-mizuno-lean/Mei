/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.LatticeChange.Basic

/-!
# The lattice change for `m₁ = (1, 0)` and `m₂ = (1, 3)`

Let `M = ℤ²` and let `M₀ ⊆ M` be spanned by `m₁ = (1, 0)` and `m₂ = (1, 3)`, with
`ℓ = det(m₁, m₂) = 3` (`det_pos`). Take `m° = 2 m₁ + m₂ = (3, 3) = 3 • (1, 1)`, so `p = 2`, `q = 1`,
`m = (1, 1)` and `r = 3` (`three_nsmul_one_one`). The canonical normal map of the lattice change
`M ⊆ ⅓M₀` (`Mei.RankTwoLatticeChange.normalMap`) sends:

* the normals `e₂*` of `ℝm₁` and `3e₁* - e₂*` of `ℝm₂` in `M` (`lineNormal_zero_eq`,
  `lineNormal_one_eq`) to the normals `e₂*` and `e₁*` of `⅓M₀`, with comparison scalar one;
* the normal `x - y` of the diagonal `ℝ(1, 1)` in `M` to the normal `x - 2y` of `ℝ(2, 1)` in
  `⅓M₀`, with comparison scalar `3` (`normalMap_normal_one_one`, `normalScalar_normal_one_one`).

Hence, for the lines `ℝm₁`, `ℝm₂` with functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}`, the
general lattice-change statement applies with all of its hypotheses discharged: on each open
ray of the diagonal, the scattering class over `M` has a single wall function `f₀` and the class
over `⅓M₀` a single wall function `f₁` on the image ray, with `f₀ = f₁ ^ 3`
(`exists_diagonal_germLabel_smul_eq_of_toClass_eq`), and for any `f₀ = f₁ ^ 3` the germ label of
a representative over `⅓M₀` is the label of `f₁` exactly when that of a representative over `M`
is the label of `f₀` (`diagonal_germLabel_eq_iff_of_toClass_eq`).

This is an instance of the lattice change of Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1), with outer power `r = ℓ = 3`. The wall
functions are not computed.
-/

public section

open TauCeti (PositiveDegreeMap)

noncomputable section

namespace Mei.RankTwoLatticeChange.Examples

open DirectedWall DirectedDiagram TauCeti.Toric

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The determinant `det(m₁, m₂) = 3` of the generators is positive. -/
theorem det_pos : 0 < Prod.det ((1, 0) : ℤ × ℤ) (1, 3) := by
  norm_num [Prod.det_apply]

/-- `m° = 2 m₁ + m₂ = 3 • (1, 1)`. -/
theorem three_nsmul_one_one :
    (3 : ℕ) • ((1, 1) : ℤ × ℤ) = (2 : ℤ) • ((1, 0) : ℤ × ℤ) + (1 : ℤ) • ((1, 3) : ℤ × ℤ) := by
  decide

/-- The normal of `ℝm₁` in `M` is `e₂*`. -/
theorem lineNormal_zero_eq : lineNormal (1, 0) (1, 3) 0 = AddMonoidHom.snd ℤ ℤ :=
  AddMonoidHom.ext fun x => by simp [Prod.det_apply]

/-- The normal of `ℝm₂` in `M` is `3e₁* - e₂*`. -/
theorem lineNormal_one_eq :
    lineNormal (1, 0) (1, 3) 1 = (3 : ℤ) • AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ :=
  AddMonoidHom.ext fun x => by simp [Prod.det_apply, mul_comm]

/-- The normal of the diagonal `ℝ(1, 1)` in `M` is `x - y`. -/
theorem normal_one_one_apply (x : ℤ × ℤ) : normal (1, 1) x = x.1 - x.2 := by
  simp [Prod.det_apply]

/-- The normal of the line `ℝ(2, 1)` in `⅓M₀` is `x - 2y`. -/
theorem normal_two_one_apply (x : ℤ × ℤ) : normal (2, 1) x = x.1 - 2 * x.2 := by
  simp [Prod.det_apply, mul_comm]

/-- The normal map sends the normal `x - y` of the diagonal in `M` to the normal `x - 2y` of
`ℝ(2, 1)` in `⅓M₀`. -/
theorem normalMap_normal_one_one : normalMap (1, 0) (1, 3) (normal (1, 1)) = normal (2, 1) :=
  normalMap_normal det_pos isCoprime_one_right three_nsmul_one_one

/-- The comparison scalar of the normal of the diagonal is `r = 3`. -/
theorem normalScalar_normal_one_one : normalScalar (1, 0) (1, 3) (normal (1, 1)) = 3 := by
  rw [normalScalar_normal det_pos isCoprime_one_right three_nsmul_one_one, Nat.cast_ofNat]

variable (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The lattice change `M ⊆ ⅓M₀` with the canonical normal map. -/
abbrev latticeChangePushforward :
    Pushforward ℕ² ℕ² h h (tropicalVertexWallSpaces (R := ℚ) ℕ² (coord (1, 0) (1, 3)))
      (tropicalVertexWallSpaces ℕ² (sublatticeCoord (1, 0) (1, 3))) :=
  pushforward ℚ h det_pos (normalMap (1, 0) (1, 3)) (normalScalar (1, 0) (1, 3))
    (normalScalar_pos det_pos) (normalMap_apply_change det_pos)

/-- The filtration of the coefficients tangent to the diagonal over `M`. -/
local notation "F₀" => TropicalVertexCoefficientAction.filtration (R := ℚ) ℕ²
  (tropicalTangentMonoid ℕ² (coord (1, 0) (1, 3))
    (AddMonoidHom.comp (Int.castAddHom ℚ) (normal (1, 1))))

/-- The filtration of the coefficients tangent to `ℝ(2, 1)` over `⅓M₀`. -/
local notation "F₁" => TropicalVertexCoefficientAction.filtration (R := ℚ) ℕ²
  (tropicalTangentMonoid ℕ² (sublatticeCoord (1, 0) (1, 3))
    (AddMonoidHom.comp (Int.castAddHom ℚ) (normal (2, 1))))

/-- The tangent monomial map of the identity degree map. -/
local notation "Φ" => completedTropicalTangentMap (R := ℚ) (PositiveDegreeMap.id ℕ²)
  (map_tropicalTangentMonoid_intCast_le (PositiveDegreeMap.id ℕ²)
    (sublatticeCoord_id_eq_change_coord (1, 0) (1, 3))
    (intCast_normal_apply_change three_nsmul_one_one))

variable {K : ℕ} (c : Fin 2 × Fin K → ℚ)

/-- **The diagonal wall function over `M` is the cube of the one over `⅓M₀`, on whole rays.** Let
`θ` be a generic point of the diagonal for some representative `D₀` of the scattering class of the
lines over `M`, and let `v` cross the diagonal. Then there are completed tangent series `f₀` over
`M` and `f₁` over `⅓M₀`, congruent to one, with `f₀ = f₁ ^ 3` under the tangent monomial map,
such that every representative over `M` has the germ label `exp(log(f₀) ∂_{x - y})` in the
direction `v` at each of its generic points `t • θ`, `t > 0`, of the diagonal, and every
representative over `⅓M₀` has the germ label `exp(log(f₁) ∂_{x - 2y})` in the direction `S v` at
each of its generic points `t • S θ`, `t > 0`, of the image line. -/
theorem exists_diagonal_germLabel_smul_eq_of_toClass_eq {κ₀ : Type}
    {D₀ : DirectedDiagram (d := ℕ²) h
      (tropicalVertexWallSpaces (R := ℚ) ℕ² (coord (1, 0) (1, 3))) κ₀}
    (hD₀ : D₀.toClass =
      ((latticeLineInput det_pos K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D₀.IsGenericPoint (line h (1, 1)) θ)
    (hv : h.realCharacter (normal (1, 1)) v ≠ 0) :
    ∃ (f₀ : {u : (F₀).completion // u - 1 ∈ (F₀).completionIdeal 1})
      (f₁ : {u : (F₁).completion // u - 1 ∈ (F₁).completionIdeal 1}),
      Φ f₀ = (f₁ : (F₁).completion) ^ 3 ∧
      (∀ {κ : Type} {D : DirectedDiagram (d := ℕ²) h
          (tropicalVertexWallSpaces (R := ℚ) ℕ² (coord (1, 0) (1, 3))) κ},
        D.toClass = ((latticeLineInput det_pos K).diagram h c).Scat
          (fun _ => ofHyperplaneRayFactors_full ..) →
        ∀ {t : ℝ} (_ : 0 < t) (htθ : D.IsGenericPoint (line h (1, 1)) (t • θ)),
          D.germLabel (t • θ) v htθ.isRegular = ℕ².completedBCHExp _
            (completedTropicalTangentField ℕ² (coord (1, 0) (1, 3))
              ((Int.castAddHom ℚ).comp (normal (1, 1))) ((F₀).completedLog f₀))) ∧
      (∀ {ι : Type} {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ²
          (sublatticeCoord (1, 0) (1, 3))) ι},
        E.toClass =
          ((sublatticeLineInput (1, 0) (1, 3) K).diagram h c).Scat
            (fun _ => ofHyperplaneRayFactors_full ..) →
        ∀ {t : ℝ} (_ : 0 < t) (htθ : E.IsGenericPoint ((line h (1, 1)).map
            (latticeChangePushforward h).spatialMap.toAffineEquiv.toAffineMap)
            (t • (latticeChangePushforward h).spatialMap θ)),
          E.germLabel (t • (latticeChangePushforward h).spatialMap θ)
              ((latticeChangePushforward h).spatialMap.toAffineEquiv.linear v) htθ.isRegular =
            ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (sublatticeCoord (1, 0) (1, 3))
              ((Int.castAddHom ℚ).comp (normal (2, 1))) ((F₁).completedLog f₁))) :=
  exists_germLabel_smul_eq_of_toClass_eq det_pos (normalScalar_pos det_pos)
    (normalMap_apply_change det_pos) three_nsmul_one_one c (normalMap_lineNormal det_pos)
    normalMap_normal_one_one isCoprime_one_right zero_le_two zero_le_one
    (Prod.isPrimitive_mk_of_isCoprime isCoprime_one_left) hD₀ hθ hv

/-- **The diagonal germ labels determine each other.** Let `D` represent the scattering class of
the lines over `M` and `E` that over `⅓M₀`, let `θ` be a generic point of the diagonal for `D`
whose image `S θ` is a generic point of the image line for `E`, and let `v` cross the diagonal.
For `f₀ = f₁ ^ 3` under the tangent monomial map, the germ label of `E` at `S θ` in the direction
`S v` is `exp(log(f₁) ∂_{x - 2y})` exactly when the germ label of `D` at `θ` in the direction `v`
is `exp(log(f₀) ∂_{x - y})`. -/
theorem diagonal_germLabel_eq_iff_of_toClass_eq {κ ι : Type}
    {D : DirectedDiagram (d := ℕ²) h
      (tropicalVertexWallSpaces (R := ℚ) ℕ² (coord (1, 0) (1, 3))) κ}
    (hDc : D.toClass =
      ((latticeLineInput det_pos K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ²
      (sublatticeCoord (1, 0) (1, 3))) ι}
    (hEc : E.toClass = ((sublatticeLineInput (1, 0) (1, 3) K).diagram h c).Scat
      (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (line h (1, 1)) θ)
    (hθ' : E.IsGenericPoint ((line h (1, 1)).map
      (latticeChangePushforward h).spatialMap.toAffineEquiv.toAffineMap)
      ((latticeChangePushforward h).spatialMap θ))
    (hv : h.realCharacter (normal (1, 1)) v ≠ 0)
    (f₀ : {u : (F₀).completion // u - 1 ∈ (F₀).completionIdeal 1})
    (f₁ : {u : (F₁).completion // u - 1 ∈ (F₁).completionIdeal 1})
    (hf : Φ f₀ = (f₁ : (F₁).completion) ^ 3) :
    E.germLabel ((latticeChangePushforward h).spatialMap θ)
        ((latticeChangePushforward h).spatialMap.toAffineEquiv.linear v) hθ'.isRegular =
        ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (sublatticeCoord (1, 0) (1, 3))
          ((Int.castAddHom ℚ).comp (normal (2, 1))) ((F₁).completedLog f₁)) ↔
      D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ²
        (coord (1, 0) (1, 3)) ((Int.castAddHom ℚ).comp (normal (1, 1))) ((F₀).completedLog f₀)) :=
  germLabel_eq_iff_of_toClass_eq det_pos (normalScalar_pos det_pos)
    (normalMap_apply_change det_pos) three_nsmul_one_one c (normalMap_lineNormal det_pos)
    normalMap_normal_one_one (by simp) hDc hEc hθ hθ' hv f₀ f₁ hf

end Mei.RankTwoLatticeChange.Examples
