/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.WallFunction
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.Pushforward

/-!
# Polynomial function walls under finite-index lattice changes

Let `P = DirectedWall.Pushforward.ofFiniteIndex T t ht hρ ν q hq hν` be the pushforward along
a finite-index tangent embedding `t : Λ → Λ'` with a compatible positive degree map `T`, where
`ν m ∘ t = q m • m` for integral normals `m`. Let `I` be a `HyperplaneTermInput` on `Λ` whose
normals `μ_i` have comparison scalar `q μ_i = 1`, so that `ν μ_i ∘ t = μ_i`
(`HyperplaneTermInput.comp_normal_of_ofFiniteIndex`). For instance, for the inclusion
`M ⊆ ℓ⁻¹M₀` of a rank-two lattice, where `M₀` is spanned by primitive vectors `m₁, m₂` of `M`
with index `ℓ`, the primitive normals of a line `ℝm_i` for `M` and for `ℓ⁻¹M₀` restrict to each
other, since `ℓ = r · ind(m_i)` with `r = 1` (`Submodule.index_eq_mul_relIndex_ker_eval`);
for two lines in rank two this is `Mei.RankTwoLatticeChange.normalScalar_lineNormal`.

The image input `I.map T t hρ (ν ∘ μ)` has normals `ν μ_i`, the same offsets and terms, and
exponents `T n_α`. The finite-index pushforward sends `z^n ∂_{μ_i}` to `z^{T n} ∂_{ν μ_i}`, since
the denominator `q μ_i` is one, and moves the hyperplane `{μ_i = a_i}` onto `{ν μ_i = a_i}`.
Hence the pushforward of the ray presentation of `I` is equivalent to the ray presentation of
the image input (`HyperplaneTermInput.diagram_pushforward_ofFiniteIndex_equivalent`), and the
pushforward of the scattering class of `I` is the scattering class of the image input
(`HyperplaneTermInput.pushforward_ofFiniteIndex_scat_diagram`). So the pushforward of any
representative of the first class represents the second
(`HyperplaneTermInput.toClass_pushforward_ofFiniteIndex`). When the pushed normals of its walls
stay primitive, its function-wall groupings are pushed along with it
(`DirectedDiagram.FunctionWallGrouping.pushforward`), and a given group label
`exp(log(f₀) ∂_n)` with `q n = r` and `T_* f₀ = f₁ ^ r` becomes `exp(log(f₁) ∂_{ν n})`
(`DirectedDiagram.FunctionWallGrouping.label_pushforward_ofFiniteIndex`).

This is the incoming-lines step used in the lattice change of Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1), where `t` is the
inclusion `M ⊆ ℓ⁻¹M₀` and the incoming lines are the lines `ℝm_i` with functions
`1 + ∑_k p_{i,k} x^{k m_i}`, here with finitely many terms. Only the pushforward of a given
representative and of its groups is treated: no comparison of the pushed groups with the groups
of an independently chosen representative of the image class is proved.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)

noncomputable section

namespace Mei.HyperplaneTermInput

open DirectedWall DirectedDiagram TauCeti.Toric

universe u

variable {R Γ Λ Γ' Λ' ι E : Type u} {V V' : Type*} [CommRing R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [AddCommGroup Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (I : HyperplaneTermInput d ρ ι E) (T : PositiveDegreeMap d e) (t : Λ →+ Λ')
  (ht : Function.Injective t) [t.range.FiniteIndex] (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n))
  {ν : (Λ →+ ℤ) → (Λ' →+ ℤ)} {q : (Λ →+ ℤ) → ℚ} (hq : ∀ m, 0 < q m)
  (hν : ∀ m x, (ν m (t x) : ℚ) = q m * m x) (hq₁ : ∀ i, q (I.normal i) = 1)

omit [t.range.FiniteIndex] in
include hν hq₁ in
/-- If the comparison scalar of the normal `μ_i` is one, the normal `ν μ_i` restricts along `t`
to `μ_i`. -/
theorem comp_normal_of_ofFiniteIndex (i : ι) : (ν (I.normal i)).comp t = I.normal i :=
  AddMonoidHom.ext fun x => by
    have hx := hν (I.normal i) x
    rw [hq₁ i, one_mul] at hx
    exact_mod_cast hx

variable [Module.Free ℤ Γ] [Module.Free ℤ Γ'] [Fintype E] [DecidableEq ι] [DecidableEq Γ]
  [DecidableEq Γ'] [Algebra ℚ R] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] {j : Λ →+ V} {j' : Λ' →+ V'}
  (h : IsIntegralLattice j) (h' : IsIntegralLattice j') (c : E → R)

local notation "P" => Pushforward.ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν

include hq₁ in
/-- If the normals `μ_i` have comparison scalar one, the finite-index pushforward of the ray
presentation of `I` is equivalent to the ray presentation of the input with normals `ν μ_i`, the
same offsets and terms, and exponents `T n_α`. -/
theorem diagram_pushforward_ofFiniteIndex_equivalent :
    ((I.diagram h c).pushforward (P)).Equivalent
      ((I.map T t hρ (fun i => ν (I.normal i)) (I.comp_normal_of_ofFiniteIndex t hν hq₁)).diagram
        h' c) := by
  have hPT : ∀ n ∈ d.monoid, ρ' ((P).degreeMap n) = t (ρ n) := fun n hn => by
    rw [Pushforward.ofFiniteIndex_degreeMap]
    exact hρ n hn
  rw [map_congr (T' := (P).degreeMap) (hT' := hPT) fun α => by
    rw [Pushforward.ofFiniteIndex_degreeMap]]
  refine I.diagram_pushforward_equivalent t _ _ (P) (fun i n x hx => ?_) hPT c
    (fun i => Pushforward.ofFiniteIndex_normalMap ..) fun i y => ?_
  · rw [Pushforward.coe_ofFiniteIndex_lieHom_of_eq_single T t ht hρ ν q hq hν (I.normal i)
      (hν (I.normal i)) x hx, hq₁ i, inv_one, map_one, one_smul,
      Pushforward.ofFiniteIndex_degreeMap]
  · have hy := LinearMap.congr_fun (h.realCharacter_comp_extend h' t (hν (I.normal i))) y
    rw [hq₁ i, Rat.cast_one, one_smul] at hy
    rwa [Pushforward.ofFiniteIndex_spatialMap,
      IsIntegralLattice.coe_extendContinuousAffineEquivOfFiniteIndex]

include hq₁ in
/-- If the normals `μ_i` have comparison scalar one, the finite-index pushforward of the
scattering class of `I` is the scattering class of the input with normals `ν μ_i`, the same
offsets and terms, and exponents `T n_α`. -/
theorem pushforward_ofFiniteIndex_scat_diagram :
    Class.pushforward (P) ((I.diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((I.map T t hρ (fun i => ν (I.normal i)) (I.comp_normal_of_ofFiniteIndex t hν hq₁)).diagram
        h' c).Scat (fun _ => ofHyperplaneRayFactors_full ..) :=
  ((I.diagram h c).pushforward_scat _ _).trans (DirectedDiagram.scat_eq_of_equivalent _ _
    (I.diagram_pushforward_ofFiniteIndex_equivalent T t ht hρ hq hν hq₁ h h' c))

include hq₁ in
/-- If the normals `μ_i` have comparison scalar one, the finite-index pushforward of a
representative of the scattering class of `I` represents the scattering class of the input with
normals `ν μ_i`, the same offsets and terms, and exponents `T n_α`. -/
theorem toClass_pushforward_ofFiniteIndex {κ : Type u}
    {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ) κ}
    (hD : D.toClass = (I.diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) :
    (D.pushforward (P)).toClass =
      ((I.map T t hρ (fun i => ν (I.normal i)) (I.comp_normal_of_ofFiniteIndex t hν hq₁)).diagram
        h' c).Scat (fun _ => ofHyperplaneRayFactors_full ..) := by
  rw [← Class.pushforward_toClass, hD,
    I.pushforward_ofFiniteIndex_scat_diagram T t ht hρ hq hν hq₁ h h' c]

end Mei.HyperplaneTermInput
