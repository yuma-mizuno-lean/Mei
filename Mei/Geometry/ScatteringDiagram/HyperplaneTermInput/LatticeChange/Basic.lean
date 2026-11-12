/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Dilation
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.GermLabel
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.FiniteIndex
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.TangentLabel
public import Mei.LinearAlgebra.Determinant.LatticeChange

/-!
# The rank-two lattice change of two incoming lines

Let `m₁, m₂ ∈ M = ℤ²` be independent with `ℓ = det(m₁, m₂) > 0`, spanning `M₀`, and let
`m° = p m₁ + q m₂ = r • m` with `p, q ≥ 0` coprime and `m` primitive in `M`. In the coordinates
of `Mei.RankTwoLatticeChange` (coefficient exponents `(a, b) ∈ ℕ²` of `x^{a m₁ + b m₂}`), the
incoming lines `ℝm₁` and `ℝm₂` with functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}` form the input
`latticeLineInput` over `M` and `sublatticeLineInput` over `ℓ⁻¹M₀`. Let `P` be the finite-index
pushforward along `M ⊆ ℓ⁻¹M₀` (`pushforward`) for a normal map `ν` with `ν μ ∘ change = σ μ • μ`
that sends the normals of the two lines to their normals in `ℓ⁻¹M₀` and the normal `det(·, m)` of
`ℝm°` in `M` to its normal `det(·, (p, q))` in `ℓ⁻¹M₀`; the canonical `normalMap` is such a map
(`normalMap_lineNormal`, `normalMap_normal`). This file proves the lattice-change statement of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, Theorem 9.5
(arXiv:2503.03719v1), with germ labels at generic points standing for "the wall function on a
ray":

* `P` carries the scattering class of the lines over `M` to the scattering class of the lines over
  `ℓ⁻¹M₀` (`pushforward_scat`), so it sends representatives to representatives
  (`toClass_pushforward`);
* every active wall of a diagram over `M` through a generic point of the line `ℝm°` lies on the
  supported ray `(p, q)` of `ℕ²` with a normal proportional to `det(·, m)`
  (`label_mem_wallGroup_of_isGenericPoint`), using that `(p, q)` is the only supported ray with
  direction on `ℝm°` (`eq_coefficientRay_of_normal_coord_eq_zero`);
* on each open ray `ℝ_{>0}θ` of `ℝm°` through a generic point of some representative, the class
  over `M` has a single wall function `f₀`, and the class over `ℓ⁻¹M₀` has a single wall function
  `f₁` on the image ray, with `f₀ = f₁ ^ r`: every representative has the germ label
  `exp(log(f₀) ∂_{det(·, m)})`, respectively `exp(log(f₁) ∂_{det(·, (p, q))})`, at each of its
  generic points of the ray (`exists_germLabel_smul_eq_of_toClass_eq`); at common generic points
  this holds for any pair of representatives (`exists_germLabel_eq_of_toClass_eq`);
* conversely, for any `f₀ = f₁ ^ r`, a representative over `ℓ⁻¹M₀` has the germ label of `f₁`
  exactly when a representative over `M` has the germ label of `f₀`
  (`germLabel_eq_iff_of_toClass_eq`).

The outer power `r` is `ℓ / ind(m°)` (`Submodule.index_eq_mul_relIndex_ker_eval`). The wall
functions are not computed, and positivity is not transported. The case `m₁ = (1, 0)`,
`m₂ = (1, 2)` with `r = 2` and the explicit wall functions `(1 + a z^{(1,1)})²` and
`1 + a z^{(1,1)}` is `Mei.HyperplaneTermInput.FiniteIndex.Examples`, and a case with `r = 3` is
`Mei.RankTwoLatticeChange.Examples`. Generic points of `ℝm°` common to two representatives exist
in every open set meeting the line (`exists_isGenericPoint_pair_line`), and the germ labels of the
class over `M` are constant along open rays of `ℝm°` (`germLabel_smul_eq_of_toClass_eq`).
-/

public section

open TauCeti (PositiveDegreeMap SupportedRay)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.RankTwoLatticeChange

open DirectedWall DirectedDiagram TauCeti.Toric

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The incoming lines `ℝm₁` and `ℝm₂` through the origin, in tangent coordinates `ρ₀` and
cooriented by `μ₀ 0` and `μ₀ 1`, with the terms `x^{(k + 1) m_i}` for `k < K`: the term `(i, k)`
has coefficient exponent `(k + 1) • e_i`. -/
def lineInput (ρ₀ : ℤ × ℤ →+ ℤ × ℤ) (μ₀ : Fin 2 → ℤ × ℤ →+ ℤ) (hμ₀ : ∀ i, μ₀ i ≠ 0)
    (hρμ : ∀ i, μ₀ i (ρ₀ (Module.Basis.finTwoProd ℤ i)) = 0) (K : ℕ) :
    HyperplaneTermInput ℕ² ρ₀ (Fin 2) (Fin 2 × Fin K) where
  normal := μ₀
  normal_ne_zero := hμ₀
  offset _ := 0
  wallIndex := Prod.fst
  exponent α := ((α.2 : ℤ) + 1) • Module.Basis.finTwoProd ℤ α.1
  exponent_mem α := Module.Basis.zsmul_mem_positiveDegrees_monoid _ α.1 (by positivity)
  exponent_ne_zero α := smul_ne_zero (by positivity) ((Module.Basis.finTwoProd ℤ).ne_zero α.1)
  normal_exponent α := by rw [map_zsmul, map_zsmul, hρμ, smul_zero]

section LineInput

variable (ρ₀ : ℤ × ℤ →+ ℤ × ℤ) (μ₀ : Fin 2 → ℤ × ℤ →+ ℤ) (hμ₀ : ∀ i, μ₀ i ≠ 0)
  (hρμ : ∀ i, μ₀ i (ρ₀ (Module.Basis.finTwoProd ℤ i)) = 0) (K : ℕ)

/-- The line `ℝm_i` is cooriented by `μ₀ i`. -/
@[simp]
theorem lineInput_normal : (lineInput ρ₀ μ₀ hμ₀ hρμ K).normal = μ₀ := by
  simp [lineInput]

/-- The lines pass through the origin. -/
@[simp]
theorem lineInput_offset : (lineInput ρ₀ μ₀ hμ₀ hρμ K).offset = 0 := by
  simp [lineInput, Pi.zero_def]

/-- The term `(i, k)` lies on the line `ℝm_i`. -/
@[simp]
theorem lineInput_wallIndex : (lineInput ρ₀ μ₀ hμ₀ hρμ K).wallIndex = Prod.fst := by
  simp [lineInput]

/-- The term `(i, k)` has coefficient exponent `(k + 1) • e_i`. -/
@[simp]
theorem lineInput_exponent (α : Fin 2 × Fin K) :
    (lineInput ρ₀ μ₀ hμ₀ hρμ K).exponent α =
      ((α.2 : ℤ) + 1) • Module.Basis.finTwoProd ℤ α.1 := by
  simp [lineInput]

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The ray presentation of the lines has its walls on hyperplanes through the origin. -/
theorem lineInput_diagram_wall_support (c : Fin 2 × Fin K → R) :
    ∀ x, (((lineInput ρ₀ μ₀ hμ₀ hρμ K).diagram h c).wall x).support =
      {y | h.realCharacter (((lineInput ρ₀ μ₀ hμ₀ hρμ K).diagram h c).wall x).normal y = 0} :=
  fun x => by
    rw [ofHyperplaneRayFactors_support, ofHyperplaneRayFactors_normal, lineInput_offset,
      Pi.zero_apply]

end LineInput

variable {m₁ m₂ : ℤ × ℤ}

/-- The incoming lines `ℝm₁` and `ℝm₂` over `M`, cooriented by `det(m₁, ·)` and `det(·, m₂)`. -/
abbrev latticeLineInput (hD : 0 < Prod.det m₁ m₂) (K : ℕ) :
    HyperplaneTermInput ℕ² (coord m₁ m₂) (Fin 2) (Fin 2 × Fin K) :=
  lineInput (coord m₁ m₂) (lineNormal m₁ m₂) (lineNormal_ne_zero hD.ne')
    (lineNormal_apply_coord_finTwoProd m₁ m₂) K

variable (m₁ m₂) in
/-- The incoming lines `ℝm₁` and `ℝm₂` over `ℓ⁻¹M₀`, cooriented by `e₂*` and `e₁*`. -/
abbrev sublatticeLineInput (K : ℕ) :
    HyperplaneTermInput ℕ² (sublatticeCoord m₁ m₂) (Fin 2) (Fin 2 × Fin K) :=
  lineInput (sublatticeCoord m₁ m₂) sublatticeLineNormal sublatticeLineNormal_ne_zero
    (sublatticeLineNormal_apply_sublatticeCoord_finTwoProd m₁ m₂) K

variable (m₁ m₂) in
/-- The two coordinate maps are compatible with the inclusion `M ⊆ ℓ⁻¹M₀` on all degrees. -/
theorem sublatticeCoord_id_eq_change_coord (n : ℤ × ℤ) (_ : n ∈ ℕ².monoid) :
    sublatticeCoord m₁ m₂ (PositiveDegreeMap.id ℕ² n) = change m₁ m₂ (coord m₁ m₂ n) := by
  rw [PositiveDegreeMap.id_apply, sublatticeCoord_eq_change_coord]

section CoefficientRay

variable {p q : ℤ} {m : ℤ × ℤ} {r : ℕ}

/-- The supported ray of `ℕ²` through the coefficient exponent `(p, q)`, for coprime
`p, q ≥ 0`. -/
def coefficientRay (hpq : IsCoprime p q) (hp : 0 ≤ p) (hq : 0 ≤ q) : SupportedRay ℕ² :=
  SupportedRay.ofMem (p, q) ((Module.Basis.mem_positiveDegrees_finTwoProd_monoid _).mpr ⟨hp, hq⟩)
    (Prod.isPrimitive_mk_of_isCoprime hpq)

/-- The generator of the ray `(p, q)` is `(p, q)`. -/
@[simp]
theorem coefficientRay_generator (hpq : IsCoprime p q) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (coefficientRay hpq hp hq).generator = (p, q) :=
  SupportedRay.generator_ofMem _ _ _

/-- **The supported ray of `ℝm°`.** Let `m₁, m₂` be independent, `p, q ≥ 0` coprime and
`r • m = p • m₁ + q • m₂`. The ray `(p, q)` is the only supported ray of `ℕ²` whose direction in
`M` lies on the line `ℝm`. -/
theorem eq_coefficientRay_of_normal_coord_eq_zero (hD : Prod.det m₁ m₂ ≠ 0) (hpq : IsCoprime p q)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : r • m = p • m₁ + q • m₂) {w : SupportedRay ℕ²}
    (hw : normal m (coord m₁ m₂ w.generator) = 0) : w = coefficientRay hpq hp hq := by
  obtain ⟨k, hk⟩ := exists_eq_zsmul_of_normal_coord_eq_zero hD hpq hm hw
  obtain ⟨s, hs, hsw⟩ := w.supported
  rw [hk, smul_smul, Module.Basis.mem_positiveDegrees_finTwoProd_monoid] at hsw
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hsw
  have hk0 : 0 ≤ k := by
    by_contra! hk0
    have hsk : s * k < 0 := mul_neg_of_pos_of_neg hs hk0
    have hp0 : p = 0 := le_antisymm (by nlinarith) hp
    have hq0 : q = 0 := le_antisymm (by nlinarith) hq
    rw [hp0, hq0] at hpq
    exact not_isCoprime_zero_zero hpq
  have hgen : w.generator = k.toNat • ((p, q) : ℤ × ℤ) := by
    rw [hk, ← natCast_zsmul, Int.toNat_of_nonneg hk0]
  have hone := w.isPrimitive.eq_one_of_eq_nsmul hgen
  refine SupportedRay.ext ?_
  rw [coefficientRay_generator, hgen, hone, one_smul]

end CoefficientRay

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  (hD : 0 < Prod.det m₁ m₂) (ν : (ℤ × ℤ →+ ℤ) → (ℤ × ℤ →+ ℤ)) (σ : (ℤ × ℤ →+ ℤ) → ℚ)
  (hσ : ∀ μ, 0 < σ μ) (hν : ∀ μ x, (ν μ (change m₁ m₂ x) : ℚ) = σ μ * μ x)

/-- The finite-index pushforward along `M ⊆ ℓ⁻¹M₀`, with identity degree map and a normal map `ν`
with `ν μ ∘ change = σ μ • μ`; see `pushforward_eq_ofFiniteIndex`. -/
def pushforward :
    Pushforward ℕ² ℕ² h h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂))
      (tropicalVertexWallSpaces ℕ² (sublatticeCoord m₁ m₂)) :=
  haveI := finiteIndex_range_change hD
  Pushforward.ofFiniteIndex (PositiveDegreeMap.id ℕ²) (change m₁ m₂) (change_injective hD.ne')
    (sublatticeCoord_id_eq_change_coord m₁ m₂) ν σ hσ hν

/-- The lattice change is the finite-index pushforward along `change m₁ m₂`, for any instance
of finite index: the defining equation of `pushforward`. -/
theorem pushforward_eq_ofFiniteIndex [(change m₁ m₂).range.FiniteIndex] :
    pushforward R h hD ν σ hσ hν =
      Pushforward.ofFiniteIndex (PositiveDegreeMap.id ℕ²) (change m₁ m₂) (change_injective hD.ne')
        (sublatticeCoord_id_eq_change_coord m₁ m₂) ν σ hσ hν := by
  rw [pushforward]

/-- The degree map of the lattice change is the identity. -/
@[simp]
theorem pushforward_degreeMap :
    (pushforward R h hD ν σ hσ hν).degreeMap = PositiveDegreeMap.id ℕ² := by
  have := finiteIndex_range_change hD
  rw [pushforward_eq_ofFiniteIndex, Pushforward.ofFiniteIndex_degreeMap]

/-- The normal map of the lattice change is `ν`. -/
@[simp]
theorem pushforward_normalMap (μ : ℤ × ℤ →+ ℤ) :
    (pushforward R h hD ν σ hσ hν).normalMap μ = ν μ := by
  have := finiteIndex_range_change hD
  rw [pushforward_eq_ofFiniteIndex, Pushforward.ofFiniteIndex_normalMap]

/-- The completed Lie map of the lattice change is injective. -/
theorem pushforward_lieHom_completedMap_injective :
    Function.Injective (pushforward R h hD ν σ hσ hν).lieHom.completedMap := by
  have := finiteIndex_range_change hD
  rw [pushforward_eq_ofFiniteIndex]
  exact Pushforward.ofFiniteIndex_lieHom_completedMap_injective _ _ _ _ _ _ _ _
    fun _ _ hxy => by simpa only [PositiveDegreeMap.id_apply] using hxy

section Lines

variable {R ν σ} (hline : ∀ i, ν (lineNormal m₁ m₂ i) = sublatticeLineNormal i)

include hD hν hline in
/-- If `ν` sends the normals of the lines in `M` to their normals in `ℓ⁻¹M₀`, their comparison
scalars are one. -/
theorem scalar_lineNormal_eq_one (i : Fin 2) : σ (lineNormal m₁ m₂ i) = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, lineNormal m₁ m₂ i x ≠ 0 := by
    by_contra! h0
    exact lineNormal_ne_zero hD.ne' i (AddMonoidHom.ext h0)
  have h := hν (lineNormal m₁ m₂ i) x
  have hx' : (lineNormal m₁ m₂ i x : ℚ) ≠ 0 := by exact_mod_cast hx
  rw [hline, sublatticeLineNormal_apply_change] at h
  exact (mul_eq_right₀ hx').mp h.symm

include hD hν hline in
/-- The normals of the input over `M` have comparison scalar one. -/
theorem scalar_latticeLineInput_normal (K : ℕ) (i : Fin 2) :
    σ ((latticeLineInput hD K).normal i) = 1 := by
  rw [lineInput_normal]
  exact scalar_lineNormal_eq_one hD hν hline i

include hline in
/-- The input over `M` mapped along `M ⊆ ℓ⁻¹M₀` with the normals `ν` is the input over `ℓ⁻¹M₀`. -/
theorem latticeLineInput_map (K : ℕ) :
    haveI := finiteIndex_range_change hD
    (latticeLineInput hD K).map (PositiveDegreeMap.id ℕ²) (change m₁ m₂)
        (sublatticeCoord_id_eq_change_coord m₁ m₂)
        (fun i => ν ((latticeLineInput hD K).normal i))
        ((latticeLineInput hD K).comp_normal_of_ofFiniteIndex (change m₁ m₂) hν
          (scalar_latticeLineInput_normal hD hν hline K)) =
      sublatticeLineInput m₁ m₂ K :=
  HyperplaneTermInput.ext (funext fun i => by simp [hline]) (by simp) (by simp)
    (funext fun α => by simp)

variable (R) {K : ℕ} (c : Fin 2 × Fin K → R)

include hline in
/-- **Incoming lines under the lattice change.** The pushforward along `M ⊆ ℓ⁻¹M₀` of the ray
presentation of the lines `ℝm_i` with functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}` over `M` is
equivalent to the ray presentation of the same lines and functions over `ℓ⁻¹M₀`. -/
theorem pushforward_equivalent :
    (((latticeLineInput hD K).diagram h c).pushforward
      (pushforward R h hD ν σ hσ hν)).Equivalent ((sublatticeLineInput m₁ m₂ K).diagram h c) := by
  have := finiteIndex_range_change hD
  rw [← latticeLineInput_map hD hν hline, pushforward_eq_ofFiniteIndex]
  exact (latticeLineInput hD K).diagram_pushforward_ofFiniteIndex_equivalent _ _
    (change_injective hD.ne') _ hσ _ (scalar_latticeLineInput_normal hD hν hline K) h h c

include hline in
/-- **Scattering classes under the lattice change.** The pushforward along `M ⊆ ℓ⁻¹M₀` of the
scattering class of the lines over `M` is the scattering class of the lines over `ℓ⁻¹M₀`. -/
theorem pushforward_scat :
    Class.pushforward (pushforward R h hD ν σ hσ hν)
        (((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((sublatticeLineInput m₁ m₂ K).diagram h c).Scat
        (fun _ => ofHyperplaneRayFactors_full ..) :=
  ((latticeLineInput hD K).diagram h c |>.pushforward_scat _ _).trans
    (DirectedDiagram.scat_eq_of_equivalent _ _ (pushforward_equivalent R h hD hσ hν hline c))

include hline in
/-- A diagram representing the scattering class of the lines over `M` is pushed along
`M ⊆ ℓ⁻¹M₀` to a diagram representing the scattering class of the lines over `ℓ⁻¹M₀`. -/
theorem toClass_pushforward {κ : Type}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ}
    (hDc : D.toClass =
      ((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) :
    (D.pushforward (pushforward R h hD ν σ hσ hν)).toClass =
      ((sublatticeLineInput m₁ m₂ K).diagram h c).Scat
        (fun _ => ofHyperplaneRayFactors_full ..) := by
  rw [← Class.pushforward_toClass, hDc, pushforward_scat R h hD hσ hν hline c]

end Lines

section GermLabel

variable {R h ν σ} {p q : ℤ} {m : ℤ × ℤ} {r : ℕ}

variable (h) in
/-- The line `ℝm` of `ℝ²`, the kernel of the real extension of `det(·, m)`. -/
def line (m : ℤ × ℤ) : AffineSubspace ℝ (ℝ × ℝ) :=
  (LinearMap.ker (h.realCharacter (normal m))).toAffineSubspace

/-- A point lies on the line `ℝm` when `det(·, m)` vanishes on it. -/
@[simp]
theorem mem_line {θ : ℝ × ℝ} : θ ∈ line h m ↔ h.realCharacter (normal m) θ = 0 := by
  rw [line, Submodule.mem_toAffineSubspace, LinearMap.mem_ker]

/-- The direction of the line `ℝm` is the kernel of the real extension of `det(·, m)`. -/
theorem direction_line : (line h m).direction = LinearMap.ker (h.realCharacter (normal m)) := by
  rw [line, Submodule.toAffineSubspace_direction]

/-- A direction is transverse to the line `ℝm` when `det(·, m)` does not vanish on it. -/
theorem notMem_direction_line_iff {v : ℝ × ℝ} :
    v ∉ (line h m).direction ↔ h.realCharacter (normal m) v ≠ 0 := by
  rw [direction_line, LinearMap.mem_ker]

/-- For `m ≠ 0`, the line `ℝm` is an affine hyperplane of `ℝ²`. -/
theorem finrank_direction_line (hm : m ≠ 0) :
    Module.finrank ℝ (line h m).direction + 1 = Module.finrank ℝ (ℝ × ℝ) := by
  rw [direction_line]
  refine Module.Dual.finrank_ker_add_one_of_ne_zero fun he => normal_apply_ne_zero hm ?_
  have h₁ := LinearMap.congr_fun he (((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)) (m.2, -m.1))
  rw [h.realCharacter_apply, LinearMap.zero_apply] at h₁
  exact_mod_cast h₁

/-- **Walls through a generic point of `ℝm°`.** Let `m₁, m₂` be independent, `p, q ≥ 0` coprime and
`r • m = p • m₁ + q • m₂` with `m` primitive. Every active wall through a generic point of the line
`ℝm`, for a diagram over `M`, has its label in the wall group of the supported ray `(p, q)` with
normal `det(·, m)`. -/
theorem label_mem_wallGroup_of_isGenericPoint (hD : Prod.det m₁ m₂ ≠ 0) (hpq : IsCoprime p q)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : r • m = p • m₁ + q • m₂) (hmp : TauCeti.IsPrimitive m)
    {κ : Type*}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ}
    {θ : ℝ × ℝ} (hθ : D.IsGenericPoint (line h m) θ) {k : ℕ} (j : D.active k)
    (hj : θ ∈ (D.wall j).support) :
    (D.wall j).label ∈ (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)).wallGroup
      (coefficientRay hpq hp hq) (normal m) := by
  /- The wall spans the line, so its normal `μ` vanishes on `m` and is a nonzero multiple of
  `det(·, m)`. Its ray is then tangent to the line, hence the ray `(p, q)`. -/
  have hker : LinearMap.ker (h.realCharacter (D.wall j).normal) =
      LinearMap.ker (h.realCharacter (normal m)) := by
    rw [← (D.wall j).direction_support, hθ.affineSpan_eq j hj, direction_line]
  have hμm : (D.wall j).normal m = 0 := by
    have hmem : ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)) m ∈
        LinearMap.ker (h.realCharacter (D.wall j).normal) := by
      rw [hker, LinearMap.mem_ker, h.realCharacter_apply, normal_apply,
        Prod.isAlt_det.self_eq_zero, Int.cast_zero]
    rw [LinearMap.mem_ker, h.realCharacter_apply] at hmem
    exact_mod_cast hmem
  obtain ⟨c, hc⟩ := exists_eq_zsmul_normal hmp hμm
  have hc0 : c ≠ 0 := fun h0 => (D.wall j).normal_ne_zero (by rw [hc, h0, zero_smul])
  have hray : (D.wall j).ray = coefficientRay hpq hp hq := by
    refine eq_coefficientRay_of_normal_coord_eq_zero hD hpq hp hq hm ?_
    have hdir := (D.wall j).normal_direction
    rw [hc, AddMonoidHom.smul_apply, smul_eq_mul] at hdir
    exact (mul_eq_zero.mp hdir).resolve_left hc0
  have hlabel := (D.wall j).label_mem
  rwa [hray, hc, DirectedWallSpaces.wallGroup_rescale _ _ _ _ hc0] at hlabel


/-- The spatial map of the lattice change fixes the origin. -/
@[simp]
theorem pushforward_spatialMap_zero : (pushforward R h hD ν σ hσ hν).spatialMap 0 = 0 := by
  have := finiteIndex_range_change hD
  rw [pushforward_eq_ofFiniteIndex, Pushforward.ofFiniteIndex_spatialMap,
    IsIntegralLattice.coe_extendContinuousAffineEquivOfFiniteIndex, map_zero]

/-- The image of the line `ℝm` under the spatial map of the lattice change passes through the
origin. -/
theorem zero_mem_map_line :
    (0 : ℝ × ℝ) ∈
      (line h m).map (pushforward R h hD ν σ hσ hν).spatialMap.toAffineEquiv.toAffineMap :=
  ⟨0, by simp, by simp⟩

/-- For `m ≠ 0`, the image of the line `ℝm` under the spatial map of the lattice change is an
affine hyperplane. -/
theorem finrank_direction_map_line (hm0 : m ≠ 0) :
    Module.finrank ℝ ((line h m).map
      (pushforward R h hD ν σ hσ hν).spatialMap.toAffineEquiv.toAffineMap).direction + 1 =
      Module.finrank ℝ (ℝ × ℝ) := by
  rw [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap, LinearEquiv.finrank_map_eq,
    finrank_direction_line hm0]

/-- The image of a direction transverse to the line `ℝm` is transverse to its image. -/
theorem linear_notMem_direction_map_line {v : ℝ × ℝ} (hv : h.realCharacter (normal m) v ≠ 0) :
    (pushforward R h hD ν σ hσ hν).spatialMap.toAffineEquiv.linear v ∉ ((line h m).map
      (pushforward R h hD ν σ hσ hν).spatialMap.toAffineEquiv.toAffineMap).direction := by
  rwa [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply, notMem_direction_line_iff]

variable (hm : r • m = p • m₁ + q • m₂)

include hm in
/-- For `r • m = p • m₁ + q • m₂`, the normal `det(·, (p, q))` of `ℓ⁻¹M₀` restricts along
`M ⊆ ℓ⁻¹M₀` to `r` times the normal `det(·, m)` of `M`, over `ℚ`. -/
theorem intCast_normal_apply_change (x : ℤ × ℤ) :
    (normal (p, q) (change m₁ m₂ x) : ℚ) = r * normal m x := by
  exact_mod_cast normal_apply_change hm x

include hν hm in
/-- If `ν` sends the normal `det(·, m)` of `M` to the normal `det(·, (p, q))` of `ℓ⁻¹M₀`, its
comparison scalar is `r`. -/
theorem scalar_normal_eq (hνm : ν (normal m) = normal (p, q)) (hm0 : m ≠ 0) : σ (normal m) = r := by
  have h := hν (normal m) (m.2, -m.1)
  rw [hνm, intCast_normal_apply_change hm] at h
  have hx : (normal m (m.2, -m.1) : ℚ) ≠ 0 := by exact_mod_cast normal_apply_ne_zero hm0
  exact (mul_right_cancel₀ hx h).symm

/-- The filtration of the coefficients tangent to `det(·, m)` over `M`. -/
local notation "F₀" => TropicalVertexCoefficientAction.filtration (R := R) ℕ²
  (tropicalTangentMonoid ℕ² (coord m₁ m₂) (AddMonoidHom.comp (Int.castAddHom R) (normal m)))

/-- The filtration of the coefficients tangent to `det(·, (p, q))` over `ℓ⁻¹M₀`. -/
local notation "F₁" => TropicalVertexCoefficientAction.filtration (R := R) ℕ²
  (tropicalTangentMonoid ℕ² (sublatticeCoord m₁ m₂)
    (AddMonoidHom.comp (Int.castAddHom R) (normal (p, q))))

/-- The tangent monomial map of the identity degree map, from the coefficients tangent to
`det(·, m)` over `M` to those tangent to `det(·, (p, q))` over `ℓ⁻¹M₀`. -/
local notation "Φ" => completedTropicalTangentMap (R := R) (PositiveDegreeMap.id ℕ²)
  (map_tropicalTangentMonoid_intCast_le (PositiveDegreeMap.id ℕ²)
    (sublatticeCoord_id_eq_change_coord m₁ m₂) (intCast_normal_apply_change hm))

/-- The lattice change. -/
local notation "P" => pushforward R h hD ν σ hσ hν

include hm in
/-- **`r`-th powers of wall functions on `ℝm°`.** Let `ν` send `det(·, m)` to `det(·, (p, q))`
and let `m ≠ 0`. If `f₀ = f₁ ^ r` under the tangent monomial map, the lattice change sends the
function-wall label of `f₀` with normal `det(·, m)` over `M` to the function-wall label of `f₁`
with normal `det(·, (p, q))` over `ℓ⁻¹M₀`. -/
theorem pushforward_lieHom_completedMap_label (hνm : ν (normal m) = normal (p, q)) (hm0 : m ≠ 0)
    (f₀ : {u : (F₀).completion // u - 1 ∈ (F₀).completionIdeal 1})
    (f₁ : {u : (F₁).completion // u - 1 ∈ (F₁).completionIdeal 1})
    (hf : Φ f₀ = (f₁ : (F₁).completion) ^ r) :
    (P).lieHom.completedMap (ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (coord m₁ m₂)
        ((Int.castAddHom R).comp (normal m)) ((F₀).completedLog f₀))) =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (sublatticeCoord m₁ m₂)
        ((Int.castAddHom R).comp (normal (p, q))) ((F₁).completedLog f₁)) := by
  have := finiteIndex_range_change hD
  have hr := scalar_normal_eq hν hm hνm hm0
  rw [pushforward_eq_ofFiniteIndex]
  exact Pushforward.ofFiniteIndex_lieHom_completedMap_completedBCHExp_completedLog _ _ _ _ ν σ hσ
    hν (normal m) (fun x => by rw [hr]; exact intCast_normal_apply_change hm x) hr f₀ f₁ hf

include hm in
/-- Let `ν` send `det(·, m)` to `det(·, (p, q))` and let `m ≠ 0`. Every completed tangent series
`f₀` over `M` congruent to one has an `r`-th root `f₁` of its image under the tangent monomial
map, and the lattice change sends the function-wall label of `f₀` to that of `f₁`. -/
theorem exists_pow_eq_and_pushforward_lieHom_completedMap_eq (hνm : ν (normal m) = normal (p, q))
    (hm0 : m ≠ 0) (f₀ : {u : (F₀).completion // u - 1 ∈ (F₀).completionIdeal 1}) :
    ∃ f₁ : {u : (F₁).completion // u - 1 ∈ (F₁).completionIdeal 1},
      Φ f₀ = (f₁ : (F₁).completion) ^ r ∧
      (P).lieHom.completedMap (ℕ².completedBCHExp _ (completedTropicalTangentField ℕ²
          (coord m₁ m₂) ((Int.castAddHom R).comp (normal m)) ((F₀).completedLog f₀))) =
        ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (sublatticeCoord m₁ m₂)
          ((Int.castAddHom R).comp (normal (p, q))) ((F₁).completedLog f₁)) := by
  have := finiteIndex_range_change hD
  have hr := scalar_normal_eq hν hm hνm hm0
  rw [pushforward_eq_ofFiniteIndex]
  exact Pushforward.exists_pow_eq_and_ofFiniteIndex_lieHom_completedMap_eq _ _ _ _ ν σ hσ hν
    (normal m) (fun x => by rw [hr]; exact intCast_normal_apply_change hm x) hr f₀

variable {K : ℕ} (c : Fin 2 × Fin K → R)
  (hline : ∀ i, ν (lineNormal m₁ m₂ i) = sublatticeLineNormal i)
  (hνm : ν (normal m) = normal (p, q))

/-- **Common generic points on `ℝm`.** Let `m ≠ 0`, let `D` be a diagram over `M` and `E` a
diagram over `ℓ⁻¹M₀`. Every open set meeting the line `ℝm` contains a generic point of the line
for `D` whose image under the spatial map of the lattice change is a generic point of the image
line for `E`. -/
theorem exists_isGenericPoint_pair_line (hm0 : m ≠ 0) {κ ι : Type*}
    (D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ)
    (E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ²
      (sublatticeCoord m₁ m₂)) ι)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : (U ∩ line h m).Nonempty) :
    ∃ θ ∈ U ∩ line h m, D.IsGenericPoint (line h m) θ ∧
      E.IsGenericPoint ((line h m).map (P).spatialMap.toAffineEquiv.toAffineMap)
        ((P).spatialMap θ) :=
  D.exists_isGenericPoint_pair E _ _ (finrank_direction_line hm0) hU hne

/-- **Germ labels of the class over `M` along rays of `ℝm`.** Let `m ≠ 0`, let `D` and `D'`
represent the scattering class of the lines over `M`, let `θ` be a generic point of the line `ℝm`
for `D` and `t • θ`, `t > 0`, a generic point of the line for `D'`, and let `v` cross the line.
Then the germ label of `D'` at `t • θ` in the direction `v` is the germ label of `D` at `θ`. -/
theorem germLabel_smul_eq_of_toClass_eq (hm0 : m ≠ 0) {κ κ' : Type}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ}
    (hDc : D.toClass =
      ((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {D' : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ'}
    (hD'c : D'.toClass =
      ((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} {t : ℝ} (ht : 0 < t) (hθ : D.IsGenericPoint (line h m) θ)
    (htθ : D'.IsGenericPoint (line h m) (t • θ)) (hv : h.realCharacter (normal m) v ≠ 0) :
    D'.germLabel (t • θ) v htθ.isRegular = D.germLabel θ v hθ.isRegular :=
  germLabel_smul_eq_of_toClass_eq_scat _ (lineInput_diagram_wall_support _ _ _ _ _ R h c) hDc hD'c
    (by simp) (finrank_direction_line hm0) ht hθ htθ (notMem_direction_line_iff.mpr hv)

include hm hline hνm in
/-- **The wall function over `M` is the `r`-th power of the one over `ℓ⁻¹M₀`, pointwise.** Let `ν`
send the normals of the lines and `det(·, m)` to their normals in `ℓ⁻¹M₀`, and let `m ≠ 0`. Let `D`
represent the scattering class of the lines over `M` and `E` that over `ℓ⁻¹M₀`. Let `θ` be a
generic point of the line `ℝm` for `D` whose image `S θ` under the spatial map is a generic point
of the image line for `E`, and let `v` cross the line. For `f₀ = f₁ ^ r` under the tangent monomial
map, the germ label of `E` at `S θ` in the direction `S v` is the function-wall label of `f₁` with
normal `det(·, (p, q))` exactly when the germ label of `D` at `θ` in the direction `v` is the
function-wall label of `f₀` with normal `det(·, m)`. -/
theorem germLabel_eq_iff_of_toClass_eq (hm0 : m ≠ 0) {κ ι : Type}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ}
    (hDc : D.toClass =
      ((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ²
      (sublatticeCoord m₁ m₂)) ι}
    (hEc : E.toClass =
      ((sublatticeLineInput m₁ m₂ K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (line h m) θ)
    (hθ' : E.IsGenericPoint ((line h m).map (P).spatialMap.toAffineEquiv.toAffineMap)
      ((P).spatialMap θ))
    (hv : h.realCharacter (normal m) v ≠ 0)
    (f₀ : {u : (F₀).completion // u - 1 ∈ (F₀).completionIdeal 1})
    (f₁ : {u : (F₁).completion // u - 1 ∈ (F₁).completionIdeal 1})
    (hf : Φ f₀ = (f₁ : (F₁).completion) ^ r) :
    E.germLabel ((P).spatialMap θ) ((P).spatialMap.toAffineEquiv.linear v) hθ'.isRegular =
        ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (sublatticeCoord m₁ m₂)
          ((Int.castAddHom R).comp (normal (p, q))) ((F₁).completedLog f₁)) ↔
      D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ²
        (coord m₁ m₂) ((Int.castAddHom R).comp (normal m)) ((F₀).completedLog f₀)) := by
  have hDE := (toClass_eq_iff _ _).mp
    ((toClass_pushforward R h hD hσ hν hline c hDc).trans hEc.symm)
  rw [← pushforward_lieHom_completedMap_label hD hσ hν hm hνm hm0 f₀ f₁ hf]
  exact hDE.germLabel_eq_completedMap_iff _
    (pushforward_lieHom_completedMap_injective R h hD ν σ hσ hν) hθ hθ'
    (notMem_direction_line_iff.mpr hv) _

include hm hline hνm in
/-- **A single wall function on each open ray of `ℝm°`.** Let `m₁, m₂` be independent with
`det(m₁, m₂) > 0`, let `p, q ≥ 0` be coprime and `r • m = p • m₁ + q • m₂` with `m` primitive, and
let `ν` send the normals of the lines and `det(·, m)` to their normals in `ℓ⁻¹M₀`. Let `θ` be a
generic point of the line `ℝm` for some representative `D₀` of the scattering class of the lines
over `M` (such points exist in every open set meeting the line), and let `v` cross the line. Then
there are completed tangent series `f₀` over `M` and `f₁` over `ℓ⁻¹M₀`, congruent to one, with
`f₀ = f₁ ^ r` under the tangent monomial map, such that

* every representative `D` of the class over `M` has the germ label `exp(log(f₀) ∂_{det(·, m)})`
  in the direction `v` at every point `t • θ`, `t > 0`, that is generic for `D` on the line;
* every representative `E` of the class over `ℓ⁻¹M₀` has the germ label
  `exp(log(f₁) ∂_{det(·, (p, q))})` in the direction `S v` at every point `t • S θ`, `t > 0`,
  that is generic for `E` on the image line.

The series are not computed. -/
theorem exists_germLabel_smul_eq_of_toClass_eq (hpq : IsCoprime p q) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hmp : TauCeti.IsPrimitive m) {κ₀ : Type}
    {D₀ : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ₀}
    (hD₀ : D₀.toClass =
      ((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D₀.IsGenericPoint (line h m) θ) (hv : h.realCharacter (normal m) v ≠ 0) :
    ∃ (f₀ : {u : (F₀).completion // u - 1 ∈ (F₀).completionIdeal 1})
      (f₁ : {u : (F₁).completion // u - 1 ∈ (F₁).completionIdeal 1}),
      Φ f₀ = (f₁ : (F₁).completion) ^ r ∧
      (∀ {κ : Type}
        {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ},
        D.toClass =
          ((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..) →
        ∀ {t : ℝ} (_ : 0 < t) (htθ : D.IsGenericPoint (line h m) (t • θ)),
          D.germLabel (t • θ) v htθ.isRegular = ℕ².completedBCHExp _
            (completedTropicalTangentField ℕ² (coord m₁ m₂) ((Int.castAddHom R).comp (normal m))
              ((F₀).completedLog f₀))) ∧
      (∀ {ι : Type} {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ²
          (sublatticeCoord m₁ m₂)) ι},
        E.toClass =
          ((sublatticeLineInput m₁ m₂ K).diagram h c).Scat
            (fun _ => ofHyperplaneRayFactors_full ..) →
        ∀ {t : ℝ} (_ : 0 < t) (htθ : E.IsGenericPoint
          ((line h m).map (P).spatialMap.toAffineEquiv.toAffineMap) (t • (P).spatialMap θ)),
          E.germLabel (t • (P).spatialMap θ) ((P).spatialMap.toAffineEquiv.linear v)
              htθ.isRegular =
            ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (sublatticeCoord m₁ m₂)
              ((Int.castAddHom R).comp (normal (p, q))) ((F₁).completedLog f₁))) := by
  /- The germ label of `D₀` at `θ` lies in the wall group of the ray `(p, q)`, hence is the
  function-wall label of some `f₀`, and its pushforward is that of an `r`-th root `f₁`. Over `M`,
  the germ label of the class is constant along the open ray of `θ`. Over `ℓ⁻¹M₀`, the pushforward
  of `D₀` represents the class and has the germ label of `f₁` at `S θ`, and the germ label of the
  class is constant along the open ray of `S θ`. -/
  obtain ⟨f₀, hf₀⟩ :=
    exists_eq_completedBCHExp_completedTropicalTangentField_completedLog_of_mem_wallGroup
      (D₀.germLabel_mem_wallGroup θ v hθ.isRegular fun _ j hj =>
        label_mem_wallGroup_of_isGenericPoint hD.ne' hpq hp hq hm hmp hθ j hj)
  obtain ⟨f₁, hf, hP⟩ :=
    exists_pow_eq_and_pushforward_lieHom_completedMap_eq (h := h) hD hσ hν hm hνm hmp.ne_zero f₀
  refine ⟨f₀, f₁, hf, fun hDc t ht htθ => ?_, fun hEc t ht htθ => ?_⟩
  · rw [germLabel_smul_eq_of_toClass_eq hD c hmp.ne_zero hD₀ hDc ht hθ htθ hv, ← hf₀]
  · rw [germLabel_smul_eq_of_toClass_eq_scat _ (lineInput_diagram_wall_support _ _ _ _ _ R h c)
      (toClass_pushforward R h hD hσ hν hline c hD₀) hEc (zero_mem_map_line hD hσ hν)
      (finrank_direction_map_line hD hσ hν hmp.ne_zero) ht (hθ.pushforward (P)) htθ
      (linear_notMem_direction_map_line hD hσ hν hv), D₀.germLabel_pushforward (P) v hθ.isRegular]
    exact (congrArg (P).lieHom.completedMap hf₀).symm.trans hP

include hm hline hνm in
/-- **The wall function over `M` is the `r`-th power of the one over `ℓ⁻¹M₀`.** Let `m₁, m₂` be
independent with `det(m₁, m₂) > 0`, let `p, q ≥ 0` be coprime and `r • m = p • m₁ + q • m₂` with
`m` primitive, and let `ν` send the normals of the lines and `det(·, m)` to their normals in
`ℓ⁻¹M₀`. Let `D` be any representative of the scattering class of the lines over `M` and `E` any
representative over `ℓ⁻¹M₀`, let `θ` be a generic point of the line `ℝm` for `D` whose image `S θ`
under the spatial map is a generic point of the image line for `E` (such points exist in every
open set meeting the line, `DirectedDiagram.exists_isGenericPoint_pair`), and let `v` cross the
line. Then there are completed tangent series `f₀` over `M` and `f₁` over `ℓ⁻¹M₀`, congruent to
one, with `f₀ = f₁ ^ r` under the tangent monomial map, such that the germ label of `D` at `θ` in
the direction `v` is the function-wall label of `f₀` with normal `det(·, m)` and the germ label of
`E` at `S θ` in the direction `S v` is the function-wall label of `f₁` with normal
`det(·, (p, q))`. The series are not computed. -/
theorem exists_germLabel_eq_of_toClass_eq (hpq : IsCoprime p q) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hmp : TauCeti.IsPrimitive m) {κ ι : Type}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² (coord m₁ m₂)) κ}
    (hDc : D.toClass =
      ((latticeLineInput hD K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ²
      (sublatticeCoord m₁ m₂)) ι}
    (hEc : E.toClass =
      ((sublatticeLineInput m₁ m₂ K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    {θ v : ℝ × ℝ} (hθ : D.IsGenericPoint (line h m) θ)
    (hθ' : E.IsGenericPoint ((line h m).map (P).spatialMap.toAffineEquiv.toAffineMap)
      ((P).spatialMap θ))
    (hv : h.realCharacter (normal m) v ≠ 0) :
    ∃ (f₀ : {u : (F₀).completion // u - 1 ∈ (F₀).completionIdeal 1})
      (f₁ : {u : (F₁).completion // u - 1 ∈ (F₁).completionIdeal 1}),
      Φ f₀ = (f₁ : (F₁).completion) ^ r ∧
      D.germLabel θ v hθ.isRegular = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ²
        (coord m₁ m₂) ((Int.castAddHom R).comp (normal m)) ((F₀).completedLog f₀)) ∧
      E.germLabel ((P).spatialMap θ) ((P).spatialMap.toAffineEquiv.linear v) hθ'.isRegular =
        ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² (sublatticeCoord m₁ m₂)
          ((Int.castAddHom R).comp (normal (p, q))) ((F₁).completedLog f₁)) := by
  obtain ⟨f₀, f₁, hf, hD', hE'⟩ :=
    exists_germLabel_smul_eq_of_toClass_eq hD hσ hν hm c hline hνm hpq hp hq hmp hDc hθ hv
  refine ⟨f₀, f₁, hf, ?_, ?_⟩
  · have h₁ := hD' hDc one_pos (by rwa [one_smul])
    simp only [one_smul] at h₁
    exact h₁
  · have h₁ := hE' hEc one_pos (by rwa [one_smul])
    simp only [one_smul] at h₁
    exact h₁

end GermLabel

end Mei.RankTwoLatticeChange
