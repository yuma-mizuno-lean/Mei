/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing.WallFunction.Examples
public import Mei.Geometry.ScatteringDiagram.HyperplaneTermInput.FiniteIndex

/-!
# The incoming lines of the lattice change for `m₁ = (1, 0)` and `m₂ = (1, 2)`

Let `M = ℤ²`, let `M₀ ⊆ M` be spanned by `m₁ = (1, 0)` and `m₂ = (1, 2)`, of index `ℓ = 2`, and
use the coordinates of `Mei.DirectedWall.LatticeChange.Examples`: the coefficient exponent
`(a, b) ∈ ℕ²` of `x^{a m₁ + b m₂}` has coordinates `latticeCoord (a, b) = (a + b, 2b)` in `M` and
`halfLatticeCoord (a, b) = (2a, 2b)` in `½M₀`, with basis `½m₁, ½m₂`, and `M ⊆ ½M₀` is
`latticeChange (x, y) = (2x - y, y)`.

The incoming lines `ℝm₁` and `ℝm₂` carry the functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}`
(`lineInput`). Over `M` they are cooriented by the normals `e₂*` and `2e₁* - e₂*`
(`latticeLineInput`); over `½M₀` by the normals `e₂*` and `e₁*` (`halfLatticeLineInput`). Both
normals of `M` are restrictions of the normals of `½M₀`, so the comparison scalar is one on
them (`primitiveLatticeChangeNormal_lineNormal`, `primitiveLatticeChangeScalar_lineNormal`).

The normal map `primitiveLatticeChangeNormal` sends `μ` to the integral character `μ ∘ t⁻¹` of
`½M₀` when it exists, that is when `μ (1, 0)` is even, and to `μ ∘ latticeCoord`, with
comparison scalar `2`, otherwise; for instance it keeps the normal `x - y` of the diagonal. It
gives the finite-index pushforward `primitiveLatticeChangePushforward`, which sends the input
over `M` to the input over `½M₀` (`latticeLineInput_map`). Hence its pushforward of the ray
presentation over `M` is equivalent to the ray presentation over `½M₀`
(`latticeLineInput_pushforward_equivalent`), and it carries the scattering class over `M` to the
scattering class over `½M₀` (`latticeLineInput_pushforward_scat`), so it sends representatives
of the first class to representatives of the second (`latticeLineInput_toClass_pushforward`).

The normal `n° = x - y` of the diagonal `ℝ(1, 1)`, along `m° = m₁ + m₂ = 2 • (1, 1)`, is kept
with comparison scalar `r = 2`. So if a diagram over `M` has a function-wall grouping whose
normals stay primitive under `primitiveLatticeChangeNormal`, and one of its groups has the label
of `(1 + a z^{(1,1)})²` with normal `n°`, then the pushed group has the label of `1 + a z^{(1,1)}`
with normal `n°` over `½M₀` (`diagonal_label_pushforward`); the grouping and the label are
hypotheses. If the diagram over `M` represents the scattering class over `M`, the same label is
carried by any representative of the scattering class over `½M₀` on a group whose crossing
germs at every order are the images of crossing germs of the diagonal group
(`diagonal_label_of_toClass_eq`); these crossing germs are hypotheses. This uses
`DirectedDiagram.FunctionWallGrouping.label_eq_of_equivalent_pushforward_ofFiniteIndex`.

So for this lattice the file proves: the pushforward of the ray presentation of the lines, the
pushforward of their scattering class and of its representatives, the transport of a given
function-wall label on the diagonal, and its comparison with groups of representatives over
`½M₀` that are matched with it by crossing germs. It does not compute the scattering class, and
it does not prove that matched crossing germs exist.

The lattice change is motivated by Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.HyperplaneTermInput.FiniteIndex.Examples

open DirectedWall DirectedDiagram TauCeti.Toric DirectedWall.LatticeChange.Examples

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The normal map of `M ⊆ ½M₀` sending `μ` to `μ ∘ latticeChange⁻¹` when `μ (1, 0)` is even, and
to `μ ∘ latticeCoord` otherwise. -/
def primitiveLatticeChangeNormal (μ : ℤ × ℤ →+ ℤ) : ℤ × ℤ →+ ℤ :=
  if Even (μ (1, 0)) then
    (μ (1, 0) / 2) • (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ) +
      μ (0, 1) • AddMonoidHom.snd ℤ ℤ
  else latticeChangeNormal μ

/-- The comparison scalar of `primitiveLatticeChangeNormal`: `1` when `μ (1, 0)` is even and `2`
otherwise. -/
def primitiveLatticeChangeScalar (μ : ℤ × ℤ →+ ℤ) : ℚ := if Even (μ (1, 0)) then 1 else 2

/-- For even `μ (1, 0)`, the normal is `(x, y) ↦ (μ (1, 0) / 2) (x + y) + μ (0, 1) y`. -/
theorem primitiveLatticeChangeNormal_apply_of_even {μ : ℤ × ℤ →+ ℤ} (hμ : Even (μ (1, 0)))
    (x : ℤ × ℤ) :
    primitiveLatticeChangeNormal μ x = μ (1, 0) / 2 * (x.1 + x.2) + μ (0, 1) * x.2 := by
  simp [primitiveLatticeChangeNormal, hμ, mul_add]

/-- For odd `μ (1, 0)`, the normal is `μ ∘ latticeCoord`. -/
theorem primitiveLatticeChangeNormal_of_not_even {μ : ℤ × ℤ →+ ℤ} (hμ : ¬Even (μ (1, 0))) :
    primitiveLatticeChangeNormal μ = latticeChangeNormal μ := by
  simp [primitiveLatticeChangeNormal, hμ]

/-- For even `μ (1, 0)`, the comparison scalar is `1`. -/
theorem primitiveLatticeChangeScalar_of_even {μ : ℤ × ℤ →+ ℤ} (hμ : Even (μ (1, 0))) :
    primitiveLatticeChangeScalar μ = 1 := by
  simp [primitiveLatticeChangeScalar, hμ]

/-- For odd `μ (1, 0)`, the comparison scalar is `2`. -/
theorem primitiveLatticeChangeScalar_of_not_even {μ : ℤ × ℤ →+ ℤ} (hμ : ¬Even (μ (1, 0))) :
    primitiveLatticeChangeScalar μ = 2 := by
  simp [primitiveLatticeChangeScalar, hμ]

/-- The comparison scalars are positive. -/
theorem primitiveLatticeChangeScalar_pos (μ : ℤ × ℤ →+ ℤ) : 0 < primitiveLatticeChangeScalar μ := by
  by_cases hμ : Even (μ (1, 0))
  · rw [primitiveLatticeChangeScalar_of_even hμ]
    exact one_pos
  · rw [primitiveLatticeChangeScalar_of_not_even hμ]
    exact two_pos

/-- The normal map pulls back along `latticeChange` to the comparison scalar times the
original normal. -/
theorem primitiveLatticeChangeNormal_apply_latticeChange (μ : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    (primitiveLatticeChangeNormal μ (latticeChange x) : ℚ) =
      primitiveLatticeChangeScalar μ * μ x := by
  by_cases hμ : Even (μ (1, 0))
  · obtain ⟨k, hk⟩ := hμ
    have hμx : μ x = x.1 * μ (1, 0) + x.2 * μ (0, 1) := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_zsmul, ← map_zsmul, ← map_add]
      congr 1
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, and_self]
    have hx : primitiveLatticeChangeNormal μ (latticeChange x) = μ x := by
      rw [primitiveLatticeChangeNormal_apply_of_even ⟨k, hk⟩, hμx, hk, latticeChange_apply,
        show (k + k) / 2 = k by omega]
      ring
    rw [hx, primitiveLatticeChangeScalar_of_even ⟨k, hk⟩, one_mul]
  · rw [primitiveLatticeChangeNormal_of_not_even hμ, primitiveLatticeChangeScalar_of_not_even hμ]
    exact latticeChangeNormal_apply_latticeChange μ x

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The finite-index pushforward along `M ⊆ ½M₀`, with identity degree map and normal map
`primitiveLatticeChangeNormal`. -/
def primitiveLatticeChangePushforward :
    Pushforward ℕ² ℕ² h h (tropicalVertexWallSpaces (R := R) ℕ² latticeCoord)
      (tropicalVertexWallSpaces ℕ² halfLatticeCoord) :=
  Pushforward.ofFiniteIndex (PositiveDegreeMap.id ℕ²) latticeChange latticeChange_injective
    halfLatticeCoord_eq_latticeChange primitiveLatticeChangeNormal primitiveLatticeChangeScalar
    primitiveLatticeChangeScalar_pos primitiveLatticeChangeNormal_apply_latticeChange

/-- The degree map of `primitiveLatticeChangePushforward` is the identity. -/
@[simp]
theorem primitiveLatticeChangePushforward_degreeMap_apply (x : ℤ × ℤ) :
    (primitiveLatticeChangePushforward R h).degreeMap x = x := by
  simp [primitiveLatticeChangePushforward]

/-- The normal map of `primitiveLatticeChangePushforward` is `primitiveLatticeChangeNormal`. -/
@[simp]
theorem primitiveLatticeChangePushforward_normalMap (μ : ℤ × ℤ →+ ℤ) :
    (primitiveLatticeChangePushforward R h).normalMap μ = primitiveLatticeChangeNormal μ := by
  simp [primitiveLatticeChangePushforward]

/-- The coefficient exponents `(k + 1) • e_i` of `x^{(k+1) m_i}` are allowed degrees. -/
theorem succ_smul_finTwoProd_mem (i : Fin 2) (k : ℕ) :
    ((k : ℤ) + 1) • Module.Basis.finTwoProd ℤ i ∈ ℕ².monoid := by
  rw [Module.Basis.mem_positiveDegrees_monoid]
  intro j
  rw [map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (by rw [Finsupp.single_apply]; split_ifs <;> simp)

/-- The coefficient exponents `(k + 1) • e_i` of `x^{(k+1) m_i}` are nonzero. -/
theorem succ_smul_finTwoProd_ne_zero (i : Fin 2) (k : ℕ) :
    ((k : ℤ) + 1) • Module.Basis.finTwoProd ℤ i ≠ 0 :=
  smul_ne_zero (by positivity) ((Module.Basis.finTwoProd ℤ).ne_zero i)

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
  exponent_mem α := succ_smul_finTwoProd_mem α.1 α.2
  exponent_ne_zero α := succ_smul_finTwoProd_ne_zero α.1 α.2
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

end LineInput

/-- The normals `e₂*` of `ℝm₁` and `2e₁* - e₂*` of `ℝm₂` in `M`. -/
def lineNormal : Fin 2 → ℤ × ℤ →+ ℤ :=
  ![AddMonoidHom.snd ℤ ℤ, (2 : ℤ) • AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ]

/-- The normals `e₂*` of `ℝm₁` and `e₁*` of `ℝm₂` in `½M₀`. -/
def halfLineNormal : Fin 2 → ℤ × ℤ →+ ℤ := ![AddMonoidHom.snd ℤ ℤ, AddMonoidHom.fst ℤ ℤ]

/-- The normal of `ℝm₁` in `M` is `e₂*`. -/
@[simp]
theorem lineNormal_zero : lineNormal 0 = AddMonoidHom.snd ℤ ℤ := by
  simp [lineNormal]

/-- The normal of `ℝm₂` in `M` is `2e₁* - e₂*`. -/
@[simp]
theorem lineNormal_one :
    lineNormal 1 = (2 : ℤ) • AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ := by
  simp [lineNormal]

/-- The normal of `ℝm₁` in `½M₀` is `e₂*`. -/
@[simp]
theorem halfLineNormal_zero : halfLineNormal 0 = AddMonoidHom.snd ℤ ℤ := by
  simp [halfLineNormal]

/-- The normal of `ℝm₂` in `½M₀` is `e₁*`. -/
@[simp]
theorem halfLineNormal_one : halfLineNormal 1 = AddMonoidHom.fst ℤ ℤ := by
  simp [halfLineNormal]

/-- The normals of `M` are nonzero. -/
theorem lineNormal_ne_zero (i : Fin 2) : lineNormal i ≠ 0 := fun h0 => by
  fin_cases i <;> simpa using DFunLike.congr_fun h0 (0, 1)

/-- The normals of `½M₀` are nonzero. -/
theorem halfLineNormal_ne_zero (i : Fin 2) : halfLineNormal i ≠ 0 := fun h0 => by
  fin_cases i
  · simpa using DFunLike.congr_fun h0 (0, 1)
  · simpa using DFunLike.congr_fun h0 (1, 0)

/-- The normal of `ℝm_i` in `M` vanishes on `m_i`. -/
theorem lineNormal_latticeCoord (i : Fin 2) :
    lineNormal i (latticeCoord (Module.Basis.finTwoProd ℤ i)) = 0 := by
  fin_cases i <;> simp

/-- The normal of `ℝm_i` in `½M₀` vanishes on `m_i`. -/
theorem halfLineNormal_halfLatticeCoord (i : Fin 2) :
    halfLineNormal i (halfLatticeCoord (Module.Basis.finTwoProd ℤ i)) = 0 := by
  fin_cases i <;> simp

/-- The incoming lines `ℝm₁` and `ℝm₂` over `M`, with the normals `lineNormal`. -/
abbrev latticeLineInput (K : ℕ) : HyperplaneTermInput ℕ² latticeCoord (Fin 2) (Fin 2 × Fin K) :=
  lineInput latticeCoord lineNormal lineNormal_ne_zero lineNormal_latticeCoord K

/-- The incoming lines `ℝm₁` and `ℝm₂` over `½M₀`, with the normals `halfLineNormal`. -/
abbrev halfLatticeLineInput (K : ℕ) :
    HyperplaneTermInput ℕ² halfLatticeCoord (Fin 2) (Fin 2 × Fin K) :=
  lineInput halfLatticeCoord halfLineNormal halfLineNormal_ne_zero
    halfLineNormal_halfLatticeCoord K

/-- The normals of the lines `ℝm_i` over `M` have comparison scalar one. -/
theorem primitiveLatticeChangeScalar_lineNormal (K : ℕ) (i : Fin 2) :
    primitiveLatticeChangeScalar ((latticeLineInput K).normal i) = 1 := by
  rw [lineInput_normal]
  fin_cases i <;> simp [primitiveLatticeChangeScalar]

/-- The normal map sends the normals of the lines in `M` to their normals in `½M₀`. -/
theorem primitiveLatticeChangeNormal_lineNormal (i : Fin 2) :
    primitiveLatticeChangeNormal (lineNormal i) = halfLineNormal i := by
  ext x
  have he : Even (lineNormal i (1, 0)) := by fin_cases i <;> simp
  rw [primitiveLatticeChangeNormal_apply_of_even he]
  fin_cases i <;> simp

/-- The input over `M` mapped along `latticeChange` with the normals
`primitiveLatticeChangeNormal` is the input over `½M₀`. -/
theorem latticeLineInput_map (K : ℕ) :
    (latticeLineInput K).map (PositiveDegreeMap.id ℕ²) latticeChange
        halfLatticeCoord_eq_latticeChange
        (fun i => primitiveLatticeChangeNormal ((latticeLineInput K).normal i))
        ((latticeLineInput K).comp_normal_of_ofFiniteIndex latticeChange
          primitiveLatticeChangeNormal_apply_latticeChange
          (primitiveLatticeChangeScalar_lineNormal K)) =
      halfLatticeLineInput K :=
  HyperplaneTermInput.ext (funext fun i => by simp [primitiveLatticeChangeNormal_lineNormal])
    (by simp) (by simp) (funext fun α => by simp)

variable {K : ℕ} (c : Fin 2 × Fin K → R)

/-- **Incoming lines under the lattice change.** The pushforward along `M ⊆ ½M₀` of the ray
presentation of the lines `ℝm_i` with functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}` over `M` is
equivalent to the ray presentation of the same lines and functions over `½M₀`. -/
theorem latticeLineInput_pushforward_equivalent :
    (((latticeLineInput K).diagram h c).pushforward
      (primitiveLatticeChangePushforward R h)).Equivalent
        ((halfLatticeLineInput K).diagram h c) := by
  rw [← latticeLineInput_map]
  exact (latticeLineInput K).diagram_pushforward_ofFiniteIndex_equivalent _ _
    latticeChange_injective halfLatticeCoord_eq_latticeChange primitiveLatticeChangeScalar_pos _
    (primitiveLatticeChangeScalar_lineNormal K) h h c

/-- **Scattering classes under the lattice change.** The pushforward along `M ⊆ ½M₀` of the
scattering class of the lines `ℝm_i` with functions `1 + ∑_{k < K} c_{i,k} x^{(k+1) m_i}` over
`M` is the scattering class of the same lines and functions over `½M₀`. -/
theorem latticeLineInput_pushforward_scat :
    Class.pushforward (primitiveLatticeChangePushforward R h)
        (((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..) :=
  ((latticeLineInput K).diagram h c |>.pushforward_scat _ _).trans
    (DirectedDiagram.scat_eq_of_equivalent _ _ (latticeLineInput_pushforward_equivalent R h c))

/-- A diagram representing the scattering class of the lines over `M` is pushed along `M ⊆ ½M₀`
to a diagram representing the scattering class of the lines over `½M₀`. -/
theorem latticeLineInput_toClass_pushforward {κ : Type}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := R) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..)) :
    (D.pushforward (primitiveLatticeChangePushforward R h)).toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..) := by
  rw [← latticeLineInput_map]
  exact (latticeLineInput K).toClass_pushforward_ofFiniteIndex _ _ latticeChange_injective
    halfLatticeCoord_eq_latticeChange primitiveLatticeChangeScalar_pos _
    (primitiveLatticeChangeScalar_lineNormal K) h h c hD

/-- The normal map keeps the normal `n°(x, y) = x - y` of the diagonal. -/
@[simp]
theorem primitiveLatticeChangeNormal_diagonalNormal :
    primitiveLatticeChangeNormal diagonalNormal = diagonalNormal := by
  rw [primitiveLatticeChangeNormal_of_not_even (by simp), latticeChangeNormal_diagonalNormal]

/-- The normal `n°` of the diagonal has comparison scalar `r = 2`. -/
@[simp]
theorem primitiveLatticeChangeScalar_diagonalNormal :
    primitiveLatticeChangeScalar diagonalNormal = 2 :=
  primitiveLatticeChangeScalar_of_not_even (by simp)

local notation "F" ρ₀ => TropicalVertexCoefficientAction.filtration (R := ℚ) ℕ²
  (tropicalTangentMonoid ℕ² ρ₀ (AddMonoidHom.comp (Int.castAddHom ℚ) diagonalNormal))

/-- **Transport of a diagonal group label.** Let a diagram over `M` have a function-wall
grouping whose normals stay primitive under `primitiveLatticeChangeNormal`, and let its group
`g` have the function-wall label of `(1 + a z^{(1,1)})²` with normal `n°`. Then the group `g` of
the pushforward along `M ⊆ ½M₀` has the function-wall label of `1 + a z^{(1,1)}` with normal
`n°`. -/
theorem diagonal_label_pushforward {κ M κ' : Type*} [AddCommGroup M] {π : ℤ × ℤ →+ M}
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (G : D.FunctionWallGrouping π κ')
    (hprim : ∀ j, TauCeti.IsPrimitive (primitiveLatticeChangeNormal (D.wall j).normal))
    {g : κ'} (a : ℚ)
    (hg : G.label g = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
      ((Int.castAddHom ℚ).comp diagonalNormal)
      ((F latticeCoord).completedLog (squaredDiagonalFunction a)))) :
    (G.pushforward (P := primitiveLatticeChangePushforward ℚ h) (π' := π)
        (fun x _ => by rw [primitiveLatticeChangePushforward_degreeMap_apply])
        (fun j => by simpa using hprim j)).label g =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) :=
  FunctionWallGrouping.label_pushforward_ofFiniteIndex _ _ latticeChange_injective
    halfLatticeCoord_eq_latticeChange primitiveLatticeChangeNormal primitiveLatticeChangeScalar
    primitiveLatticeChangeScalar_pos primitiveLatticeChangeNormal_apply_latticeChange G
    (fun x => by
      rw [primitiveLatticeChangeScalar_diagonalNormal]
      exact diagonalNormal_latticeChange x)
    (r := 2) (by simp) _ _ _ _ hg (completedTropicalTangentMap_squaredDiagonalFunction _ a)

/-- **The diagonal label in matched representatives over `½M₀`.** Let `D` represent the scattering
class of the lines over `M`, with a function-wall grouping whose normals stay primitive under
`primitiveLatticeChangeNormal`, and let its group `g` have the function-wall label of
`(1 + a z^{(1,1)})²` with normal `n°`. Let `E` be any representative of the scattering class of
the lines over `½M₀`, with a function-wall grouping `G'`. Suppose that at every order `k` the
group `g` has a crossing germ at order `k` (the cutoff modulus is the identity), at a point `θ`
and a direction `v`, and that the group `g'` of `G'` has a crossing germ at order `k` at their
images under the spatial map. Then `g'` has the function-wall label of `1 + a z^{(1,1)}` with
normal `n°`. -/
theorem diagonal_label_of_toClass_eq {κ M κ' ι' M' κ'' : Type} [AddCommGroup M]
    [AddCommGroup M'] {π : ℤ × ℤ →+ M} {π' : ℤ × ℤ →+ M'} (c : Fin 2 × Fin K → ℚ)
    {D : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² latticeCoord) κ}
    (hD : D.toClass =
      ((latticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    (G : D.FunctionWallGrouping π κ')
    (hprim : ∀ j, TauCeti.IsPrimitive (primitiveLatticeChangeNormal (D.wall j).normal))
    {g : κ'} (a : ℚ)
    (hg : G.label g = ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² latticeCoord
      ((Int.castAddHom ℚ).comp diagonalNormal)
      ((F latticeCoord).completedLog (squaredDiagonalFunction a))))
    {E : DirectedDiagram (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² halfLatticeCoord) ι'}
    (hE : E.toClass =
      ((halfLatticeLineInput K).diagram h c).Scat (fun _ => ofHyperplaneRayFactors_full ..))
    (G' : E.FunctionWallGrouping π' κ'') {g' : κ''}
    (hgerm : ∀ k, ∃ θ v, G.IsCrossingGerm g k θ v ∧
      G'.IsCrossingGerm g' k ((primitiveLatticeChangePushforward ℚ h).spatialMap θ)
        ((primitiveLatticeChangePushforward ℚ h).spatialMap.toAffineEquiv.linear v)) :
    G'.label g' =
      ℕ².completedBCHExp _ (completedTropicalTangentField ℕ² halfLatticeCoord
        ((Int.castAddHom ℚ).comp diagonalNormal) ((F halfLatticeCoord).completedLog
          (diagonalFunction halfLatticeCoord diagonalNormal_halfLatticeCoord a))) :=
  FunctionWallGrouping.label_eq_of_equivalent_pushforward_ofFiniteIndex _ _
    latticeChange_injective halfLatticeCoord_eq_latticeChange primitiveLatticeChangeNormal
    primitiveLatticeChangeScalar primitiveLatticeChangeScalar_pos
    primitiveLatticeChangeNormal_apply_latticeChange G
    (fun x => by
      rw [primitiveLatticeChangeScalar_diagonalNormal]
      exact diagonalNormal_latticeChange x)
    (r := 2) (by simp) (π' := π) (fun x _ => by simp)
    (fun j => by simpa using hprim j) _ _ hg
    (completedTropicalTangentMap_squaredDiagonalFunction _ a)
    ((toClass_eq_iff _ _).mp ((latticeLineInput_toClass_pushforward ℚ h c hD).trans hE.symm)) G'
    fun k => by
      obtain ⟨θ, v, hθ, hθ'⟩ := hgerm k
      exact ⟨θ, v, by rwa [PositiveDegreeMap.id_modulus], hθ'⟩

end Mei.HyperplaneTermInput.FiniteIndex.Examples
