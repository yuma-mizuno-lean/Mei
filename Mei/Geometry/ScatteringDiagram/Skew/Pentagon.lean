/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Coefficient
public import Mei.Geometry.ScatteringDiagram.Skew.Dilogarithm

/-!
# The pentagon identity for dilogarithm elements

Let `n₁, n₂` be nonzero positive degrees of a skew lattice datum and `c` a rational number
with `c {n₁, n₂} = 1` that is an integer multiple of the ray indices `κ(n₁)` and `κ(n₂)`.
Writing `Ψ[n]^c` for the ray label `rayExp (c • negDilogNeg R)` of degree `n`, the completed
skew group satisfies the pentagon identity
`Ψ[n₂]^c Ψ[n₁]^c = Ψ[n₁]^c Ψ[n₁ + n₂]^c Ψ[n₂]^c`.
For `c > 0` the left side is antiordered and the right side ordered, since
`{n₂, n₁} < 0` and `{n₁, n₁ + n₂} = {n₁ + n₂, n₂} = {n₁, n₂} > 0`. This is the elementary
exchange of out-of-order dilogarithm factors in rank two. No nondegeneracy of the skew form
is assumed.

## Main statements

* `Mei.SkewLatticeDatum.rayExp_smul_negDilogNeg_pentagon`: the pentagon identity for the
  normalized powers `Ψ[n]^c`.
* `Mei.SkewLatticeDatum.dilogElement_pentagon`: if `n₁, n₂ ∈ N°` and `{n₁, n₂} = 1`, then
  `Ψ[n₂] Ψ[n₁] = Ψ[n₁] Ψ[n₁ + n₂] Ψ[n₂]`.

## Implementation notes

Both sides are compared through the faithful action on the principal coefficient completion
(`eq_of_completedBCHAction_completedMap_single_eq`). There `Ψ[n]^c` multiplies a monomial
`z^p` by an integer power of the binomial `1 + z^{r(n)}`
(`completedBCHAction_completedMap_rayExp_smul_negDilogNeg`). With `x = z^{r(n₁)}` and
`y = z^{r(n₂)}`, both sides multiply `z^p` by `(1 + x + xy)^a (1 + y)^b`, where `a` and `b`
are the normal exponents of `p`.

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5,
  arXiv:2111.00800v6; its ordering of products is the reverse of the one used here.
* Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1,
  arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open _root_.AddMonoidAlgebra PowerSeries
open scoped Mei.TropicalVertexCoefficientAction PrincipalCoefficientAction

variable {N R : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [CommRing R] [Algebra ℚ R] (D : SkewLatticeDatum N) (d : PositiveDegrees D.unfrozen)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "e" => D.principalPositiveDegrees d
local notation "ℳ" => tropicalVertexGrading (R := R) e (AddMonoidHom.id Lpr)
local notation "β" => D.coefficientForm R
local notation "hβ" => D.isAlt_coefficientForm R
local notation "𝓛" => SkewLieAlgebra.positiveGrading β hβ d
local notation "Qpr" => D.principalCoefficientMonoid d
local notation "Fpr" => TropicalVertexCoefficientAction.filtration (R := R) e Qpr
local notation "κ" => D.sublattice.toAddSubgroup.rayIndex
local notation "Ψ" => SkewLieAlgebra.rayExp β hβ

omit [Algebra ℚ R] in
/-- An algebra automorphism maps an integer power of a unit to the same power of its
image unit. -/
private theorem algEquiv_coe_zpow {K : Type*} [CommRing K] [Algebra R K] (φ : K ≃ₐ[R] K)
    (U : Kˣ) (k : ℤ) : φ ↑(U ^ k) = ↑(Units.map (φ : K →* K) U ^ k) := by
  rw [← map_zpow, Units.coe_map]
  rfl

/-- The unit identity behind the pentagon: if `U₁ = 1 + x`, `U₂ = 1 + y`,
`V = 1 + U₂ x`, `P = 1 + U₁⁻¹ x y` and `W = 1 + P⁻¹ U₁⁻¹ y`, then `V = P U₁` and
`U₂ = W P`, so `V^a U₂^b z = W^b P^(a + b) U₁^a z`. -/
private theorem pentagon_units {K : Type*} [CommRing K] {x y w : K} {U₁ U₂ V P W : Kˣ}
    (hU₁ : (U₁ : K) = 1 + x) (hU₂ : (U₂ : K) = 1 + y) (hw : w = x * y)
    (hV : (V : K) = 1 + ↑(U₂ ^ (1 : ℤ)) * x) (hP : (P : K) = 1 + ↑(U₁ ^ (-1 : ℤ)) * w)
    (hW : (W : K) = 1 + ↑(P ^ (-1 : ℤ)) * (↑(U₁ ^ (-1 : ℤ)) * y)) (a b : ℤ) (z : K) :
    ↑(V ^ a) * (↑(U₂ ^ b) * z) = ↑(W ^ b) * (↑(P ^ (a + b)) * (↑(U₁ ^ a) * z)) := by
  subst hw
  simp only [zpow_one] at hV
  simp only [zpow_neg_one] at hP hW
  have h₁ := U₁.inv_mul
  have hP' := P.inv_mul
  have hVP : V = P * U₁ := by
    apply Units.ext
    rw [Units.val_mul, hV, hP, hU₂]
    linear_combination (-(x * y)) * h₁ - hU₁
  have hWP : U₂ = W * P := by
    apply Units.ext
    rw [Units.val_mul, hW, hU₂]
    linear_combination (-(↑U₁⁻¹ * y)) * hP' - hP - y * h₁ + (↑U₁⁻¹ * y) * hU₁
  have key : V ^ a * U₂ ^ b = W ^ b * P ^ (a + b) * U₁ ^ a := by
    rw [hVP, hWP, mul_zpow, mul_zpow, zpow_add]
    simp only [mul_assoc, mul_comm]
  simpa only [Units.val_mul, mul_assoc] using congrArg (fun u : Kˣ => (u : K) * z) key

/-- The normalized principal normal `s κ(n) νₙ` evaluates to `c {m, n}` on the principal
exponent of `m`, when `s κ(n) = c`. -/
private theorem zsmul_principalNormal_principalEmbedding {n m : D.unfrozen} {c : ℚ} {s k : ℤ}
    (h : s * κ n = c) (hk : c * D.form m n = k) :
    s * D.principalNormal n (D.principalEmbedding m) = k := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, cast_principalNormal_principalEmbedding, ← hk, ← h, mul_assoc]

omit [Module.Free ℤ N] [Algebra ℚ R] in
/-- A principal coefficient monomial of nonzero unfrozen degree is congruent to `0`, so
`1 + z^q` is a unit of the principal coefficient completion. -/
private theorem exists_units_eq_one_add_single (q : Qpr) (hq : q.val.2 ≠ 0) :
    ∃ U : (Fpr).completionˣ, (U : (Fpr).completion) = 1 + (Fpr).toCompletion (single q 1) := by
  have hmem : (Fpr).toCompletion (single q 1) ∈ (Fpr).completionIdeal 1 := by
    rw [AlgFiltration.toCompletion_mem_completionIdeal_iff,
      mem_principalCoefficientFiltration_ideal_iff]
    intro p hp
    have hpq : p = q := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hp) (by simp [Ne.symm h])
    rw [hpq]
    have := d.degree_pos ((D.mem_principalCoefficientMonoid d _).mp q.property) hq
    omega
  exact ⟨((Fpr).isUnit_of_sub_one_mem (by simpa using hmem)).unit, IsUnit.unit_spec _⟩

variable [DecidableEq D.unfrozen]

/-- **Pentagon identity.** Let `n₁, n₂` be nonzero positive degrees and `c` a rational
number with `c {n₁, n₂} = 1` that is an integer multiple of `κ(n₁)` and of `κ(n₂)`.
Then the ray labels `Ψ[n]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` satisfy
`Ψ[n₂]^c Ψ[n₁]^c = Ψ[n₁]^c Ψ[n₁ + n₂]^c Ψ[n₂]^c`. -/
theorem rayExp_smul_negDilogNeg_pentagon {n₁ n₂ : D.unfrozen} (hn₁ : n₁ ∈ d.monoid)
    (hn₂ : n₂ ∈ d.monoid) (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0) {c : ℚ}
    (hc : c * D.form n₁ n₂ = 1) {s₁ s₂ : ℤ} (h₁ : s₁ * κ n₁ = c) (h₂ : s₂ * κ n₂ = c) :
    Ψ hn₂ hn₂0 (algebraMap ℚ R c • negDilogNeg R) *
        Ψ hn₁ hn₁0 (algebraMap ℚ R c • negDilogNeg R) =
      Ψ hn₁ hn₁0 (algebraMap ℚ R c • negDilogNeg R) *
        Ψ (add_mem hn₁ hn₂) (ne_of_apply_ne Subtype.val
          (D.add_ne_zero_of_form_ne_zero (right_ne_zero_of_mul_eq_one hc)))
          (algebraMap ℚ R c • negDilogNeg R) *
        Ψ hn₂ hn₂0 (algebraMap ℚ R c • negDilogNeg R) := by
  classical
  have : Fact ((D.principalPositiveDegrees d).monoid ≤ Qpr) :=
    ⟨D.principalPositiveDegrees_le_coefficientMonoid d⟩
  have hn₁₂ : ((n₁ + n₂ : D.unfrozen) : N) ≠ 0 :=
    D.add_ne_zero_of_form_ne_zero (right_ne_zero_of_mul_eq_one hc)
  obtain ⟨s₃, h₃, hv⟩ := D.sublattice.toAddSubgroup.exists_zsmul_rayVector_add hn₁₂ h₁ h₂
  -- Normal exponents: `E₁₂ = E₁ + E₂`, and the values at the principal exponents.
  have hadd (p : Lpr) : s₃ * D.principalNormal (n₁ + n₂) p =
      s₁ * D.principalNormal n₁ p + s₂ * D.principalNormal n₂ p := by
    have := congrArg (fun v : D.sublattice => p.1 v) hv
    simpa only [principalNormal_apply, Submodule.coe_add, map_add, map_zsmul, smul_eq_mul]
      using this
  have hE₁₁ := D.zsmul_principalNormal_principalEmbedding (m := n₁) (k := 0) h₁ (by simp)
  have hE₁₂ := D.zsmul_principalNormal_principalEmbedding (m := n₂) (k := -1) h₁
    (by rw [form_swap, mul_neg, hc, Int.cast_neg, Int.cast_one])
  have hE₂₁ := D.zsmul_principalNormal_principalEmbedding (m := n₁) (k := 1) h₂
    (by rw [hc, Int.cast_one])
  have hE₂₂ := D.zsmul_principalNormal_principalEmbedding (m := n₂) (k := 0) h₂ (by simp)
  -- The binomial units `1 + z^q` of the principal exponents.
  obtain ⟨q₁, hq₁⟩ : ∃ q : Qpr, (q : Lpr) = D.principalEmbedding n₁ :=
    ⟨⟨_, by simpa using hn₁⟩, rfl⟩
  obtain ⟨q₂, hq₂⟩ : ∃ q : Qpr, (q : Lpr) = D.principalEmbedding n₂ :=
    ⟨⟨_, by simpa using hn₂⟩, rfl⟩
  have hq₁₂ : ((q₁ + q₂ : Qpr) : Lpr) = D.principalEmbedding (n₁ + n₂) := by
    rw [AddSubmonoid.coe_add, hq₁, hq₂, map_add]
  obtain ⟨U₁, hU₁⟩ := D.exists_units_eq_one_add_single (R := R) d q₁
    (by simpa [hq₁] using hn₁0)
  obtain ⟨U₂, hU₂⟩ := D.exists_units_eq_one_add_single (R := R) d q₂
    (by simpa [hq₂] using hn₂0)
  obtain ⟨U₁₂, hU₁₂⟩ := D.exists_units_eq_one_add_single (R := R) d (q₁ + q₂)
    (by simpa [hq₁₂] using ne_of_apply_ne Subtype.val hn₁₂)
  -- Each factor multiplies `z^p` by a power of its binomial unit.
  have W₁ := D.completedBCHAction_completedMap_rayExp_smul_negDilogNeg d hn₁ hn₁0 s₁ Qpr q₁ hq₁
    U₁ hU₁
  have W₂ := D.completedBCHAction_completedMap_rayExp_smul_negDilogNeg d hn₂ hn₂0 s₂ Qpr q₂ hq₂
    U₂ hU₂
  have W₁₂ := D.completedBCHAction_completedMap_rayExp_smul_negDilogNeg d (add_mem hn₁ hn₂)
    (ne_of_apply_ne Subtype.val hn₁₂) s₃ Qpr (q₁ + q₂) hq₁₂ U₁₂ hU₁₂
  have h₃' : (s₃ : ℚ) * κ ((n₁ + n₂ : D.unfrozen) : N) = c := by
    rw [Submodule.coe_add]
    exact h₃
  simp only [h₁] at W₁
  simp only [h₂] at W₂
  simp only [h₃'] at W₁₂
  -- Normal exponents at the principal exponents `q₁`, `q₂` and `q₁ + q₂`.
  have e₁₂ : s₁ * D.principalNormal n₁ (q₂ : Lpr) = -1 := hq₂ ▸ hE₁₂
  have e₂₁ : s₂ * D.principalNormal n₂ (q₁ : Lpr) = 1 := hq₁ ▸ hE₂₁
  have e₁ : s₁ * D.principalNormal n₁ ((q₁ + q₂ : Qpr) : Lpr) = -1 := by
    rw [AddSubmonoid.coe_add, map_add, mul_add, hq₁, hq₂, hE₁₁, hE₁₂, zero_add]
  have e₁₂₂ : s₃ * D.principalNormal (n₁ + n₂) (q₂ : Lpr) = -1 := by
    rw [hadd, hq₂, hE₁₂, hE₂₂, add_zero]
  have hXY : (Fpr).toCompletion (single (q₁ + q₂) 1) =
      (Fpr).toCompletion (single q₁ 1) * (Fpr).toCompletion (single q₂ 1) := by
    rw [← map_mul, single_mul_single, one_mul]
  -- Compare the actions on each monomial `z^p`.
  apply D.eq_of_completedBCHAction_completedMap_single_eq d
  intro p
  simp only [map_mul, AlgEquiv.mul_apply]
  simp only [W₁, W₂, W₁₂, map_mul, algEquiv_coe_zpow, hadd]
  refine pentagon_units hU₁ hU₂ hXY ?_ ?_ ?_ _ _ _
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, hU₁, map_add, map_one, W₂, e₂₁]
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, hU₁₂, map_add, map_one, W₁, e₁]
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, hU₂, map_add, map_one, map_mul, W₁, W₁₂,
      algEquiv_coe_zpow, e₁₂, e₁₂₂]

/-- **Pentagon identity for dilogarithm elements.** If `n₁, n₂ ∈ N°` are nonzero positive
degrees with `{n₁, n₂} = 1`, then `Ψ[n₂] Ψ[n₁] = Ψ[n₁] Ψ[n₁ + n₂] Ψ[n₂]`. -/
theorem dilogElement_pentagon {n₁ n₂ : D.unfrozen} (hn₁ : n₁ ∈ d.monoid) (hn₂ : n₂ ∈ d.monoid)
    (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0) (h₁ : (n₁ : N) ∈ D.sublattice)
    (h₂ : (n₂ : N) ∈ D.sublattice) (h : D.form n₁ n₂ = 1) :
    SkewLieAlgebra.dilogElement β hβ hn₂ hn₂0 * SkewLieAlgebra.dilogElement β hβ hn₁ hn₁0 =
      SkewLieAlgebra.dilogElement β hβ hn₁ hn₁0 *
        SkewLieAlgebra.dilogElement β hβ (add_mem hn₁ hn₂) (ne_of_apply_ne Subtype.val
          (D.add_ne_zero_of_form_ne_zero (ne_of_eq_of_ne h one_ne_zero))) *
        SkewLieAlgebra.dilogElement β hβ hn₂ hn₂0 := by
  have κ₁ : κ n₁ = 1 := D.rayIndex_eq_one_of_form_eq_one (a := -n₂) n₁.property h₁ (by
    rw [map_neg, LinearMap.neg_apply, form_swap, neg_neg, h])
  have κ₂ : κ n₂ = 1 := D.rayIndex_eq_one_of_form_eq_one n₂.property h₂ h
  have hp := D.rayExp_smul_negDilogNeg_pentagon (R := R) d hn₁ hn₂ hn₁0 hn₂0 (c := 1)
    (s₁ := 1) (s₂ := 1) (by rw [one_mul, h]) (by rw [κ₁, Int.cast_one, one_mul])
    (by rw [κ₂, Int.cast_one, one_mul])
  simpa only [map_one, one_smul, SkewLieAlgebra.dilogElement_def] using hp

end Mei.SkewLatticeDatum
