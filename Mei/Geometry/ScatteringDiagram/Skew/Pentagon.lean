/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Dilogarithm
public import Mei.Geometry.ScatteringDiagram.Skew.Examples
public import Mei.Algebra.Lie.Skew.Map
public import Mei.Algebra.Lie.Skew.Weight
public import Mei.Algebra.Group.Units.Hom
public import Mei.Algebra.Ring.Units
public import Mei.Algebra.PositiveDegrees.Basis

/-!
# The pentagon identity for dilogarithm elements

Let `n₁, n₂` be nonzero positive degrees for an alternating form `β` valued in a
commutative `ℚ`-algebra, and let `c` satisfy `c * β n₁ n₂ = 1`. Writing `Ψ[n]^c` for the
ray label `rayExp (c • negDilogNeg R)`
of degree `n`, the completed skew group satisfies the pentagon identity
`Ψ[n₂]^c Ψ[n₁]^c = Ψ[n₁]^c Ψ[n₁ + n₂]^c Ψ[n₂]^c`.
For a rational-valued form and rational `c > 0`, the left side is antiordered and the right
side ordered, since
`{n₂, n₁} < 0` and `{n₁, n₁ + n₂} = {n₁ + n₂, n₂} = {n₁, n₂} > 0`. This is the elementary
exchange of out-of-order dilogarithm factors in rank two. No nondegeneracy of the skew form
is assumed. Specializing `β` to `D.coefficientForm R` gives the skew lattice identity.

## Main statements

* `Mei.SkewLieAlgebra.rayExp_smul_negDilogNeg_pentagon`: the pentagon identity for the
  normalized powers `Ψ[n]^c`.
* `Mei.SkewLieAlgebra.dilogElement_pentagon`: if `{n₁, n₂} = 1`, then
  `Ψ[n₂] Ψ[n₁] = Ψ[n₁] Ψ[n₁ + n₂] Ψ[n₂]`.
* `Mei.SkewLieAlgebra.rayExp_rescale_smul_negDilogNeg_pentagon`: the identity with monomial
  coefficients. For a weight `χ` multiplicative on the allowed monoid, write `Ψ_u[n]^c` for the
  ray label of `c ∑_{j ≥ 1} (-1)^(j+1) u^j X_{jn} / j²`; then
  `Ψ_{χ(n₂)}[n₂]^c Ψ_{χ(n₁)}[n₁]^c = Ψ_{χ(n₁)}[n₁]^c Ψ_{χ(n₁) χ(n₂)}[n₁ + n₂]^c Ψ_{χ(n₂)}[n₂]^c`.
  The weights need not be units.

## Implementation notes

First prove the identity for integral multiples of the ray indices by comparing both sides
through the faithful action on the principal coefficient completion
(`eq_of_completedBCHAction_completedMap_single_eq`). There `Ψ[n]^c` multiplies a monomial
`z^p` by an integer power of the binomial `1 + z^{r(n)}`
(`completedBCHAction_completedMap_rayExp_smul_negDilogNeg`). With `x = z^{r(n₁)}` and
`y = z^{r(n₂)}`, both sides multiply `z^p` by `(1 + x + xy)^a (1 + y)^b`, where `a` and `b`
are the normal exponents of `p`.
The unrestricted identity follows by transporting this calculation from the unimodular plane:
the skew Lie map `X_(a,b) ↦ c X_(a n₁ + b n₂)` preserves brackets because `c {n₁,n₂} = 1`.
`SkewLieAlgebra.gradedMap` and its finite-projection formula transport the ray labels.
The identity with coefficients is the image of the identity with coefficient one under the weight
map `X_n ↦ χ(n) X_n` (`SkewLieAlgebra.weightGradedLieHom`), which rescales the series of each ray
label.

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5,
  arXiv:2111.00800v6; its ordering of products is the reverse of the one used here.
* Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1,
  arXiv:1411.1394v2.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)

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

variable [DecidableEq D.unfrozen]

/-- **Pentagon identity.** Let `n₁, n₂` be nonzero positive degrees and `c` a rational
number with `c {n₁, n₂} = 1` that is an integer multiple of `κ(n₁)` and of `κ(n₂)`.
Then the ray labels `Ψ[n]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` satisfy
`Ψ[n₂]^c Ψ[n₁]^c = Ψ[n₁]^c Ψ[n₁ + n₂]^c Ψ[n₂]^c`. -/
private theorem rayExp_smul_negDilogNeg_pentagon_integral {n₁ n₂ : D.unfrozen} (hn₁ : n₁ ∈ d.monoid)
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
  obtain ⟨U₁, hU₁⟩ : ∃ U : (Fpr).completionˣ,
      (U : (Fpr).completion) = 1 + (Fpr).toCompletion (single q₁ 1) :=
    D.exists_units_eq_one_add_single (R := R) d q₁
    (by simpa [hq₁] using hn₁0)
  obtain ⟨U₂, hU₂⟩ : ∃ U : (Fpr).completionˣ,
      (U : (Fpr).completion) = 1 + (Fpr).toCompletion (single q₂ 1) :=
    D.exists_units_eq_one_add_single (R := R) d q₂
    (by simpa [hq₂] using hn₂0)
  obtain ⟨U₁₂, hU₁₂⟩ : ∃ U : (Fpr).completionˣ,
      (U : (Fpr).completion) = 1 + (Fpr).toCompletion (single (q₁ + q₂) 1) :=
    D.exists_units_eq_one_add_single (R := R) d (q₁ + q₂)
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
  simp only [W₁, W₂, W₁₂, map_mul, Mei.map_units_zpow, hadd]
  refine Units.pentagon hU₁ hU₂ hXY ?_ ?_ ?_ _ _ _
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, hU₁, map_add, map_one, W₂, e₂₁]
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, hU₁₂, map_add, map_one, W₁, e₁]
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, hU₂, map_add, map_one, map_mul, W₁, W₁₂,
      Mei.map_units_zpow, e₁₂, e₁₂₂]

end Mei.SkewLatticeDatum

namespace Mei.SkewLieAlgebra

open PowerSeries SkewLatticeDatum

variable {Γ R : Type*} [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) (d : PositiveDegrees Γ)

local notation "Ψ" => rayExp β hβ

/-- **Pentagon identity.** For nonzero positive degrees with `c * β n₁ n₂ = 1`,
the scaled ray labels satisfy
`Ψ[n₂]^c Ψ[n₁]^c = Ψ[n₁]^c Ψ[n₁ + n₂]^c Ψ[n₂]^c`.
The alternating form may take values in any commutative `ℚ`-algebra. -/
theorem rayExp_smul_negDilogNeg_pentagon {n₁ n₂ : Γ} (hn₁ : n₁ ∈ d.monoid)
    (hn₂ : n₂ ∈ d.monoid) (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0) {c : R}
    (hc : c * β n₁ n₂ = 1) :
    Ψ hn₂ hn₂0 (c • negDilogNeg R) *
        Ψ hn₁ hn₁0 (c • negDilogNeg R) =
      Ψ hn₁ hn₁0 (c • negDilogNeg R) *
        Ψ (add_mem hn₁ hn₂) (d.add_ne_zero hn₁ hn₂ hn₁0)
          (c • negDilogNeg R) *
        Ψ hn₂ hn₂0 (c • negDilogNeg R) := by
  classical
  -- Establish the unit-pairing identity in the unimodular plane.
  let E := Examples.unimodularRankTwo
  let t : (ℤ × ℤ) ≃ₗ[ℤ] E.unfrozen :=
    (LinearEquiv.ofTop E.unfrozen Examples.unimodularRankTwo_unfrozen).symm
  let b := (Module.Basis.finTwoProd ℤ).map t
  let δ := b.positiveDegrees
  let v₁ := b 0
  let v₂ := b 1
  have hv₁ : v₁ ∈ δ.monoid := by simp [v₁, δ]
  have hv₂ : v₂ ∈ δ.monoid := by simp [v₂, δ]
  have hv₁0 : v₁ ≠ 0 := b.ne_zero 0
  have hv₂0 : v₂ ≠ 0 := b.ne_zero 1
  -- The equivalence fixes the underlying coordinates; specify it to keep the
  -- canonical integer module on `E.unfrozen` in every basis coercion.
  have ht (v : ℤ × ℤ) : (t v : ℤ × ℤ) = v :=
    LinearEquiv.coe_ofTop_symm_apply _ v
  have hb₁ : (v₁ : ℤ × ℤ) = (1, 0) := by
    simpa only [v₁, b, Module.Basis.map_apply, Module.Basis.finTwoProd_zero] using
      ht (1, 0)
  have hb₂ : (v₂ : ℤ × ℤ) = (0, 1) := by
    simpa only [v₂, b, Module.Basis.map_apply, Module.Basis.finTwoProd_one] using
      ht (0, 1)
  have hpair : E.form v₁ v₂ = 1 := by
    simp only [E, Examples.unimodularRankTwo_form, Examples.rankTwoForm_apply, hb₁, hb₂]
    norm_num
  have hκ₁ : E.sublattice.toAddSubgroup.rayIndex v₁ = 1 :=
    E.rayIndex_eq_one_of_form_eq_one (a := -v₂) v₁.property (by simp [E]) (by
      rw [map_neg, LinearMap.neg_apply, form_swap, neg_neg, hpair])
  have hκ₂ : E.sublattice.toAddSubgroup.rayIndex v₂ = 1 :=
    E.rayIndex_eq_one_of_form_eq_one v₂.property (by simp [E]) hpair
  have hp := E.rayExp_smul_negDilogNeg_pentagon_integral (R := R) δ hv₁ hv₂ hv₁0 hv₂0
    (c := 1) (s₁ := 1) (s₂ := 1) (by simpa using hpair) (by simp [hκ₁]) (by simp [hκ₂])
  simp only [map_one, one_smul] at hp
  -- The basis map `(a, b) ↦ a n₁ + b n₂` is a positive degree map with identity modulus.
  let T : PositiveDegreeMap δ d := b.positiveDegreeMap ![n₁, n₂]
    (Fin.forall_fin_two.mpr ⟨hn₁, hn₂⟩) (Fin.forall_fin_two.mpr ⟨hn₁0, hn₂0⟩)
  have f₁ : T v₁ = n₁ := b.positiveDegreeMap_self _ _ _ 0
  have f₂ : T v₂ = n₂ := b.positiveDegreeMap_self _ _ _ 1
  have f_apply (v : E.unfrozen) : T v = b.repr v 0 • n₁ + b.repr v 1 • n₂ := by
    simp [T, Module.Basis.constr_apply_fintype, Fin.sum_univ_two]
  -- Scaling generators by `c` compensates for the change in skew pairing.
  have hform (v w : E.unfrozen) :
      E.coefficientForm R v w = c * β (T v) (T w) := by
    have he (v : E.unfrozen) : (v : ℤ × ℤ) = (b.repr v 0, b.repr v 1) := by
      -- The mapped standard basis reads exactly the two coordinates of `v`.
      rfl
    simp only [SkewLatticeDatum.coefficientForm_apply, E,
      Examples.unimodularRankTwo_form, Examples.rankTwoForm_apply, he,
      Int.cast_sub, Int.cast_mul, map_sub, map_mul, map_intCast]
    rw [f_apply, f_apply]
    simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply,
      hβ.self_eq_zero, ← hβ.neg n₁ n₂]
    linear_combination (-(b.repr v 0 : R) * b.repr w 1 +
      (b.repr v 1 : R) * b.repr w 0) * hc
  let φ := SkewLieAlgebra.gradedMap (E.coefficientForm R) (E.isAlt_coefficientForm R)
    β hβ c T hform
  -- Transport each finite projection; the degree estimate gives the same source cutoff.
  apply CompletedGroup.ext
  intro k
  have hk : T.modulus k ≤ k := (b.positiveDegreeMap_modulus _ _ _ k).le
  let ψ := (φ.lieTruncatedMap k hk).bchGroupMap.comp
    (CompletedGroup.projection (F := δ.groupTower
      (SkewLieAlgebra.positiveGrading (E.coefficientForm R) (E.isAlt_coefficientForm R) δ)) k)
  have h := congrArg ψ hp
  simp only [map_mul] at h
  have hmap {v : E.unfrozen} (hv : v ∈ δ.monoid) (hv0 : v ≠ 0) :
      ψ (SkewLieAlgebra.rayExp (E.coefficientForm R) (E.isAlt_coefficientForm R)
        hv hv0 (negDilogNeg R)) = CompletedGroup.projection k
          (Ψ (T.map_mem hv) (T.map_ne_zero hv hv0) (c • negDilogNeg R)) := by
    exact SkewLieAlgebra.lieTruncatedMap_gradedMap_projection_rayExp
      (E.coefficientForm R) (E.isAlt_coefficientForm R) β hβ c T hform
      hv hv0 (negDilogNeg R) k k hk
  simp only [hmap] at h
  simp only [f₁, f₂, map_add] at h
  simp only [map_mul]
  exact h

/-- **Pentagon identity with coefficients.** Let `χ` be a weight on the exponent group that is
multiplicative on the allowed monoid, and let `n₁, n₂` be nonzero allowed degrees with
`c * β n₁ n₂ = 1`. Writing `Ψ_u[n]^c` for the ray label of
`c ∑_{j ≥ 1} (-1)^(j+1) u^j X_{jn} / j²`, that is of `(c • negDilogNeg R)(u T)`,
`Ψ_{χ(n₂)}[n₂]^c Ψ_{χ(n₁)}[n₁]^c = Ψ_{χ(n₁)}[n₁]^c Ψ_{χ(n₁) χ(n₂)}[n₁ + n₂]^c Ψ_{χ(n₂)}[n₂]^c`. -/
theorem rayExp_rescale_smul_negDilogNeg_pentagon {χ : Γ → R}
    (hχ : ∀ n ∈ d.monoid, ∀ m ∈ d.monoid, χ (n + m) = χ n * χ m) {n₁ n₂ : Γ}
    (hn₁ : n₁ ∈ d.monoid) (hn₂ : n₂ ∈ d.monoid) (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0) {c : R}
    (hc : c * β n₁ n₂ = 1) :
    Ψ hn₂ hn₂0 (rescale (χ n₂) (c • negDilogNeg R)) *
        Ψ hn₁ hn₁0 (rescale (χ n₁) (c • negDilogNeg R)) =
      Ψ hn₁ hn₁0 (rescale (χ n₁) (c • negDilogNeg R)) *
        Ψ (add_mem hn₁ hn₂) (d.add_ne_zero hn₁ hn₂ hn₁0)
          (rescale (χ n₁ * χ n₂) (c • negDilogNeg R)) *
        Ψ hn₂ hn₂0 (rescale (χ n₂) (c • negDilogNeg R)) := by
  have h := congrArg (weightGradedLieHom β hβ d hχ).completedMap
    (rayExp_smul_negDilogNeg_pentagon β hβ d hn₁ hn₂ hn₁0 hn₂0 hc)
  simp only [map_mul, completedMap_weightGradedLieHom_rayExp, hχ n₁ hn₁ n₂ hn₂] at h
  exact h

/-- **Pentagon identity for dilogarithm elements.** For nonzero positive degrees
with `{n₁, n₂} = 1`, one has `Ψ[n₂] Ψ[n₁] = Ψ[n₁] Ψ[n₁ + n₂] Ψ[n₂]`. -/
theorem dilogElement_pentagon {n₁ n₂ : Γ} (hn₁ : n₁ ∈ d.monoid) (hn₂ : n₂ ∈ d.monoid)
    (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0) (h : β n₁ n₂ = 1) :
    SkewLieAlgebra.dilogElement β hβ hn₂ hn₂0 * SkewLieAlgebra.dilogElement β hβ hn₁ hn₁0 =
      SkewLieAlgebra.dilogElement β hβ hn₁ hn₁0 *
        SkewLieAlgebra.dilogElement β hβ (add_mem hn₁ hn₂) (d.add_ne_zero hn₁ hn₂ hn₁0) *
        SkewLieAlgebra.dilogElement β hβ hn₂ hn₂0 := by
  have hp := rayExp_smul_negDilogNeg_pentagon β hβ d hn₁ hn₂ hn₁0 hn₂0 (c := 1)
    (by rw [one_mul, h])
  simpa only [one_smul, SkewLieAlgebra.dilogElement_def] using hp

end Mei.SkewLieAlgebra
