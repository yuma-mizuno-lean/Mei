/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Dilogarithm
public import Mei.RingTheory.FilteredAlgebra.Positive.PowerSeries
import Mei.Geometry.ScatteringDiagram.Skew.Coefficient.Positive
import Mei.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Log

/-!
# Integral actions of dilogarithm powers

Fix a coefficient map `φ : S →+* R` from a semiring to a commutative `ℚ`-algebra.
A principal coefficient is *`S`-integral* when it is positive, in the sense of
`AlgFiltration.IsPositive`, for the image of `S[Q]`; for `ℤ →+* ℚ` this says that every
monomial coefficient is an integer.

For a nonzero positive degree `n` and a rational exponent `c`, the power
`Ψ[n]^c = exp(c ∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` of the dilogarithm element acts on the
principal coefficient completion through the principal realization. Its action on a monomial
is `z^p ↦ z^p (1 + z^{r(n)})^{(c / κ(n)) ⟨κ(n) n, p⟩}`, where `⟨κ(n) n, -⟩` is the primitive
integral principal normal. When `c / κ(n)` is an integer `s`, the factor is an integral power
of a unit with integral inverse, so `Ψ[n]^c` preserves `S`-integral coefficients for every
ring `S`. Conversely, pairing with a character on which the primitive normal takes the
value `1` reads `c / κ(n)` off the linear coefficient of the wall function, by
`isPositive_completedAeval_single_iff`. Hence for `ℤ →+* ℚ` the
power `Ψ[n]^c` preserves integral coefficients exactly when `c ∈ κ(n) ℤ`.

More generally, integrality detects the lowest logarithmic coefficient of an arbitrary
completed skew label `g`. If all coefficients of `g` vanish below the degree `deg n` of `n`
and its coefficient in degree `n` is `c X_n`, then at order `deg n` the label acts by
`z^p ↦ z^p + ∑ c_m ⟨m, p⟩ z^{p + r(m)}`, summed over its coefficients `c_m X_m` of degree
`deg n`. The monomials `z^{p + r(m)}` are distinct, so the same pairing reads off `c / κ(n)`.

For a finite product `C = Ψ[m₁]^{c₁} ⋯ Ψ[m_r]^{c_r}` of rational dilogarithm powers at pairwise
distinct degrees, in any order, this gives integrality of all normalized exponents
`cᵢ / κ(mᵢ)` by induction on the degree. If a label `g` agrees with `C` at order `k` and acts
integrally, the factors of degree below `deg mᵢ ≤ k` have integral normalized exponents, so
they and their inverses act integrally.
Removing them from `g` leaves a label that lies in the degree filtration, by
`PositiveDegrees.inv_prod_filter_mul_prod_mem_degreeFiltration_and_logComponent`, and has
lowest coefficient `cᵢ X_{mᵢ}`. Hence `C` acts integrally exactly when every `cᵢ` lies in
`κ(mᵢ) ℤ`. This is the integrality step in the ordering of rank-two products of normalized
dilogarithm powers: the normalized exponent `cᵢ / κ(mᵢ)` of an ordered factorization agreeing
with an integral product at order `k` is an integer whenever `deg mᵢ ≤ k`, so each such factor
is again of the form
`Ψ[tn]^(s κ(tn))` with `s` an integer.

## Main statements

* `Mei.SkewLatticeDatum.isPositive_completedBCHAction_rayExp_zsmul`: integral powers
  `Ψ[n]^(s κ(n))` preserve `S`-integral coefficients.
* `Mei.SkewLatticeDatum.algebraMap_div_rayIndex_mem_rangeS_of_isPositive`: if `Ψ[n]^c`
  preserves `S`-integral coefficients, then `c / κ(n)` lies in the image of `S`.
* `Mei.SkewLatticeDatum.forall_isPositive_completedBCHAction_rayExp_iff`: over `ℚ`, `Ψ[n]^c`
  preserves integral coefficients if and only if `c` is an integer multiple of `κ(n)`.
* `Mei.SkewLatticeDatum.algebraMap_inv_rayIndex_mul_mem_rangeS_of_isPositive`: the lowest
  logarithmic coefficient `c X_n` of a label preserving `S`-integral coefficients has
  `c / κ(n)` in the image of `S`.
* `Mei.SkewLatticeDatum.exists_eq_intCast_mul_rayIndex_of_projection_eq_prod`: a label
  preserving integral coefficients that agrees at order `k` with a product of dilogarithm
  powers `Ψ[mᵢ]^{cᵢ}` at distinct degrees has `cᵢ ∈ κ(mᵢ) ℤ` whenever `deg mᵢ ≤ k`.
* `Mei.SkewLatticeDatum.forall_isPositive_completedBCHAction_prod_rayExp_iff`: such a product
  preserves integral coefficients if and only if every `cᵢ` lies in `κ(mᵢ) ℤ`.

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2, the lemma
  that `Ψ[tn]^(s δ(tn))` acts on `ℤ[[P_pr]]` if and only if `s` is an integer, and the
  lemma, proved from it by induction on the degree, that the exponents of the ordered
  product produced by the ordering algorithm are integers, arXiv:2111.00800v6.
* Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1 and
  Appendix B, arXiv:1411.1394v2, for the principal realization.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open _root_.AddMonoidAlgebra PowerSeries

variable {N R : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [CommRing R] [Algebra ℚ R] (D : SkewLatticeDatum N) (d : PositiveDegrees D.unfrozen)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "e" => D.principalPositiveDegrees d
local notation "Qpr" => D.principalCoefficientMonoid d
local notation "Fpr" => TropicalVertexCoefficientAction.filtration
  (R := R) (D.principalPositiveDegrees d) Qpr

variable [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  {n : D.unfrozen} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

local notation "ρ" => AddMonoidHom.id Lpr
local notation "ℳ" => tropicalVertexGrading (R := R) e ρ
local notation "β" => D.coefficientForm R
local notation "hβ" => D.isAlt_coefficientForm R
local notation "𝔤" => SkewLieAlgebra.positiveLieAlgebra β hβ d
local notation "𝓛" => SkewLieAlgebra.positiveGrading β hβ d

open TropicalVertexCoefficientAction

section Monoid

variable {S : Type*} [Ring S] (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees d).monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q

/-- The integrality of `Ψ[n]^(s κ(n))`, given the monomial `z^q` at the principal degree of
`n` and the binomial unit `1 + z^q`. -/
private theorem isPositive_completedBCHAction_rayExp_zsmul_of_unit (φ : S →+* R) (s : ℤ) (q : Q)
    (hq : q.val = D.principalEmbedding n) (U : (F).completionˣ)
    (hUval : (U : (F).completion) = 1 + (F).toCompletion (single q 1)) {x : (F).completion}
    (hx : (F).IsPositive (mapRingHom Q φ).rangeS x) :
    (F).IsPositive (mapRingHom Q φ).rangeS
      ((F).completedBCHAction (R := R) e ℳ ((D.principalGradedLieHom d).completedMap
        (SkewLieAlgebra.rayExp β hβ hn hn0
          (algebraMap ℚ R ((s : ℚ) * D.sublattice.toAddSubgroup.rayIndex n) •
            negDilogNeg R))) x) := by
  have hmem := D.toCompletion_single_principalEmbedding_mem_first (R := R) d hn hn0 Q q hq
  -- The binomial unit `1 + z^q` and its inverse are integral.
  have hsingle (p : Q) (c : S) :
      (F).IsPositive (mapRingHom Q φ).rangeS ((F).toCompletion (single p (φ c))) :=
    AlgFiltration.isPositive_toCompletion
      (RingHom.mem_rangeS.mpr ⟨single p c, by simp [mapRingHom_single]⟩)
  have hupos : (F).IsPositive (mapRingHom Q φ).rangeS ((F).toCompletion (single q 1)) := by
    simpa only [map_one] using hsingle q 1
  have hUpos : (F).IsPositive (mapRingHom Q φ).rangeS (U : (F).completion) := by
    rw [hUval]
    exact AlgFiltration.isPositive_one.add hupos
  have hUinv : (F).IsPositive (mapRingHom Q φ).rangeS ((U⁻¹ : (F).completionˣ) :
      (F).completion) := by
    refine AlgFiltration.IsPositive.inv_of_val_eq_one_add (x := ⟨_, hmem⟩) hupos ?_ hUval
    exact RingHom.mem_rangeS.mpr ⟨-1, by simp⟩
  have hUzpow (m : ℤ) :
      (F).IsPositive (mapRingHom Q φ).rangeS ((U ^ m : (F).completionˣ) : (F).completion) := by
    rcases m with m | m
    · simpa only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val] using
        hUpos.pow m
    · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      exact hUinv.pow (m + 1)
  -- Monomials, hence all integral polynomials, have integral images.
  have hpoly (a : S[Q]) : (F).IsPositive (mapRingHom Q φ).rangeS
      ((F).completedBCHAction (R := R) e ℳ ((D.principalGradedLieHom d).completedMap
        (SkewLieAlgebra.rayExp β hβ hn hn0
          (algebraMap ℚ R ((s : ℚ) * D.sublattice.toAddSubgroup.rayIndex n) •
            negDilogNeg R))) ((F).toCompletion (mapRingHom Q φ a))) := by
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simpa only [map_zero] using AlgFiltration.isPositive_zero
    | add a b ha hb => simpa only [map_add] using ha.add hb
    | single p c =>
      have hmon := D.completedBCHAction_completedMap_rayExp_smul_negDilogNeg d hn hn0
        s Q q hq U hUval p (φ c)
      simpa only [mapRingHom_single, hmon] using (hUzpow _).mul (hsingle p c)
  refine AlgFiltration.IsPositive.apply_of_projection_congr
    ((F).completedBCHAction (R := R) e ℳ ((D.principalGradedLieHom d).completedMap
      (SkewLieAlgebra.rayExp β hβ hn hn0
        (algebraMap ℚ R ((s : ℚ) * D.sublattice.toAddSubgroup.rayIndex n) • negDilogNeg R))))
    (fun k y z h => by simp only [AlgFiltration.projection_completedBCHAction, h])
    (fun a ha => (RingHom.mem_rangeS.mp ha).elim fun b hb => hb ▸ hpoly b) hx

/-- **Integral powers act integrally.** For an integer `s`, the principal action of the
normalized dilogarithm power `Ψ[n]^(s κ(n))` sends every completed coefficient that is
integral for the image of `S[Q]` to such a coefficient. Here `Q` is any coefficient monoid
containing the principal positive degrees. -/
theorem isPositive_completedBCHAction_rayExp_zsmul (φ : S →+* R) (s : ℤ) {x : (F).completion}
    (hx : (F).IsPositive (mapRingHom Q φ).rangeS x) :
    (F).IsPositive (mapRingHom Q φ).rangeS
      ((F).completedBCHAction (R := R) e ℳ ((D.principalGradedLieHom d).completedMap
        (SkewLieAlgebra.rayExp β hβ hn hn0
          (algebraMap ℚ R ((s : ℚ) * D.sublattice.toAddSubgroup.rayIndex n) •
            negDilogNeg R))) x) :=
  have hpos : D.principalEmbedding n ∈ (e).monoid := by
    rw [principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
    exact ⟨hn, rfl⟩
  have hmem := D.toCompletion_single_principalEmbedding_mem_first (R := R) d hn hn0 Q
    ⟨_, Fact.out (p := (D.principalPositiveDegrees d).monoid ≤ Q) hpos⟩ rfl
  have hU : (1 + (F).toCompletion (single _ 1)) - 1 ∈ (F).completionIdeal 1 := by
    simpa only [add_sub_cancel_left] using hmem
  D.isPositive_completedBCHAction_rayExp_zsmul_of_unit d hn hn0 Q φ s _ rfl
    ((F).isUnit_of_sub_one_mem hU).unit (IsUnit.unit_spec _) hx

end Monoid

section Principal

variable {S : Type*} [Semiring S]
  [Fact ((D.principalPositiveDegrees d).monoid ≤ D.principalCoefficientMonoid d)]

include hn hn0 in
/-- **Integrality detects the lowest logarithmic coefficient.** Let `g` be a completed skew
label whose logarithmic coefficients vanish in all degrees below that of a nonzero allowed
degree `n`, and whose principal action preserves the coefficients integral for the image of
`S[Q_pr]`. If its coefficient in degree `n` is `c X_n`, then `c / κ(n)` lies in the image
of `S`. At order `deg n` the action sends `z^p` to `z^p + ∑ c_m ⟨m, p⟩ z^{p + r(m)}`, summed
over the coefficients `c_m X_m` of degree `deg n`, and the monomials `z^{p + r(m)}` are
distinct. -/
theorem algebraMap_inv_rayIndex_mul_mem_rangeS_of_isPositive [Module.Free ℤ D.sublattice]
    (φ : S →+* R) {g : d.completedBCHGroup 𝓛}
    (hg : g ∈ CompletedGroup.degreeFiltration (d.groupTower 𝓛) (d.degree n).toNat)
    (h : ∀ x : (Fpr).completion, (Fpr).IsPositive (mapRingHom Qpr φ).rangeS x →
      (Fpr).IsPositive (mapRingHom Qpr φ).rangeS
        ((Fpr).completedBCHAction (R := R) e ℳ ((D.principalGradedLieHom d).completedMap g) x))
    {c : R}
    (hc : ((d.logComponent 𝓛 g n : 𝔤) : D.skewLieAlgebra R) = SkewLieAlgebra.single β hβ n c) :
    algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex n)⁻¹ * c ∈ φ.rangeS := by
  classical
  have hnN : (n : N) ≠ 0 := fun h => hn0 (Subtype.ext h)
  have hκ := D.sublattice.toAddSubgroup.rayIndex_pos hnN
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (d.degree n).toNat = a + 1 :=
    ⟨(d.degree n).toNat - 1, by have := d.degree_pos hn hn0; omega⟩
  have hdeg : d.degree n = (a + 1 : ℕ) := by have := d.degree_pos hn hn0; omega
  rw [ha] at hg
  -- A character `χ` with `χ (κ(n) n) = 1`, and the monomial `z^p` for `p = (χ, 0)`.
  obtain ⟨χ, hχ⟩ := TauCeti.isPrimitive_def.mp
    (D.sublattice.toAddSubgroup.isPrimitive_rayVector hκ)
  obtain ⟨p, hpv⟩ : ∃ p : Qpr, p.val = (χ, 0) := ⟨⟨_, by simp⟩, rfl⟩
  have hp : D.principalNormal n p.val = 1 := by rw [hpv, principalNormal_apply]; exact hχ
  have hev : D.principalEvaluation (R := R) n p.val =
      algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex n)⁻¹ := by
    have h₁ := D.intCast_principalNormal_apply (R := R) n p.val
    rw [hp, Int.cast_one] at h₁
    calc D.principalEvaluation (R := R) n p.val
        = algebraMap ℚ R ((D.sublattice.toAddSubgroup.rayIndex n)⁻¹ *
            D.sublattice.toAddSubgroup.rayIndex n) * D.principalEvaluation (R := R) n p.val := by
          rw [inv_mul_cancel₀ hκ.ne', map_one, one_mul]
      _ = algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex n)⁻¹ := by
          rw [map_mul, mul_assoc, ← h₁, mul_one]
  -- The order-`(a + 1)` projection of the image of `z^p`.
  have hpos := h ((Fpr).toCompletion (single p 1)) (AlgFiltration.isPositive_toCompletion
    (RingHom.mem_rangeS.mpr ⟨single p 1, by simp [mapRingHom_single]⟩))
  rw [AlgFiltration.isPositive_iff] at hpos
  obtain ⟨b, hb, hbx⟩ := hpos (a + 1)
  rw [projection_completedBCHAction_single_of_mem_degreeFiltration D d hg
    (d.log_projection_eq_mkQ_sum 𝓛 g (a + 1)).symm p, Ideal.Quotient.eq] at hbx
  -- The monomial `z^{p + r(n)}` has order `a + 1`, so it does not occur in the difference.
  obtain ⟨q, hq⟩ : ∃ q : Qpr, q = ⟨(D.principalCharacter n, n), by simp [hn]⟩ + p := ⟨_, rfl⟩
  have hq2 : q.val.2 = n := by simp [hq, hpv]
  have hzero : (b - (single p 1 + D.principalCoefficientAction d
      (∑ m ∈ (d.finite_cutoff (a + 1)).toFinset, (d.logComponent 𝓛 g m : 𝔤))
        (single p 1))).coeff q = 0 := by
    by_contra hne
    have := (D.mem_principalCoefficientFiltration_ideal_iff d _ _).mp hbx q
      (Finsupp.mem_support_iff.mpr hne)
    rw [hq2, hdeg] at this
    push_cast at this
    omega
  have hpq : p ≠ q := fun h => hn0 (by rw [← hq2, ← h, hpv])
  -- Only the degree-`n` coefficient contributes to `z^{p + r(n)}`.
  have hsum : SkewLieAlgebra.toFinsupp β hβ
      (∑ m ∈ (d.finite_cutoff (a + 1)).toFinset, (d.logComponent 𝓛 g m : 𝔤)).val n = c := by
    have hnc : n ∈ (d.finite_cutoff (a + 1)).toFinset :=
      (d.finite_cutoff (a + 1)).mem_toFinset.mpr (d.mem_cutoff.mpr ⟨hn, hdeg.le⟩)
    rw [AddSubmonoidClass.coe_finsetSum, map_sum, Finset.sum_apply',
      Finset.sum_eq_single_of_mem n hnc, hc, SkewLieAlgebra.toFinsupp_single,
      Finsupp.single_eq_same]
    intro m _ hmn
    obtain ⟨r, hr⟩ := (SkewLieAlgebra.mem_grade_iff β hβ m _).mp
      ((SkewLieAlgebra.mem_positiveGrading_iff β hβ d m _).mp (d.logComponent 𝓛 g m).property)
    rw [← hr, SkewLieAlgebra.toFinsupp_single, Finsupp.single_eq_of_ne (Ne.symm hmn)]
  have hcoeff := D.principalCoefficientAction_coeff d
    (∑ m ∈ (d.finite_cutoff (a + 1)).toFinset, (d.logComponent 𝓛 g m : 𝔤)) ⟨n, hn⟩ p 1
  rw [hsum, hev, one_mul, ← hq] at hcoeff
  rw [coeff_sub, coeff_add, Finsupp.sub_apply, Finsupp.add_apply, hcoeff, coeff_single,
    Finsupp.single_eq_of_ne (Ne.symm hpq), zero_add, sub_eq_zero] at hzero
  obtain ⟨b', rfl⟩ := RingHom.mem_rangeS.mp hb
  rw [coeff_mapRingHom] at hzero
  exact RingHom.mem_rangeS.mpr ⟨_, hzero.trans (mul_comm _ _)⟩

/-- **Integrality detects the exponent.** If the principal action of `Ψ[n]^c`, for a
rational exponent `c`, sends coefficients integral for the image of `S[Q_pr]` to such
coefficients, then the normalized exponent `c / κ(n)` lies in the image of `S`. It is read
off the linear coefficient of the wall function at a character on which the primitive
principal normal is `1`. -/
theorem algebraMap_div_rayIndex_mem_rangeS_of_isPositive [Module.Free ℤ D.sublattice]
    (φ : S →+* R) {c : ℚ}
    (h : ∀ x : (Fpr).completion, (Fpr).IsPositive (mapRingHom Qpr φ).rangeS x →
      (Fpr).IsPositive (mapRingHom Qpr φ).rangeS
        ((Fpr).completedBCHAction (R := R) e ℳ ((D.principalGradedLieHom d).completedMap
          (SkewLieAlgebra.rayExp β hβ hn hn0 (algebraMap ℚ R c • negDilogNeg R))) x)) :
    algebraMap ℚ R (c / D.sublattice.toAddSubgroup.rayIndex n) ∈ φ.rangeS := by
  have hnN : (n : N) ≠ 0 := fun h => hn0 (Subtype.ext h)
  have hκ := D.sublattice.toAddSubgroup.rayIndex_pos hnN
  -- The wall function `f = (1 + X)^t` for `t = c / κ(n)`, written as `exp (t log (1 + X))`.
  have hf0 : constantCoeff
      (algebraMap ℚ R (c / D.sublattice.toAddSubgroup.rayIndex n) • log R) = 0 := by simp
  obtain ⟨f, hfdef⟩ : ∃ f : PowerSeries R,
      f = (exp R).subst (algebraMap ℚ R (c / D.sublattice.toAddSubgroup.rayIndex n) • log R) :=
    ⟨_, rfl⟩
  have hf : constantCoeff f = 1 := hfdef ▸ constantCoeff_subst_exp hf0
  have hlog : logOf f = algebraMap ℚ R (c / D.sublattice.toAddSubgroup.rayIndex n) • log R :=
    hfdef ▸ logOf_subst_exp hf0
  have hlabel : algebraMap ℚ R (((1 : ℤ) : ℚ) * D.sublattice.toAddSubgroup.rayIndex n) •
      eulerDerivInv (logOf f) = algebraMap ℚ R c • negDilogNeg R := by
    rw [hlog, map_smul, eulerDerivInv_log, smul_smul, ← map_mul, Int.cast_one, one_mul,
      mul_div_cancel₀ _ hκ.ne']
  -- The monomial `z^q` at the principal degree of `n` and the evaluated wall function.
  obtain ⟨q, hq⟩ : ∃ q : Qpr, q.val = D.principalEmbedding n := ⟨⟨_, by simp [hn]⟩, rfl⟩
  have hq0 : q.val.2 ≠ 0 := by simpa [hq] using hn0
  have hmem := D.toCompletion_single_mem_completionIdeal_one (R := R) d q hq0
  obtain ⟨fQ, hfQ⟩ : ∃ fQ : (Fpr).completionˣ,
      (fQ : (Fpr).completion) = (Fpr).completedAeval ⟨_, hmem⟩ f :=
    ⟨((Fpr).isUnit_of_sub_one_mem ((Fpr).completedAeval_sub_one_mem_first _ f hf)).unit,
      IsUnit.unit_spec _⟩
  -- A character `χ` with `χ (κ(n) n) = 1`, so that `⟨κ(n) n, (χ, 0)⟩ = 1`.
  obtain ⟨χ, hχ⟩ := TauCeti.isPrimitive_def.mp
    (D.sublattice.toAddSubgroup.isPrimitive_rayVector hκ)
  obtain ⟨p, hpv⟩ : ∃ p : Qpr, p.val = (χ, 0) := ⟨⟨_, by simp⟩, rfl⟩
  obtain ⟨p', hp'v⟩ : ∃ p' : Qpr, p'.val = (-χ, 0) := ⟨⟨_, by simp⟩, rfl⟩
  have hp : D.principalNormal n p.val = 1 := by rw [hpv, principalNormal_apply]; exact hχ
  have hpp' : p + p' = 0 := Subtype.ext (by simp [hpv, hp'v])
  have haction := D.completedBCHAction_completedMap_rayExp_eulerDerivInv_logOf d hn hn0 1 Qpr
    f hf q hq ⟨_, hmem⟩ rfl fQ hfQ p 1
  have hθ : (Fpr).completedBCHAction (R := R) e ℳ ((D.principalGradedLieHom d).completedMap
      (SkewLieAlgebra.rayExp β hβ hn hn0 (algebraMap ℚ R c • negDilogNeg R)))
        ((Fpr).toCompletion (single p 1)) = fQ * (Fpr).toCompletion (single p 1) := by
    simpa only [hlabel, hp, mul_one, zpow_one] using haction
  have hmono (r : Qpr) : (Fpr).IsPositive (mapRingHom Qpr φ).rangeS
      ((Fpr).toCompletion (single r 1)) :=
    AlgFiltration.isPositive_toCompletion
      (RingHom.mem_rangeS.mpr ⟨single r 1, by simp [mapRingHom_single]⟩)
  -- Cancelling the invertible character monomial leaves the wall function.
  have hcancel : (fQ : (Fpr).completion) * (Fpr).toCompletion (single p 1) *
      (Fpr).toCompletion (single p' 1) = fQ := by
    have h01 : (single p 1 * single p' 1 : R[Qpr]) = 1 := by
      rw [single_mul_single, hpp', mul_one, one_def]
    simp only [mul_assoc, ← map_mul, h01, map_one, mul_one]
  have hfpos : (Fpr).IsPositive (mapRingHom Qpr φ).rangeS
      ((Fpr).completedAeval ⟨_, hmem⟩ f) := by
    have h₁ : (Fpr).IsPositive (mapRingHom Qpr φ).rangeS
        ((fQ : (Fpr).completion) * (Fpr).toCompletion (single p 1)) := by
      simpa only [hθ] using h _ (hmono p)
    have h₂ : (Fpr).IsPositive (mapRingHom Qpr φ).rangeS (fQ : (Fpr).completion) := by
      simpa only [hcancel] using h₁.mul (hmono p')
    simpa only [hfQ] using h₂
  have hcoeff := (D.isPositive_completedAeval_single_iff d φ q hq0 f).mp hfpos
  obtain ⟨r, hr⟩ := RingHom.mem_rangeS.mp (hcoeff 1)
  refine RingHom.mem_rangeS.mpr ⟨r, hr.trans ?_⟩
  rw [← coeff_one_logOf hf, hlog, map_smul, coeff_one_log, smul_eq_mul, mul_one]

/-- **Integrality criterion for dilogarithm powers.** Over `ℚ`, the principal action of
`Ψ[n]^c` preserves the completed coefficients with integer monomial coefficients if and
only if `c` is an integer multiple of `κ(n)`. -/
theorem forall_isPositive_completedBCHAction_rayExp_iff [Module.Free ℤ D.sublattice] {c : ℚ} :
    (∀ x : (TropicalVertexCoefficientAction.filtration (R := ℚ)
        (D.principalPositiveDegrees d) Qpr).completion,
      (TropicalVertexCoefficientAction.filtration (R := ℚ)
        (D.principalPositiveDegrees d) Qpr).IsPositive
          (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x →
        (TropicalVertexCoefficientAction.filtration (R := ℚ)
          (D.principalPositiveDegrees d) Qpr).IsPositive
          (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
          ((TropicalVertexCoefficientAction.filtration (R := ℚ)
            (D.principalPositiveDegrees d) Qpr).completedBCHAction (R := ℚ) e
            (tropicalVertexGrading (R := ℚ) e ρ)
            ((D.principalGradedLieHom (R := ℚ) d).completedMap
              (SkewLieAlgebra.rayExp (D.coefficientForm ℚ) (D.isAlt_coefficientForm ℚ) hn hn0
                (algebraMap ℚ ℚ c • negDilogNeg ℚ))) x)) ↔
      ∃ s : ℤ, c = s * D.sublattice.toAddSubgroup.rayIndex n := by
  have hκ := D.sublattice.toAddSubgroup.rayIndex_pos (n := (n : N))
    (fun h => hn0 (Subtype.ext h))
  constructor
  · intro h
    obtain ⟨s, hs⟩ := RingHom.mem_rangeS.mp
      (D.algebraMap_div_rayIndex_mem_rangeS_of_isPositive d hn hn0 (Int.castRingHom ℚ) h)
    refine ⟨s, ?_⟩
    rw [Algebra.algebraMap_self, RingHom.id_apply, eq_comm, div_eq_iff hκ.ne'] at hs
    simpa only [eq_intCast] using hs
  · rintro ⟨s, rfl⟩ x hx
    exact D.isPositive_completedBCHAction_rayExp_zsmul d hn hn0 _ (Int.castRingHom ℚ) s hx

end Principal

section Product

variable [Fact ((D.principalPositiveDegrees d).monoid ≤ D.principalCoefficientMonoid d)]

local notation "βℚ" => D.coefficientForm ℚ
local notation "hβℚ" => D.isAlt_coefficientForm ℚ
local notation "𝔤ℚ" => SkewLieAlgebra.positiveLieAlgebra βℚ hβℚ d
local notation "𝓛ℚ" => SkewLieAlgebra.positiveGrading βℚ hβℚ d
local notation "Fℚ" => TropicalVertexCoefficientAction.filtration
  (R := ℚ) (D.principalPositiveDegrees d) Qpr

include hn hn0 in
/-- A dilogarithm power `Ψ[n]^c` with `c ∈ κ(n) ℤ` preserves integral principal coefficients. -/
private theorem isPositive_completedBCHAction_rayExp_of_eq {c : ℚ} {s : ℤ}
    (hs : c = s * D.sublattice.toAddSubgroup.rayIndex n) {x : (Fℚ).completion}
    (hx : (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x) :
    (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
      ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
        ((D.principalGradedLieHom (R := ℚ) d).completedMap
          (SkewLieAlgebra.rayExp βℚ hβℚ hn hn0 (c • negDilogNeg ℚ))) x) := by
  subst hs
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    D.isPositive_completedBCHAction_rayExp_zsmul (R := ℚ) d hn hn0 Qpr (Int.castRingHom ℚ) s hx

omit [Module.Free ℤ N] in
/-- A finite product of labels whose principal actions preserve the coefficients with integer
monomial coefficients has the same property. -/
private theorem isPositive_completedBCHAction_list_prod (L : List (d.completedBCHGroup 𝓛ℚ))
    (hL : ∀ y ∈ L, ∀ x : (Fℚ).completion,
      (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x →
        (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
          ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
            ((D.principalGradedLieHom (R := ℚ) d).completedMap y) x))
    {x : (Fℚ).completion} (hx : (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x) :
    (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
      ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
        ((D.principalGradedLieHom (R := ℚ) d).completedMap L.prod) x) := by
  induction L generalizing x with
  | nil => simpa only [List.prod_nil, map_one, AlgEquiv.one_apply] using hx
  | cons y L ih =>
    simp only [List.prod_cons, map_mul, AlgEquiv.mul_apply]
    exact hL y List.mem_cons_self _ (ih (fun z hz => hL z (List.mem_cons_of_mem y hz)) hx)

/-- **Integrality of the exponents of a product of dilogarithm powers.** Let
`C = Ψ[m₁]^{c₁} ⋯ Ψ[m_r]^{c_r}` be a finite product of rational powers of dilogarithm
elements at pairwise distinct nonzero allowed degrees, in any order. If a completed skew label
`g` agrees with `C` at order `k` and its principal action preserves the completed coefficients
with integer monomial coefficients, then every exponent `cᵢ` with `deg mᵢ ≤ k` is an integer
multiple of `κ(mᵢ)`, so that `Ψ[mᵢ]^{cᵢ}` is an integral power of the normalized factor
`Ψ[mᵢ]^{κ(mᵢ)}`. By induction on `deg mᵢ`, the factors of smaller degree act integrally;
removing them leaves a label whose lowest coefficient in degree `mᵢ` is `cᵢ X_{mᵢ}`. -/
theorem exists_eq_intCast_mul_rayIndex_of_projection_eq_prod [Module.Free ℤ D.sublattice]
    {r : ℕ} (m : Fin r → D.unfrozen) (hm : ∀ i, m i ∈ d.monoid) (hm0 : ∀ i, m i ≠ 0)
    (hinj : Function.Injective m) (c : Fin r → ℚ) {g : d.completedBCHGroup 𝓛ℚ}
    (hg : ∀ x : (Fℚ).completion,
      (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x →
        (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
          ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
            ((D.principalGradedLieHom (R := ℚ) d).completedMap g) x))
    {k : ℕ}
    (hk : CompletedGroup.projection k g = CompletedGroup.projection k
      (List.ofFn fun i => SkewLieAlgebra.rayExp βℚ hβℚ (hm i) (hm0 i) (c i • negDilogNeg ℚ)).prod)
    (i : Fin r) (hi : d.degree (m i) ≤ k) :
    ∃ s : ℤ, c i = s * D.sublattice.toAddSubgroup.rayIndex (m i) := by
  classical
  rw [List.ofFn_eq_map] at hk
  suffices H : ∀ ℓ : ℕ, ∀ i, (d.degree (m i)).toNat = ℓ → d.degree (m i) ≤ k →
      ∃ s : ℤ, c i = s * D.sublattice.toAddSubgroup.rayIndex (m i) from H _ i rfl hi
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ IH =>
  intro i hiℓ hik
  have hdi := d.degree_pos (hm i) (hm0 i)
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, ℓ = a + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨hmem, hc⟩ := SkewLieAlgebra.inv_prod_filter_mul_mem_and_logComponent
    βℚ hβℚ m hm hm0 hinj c hk i (a := a) (by omega) (by omega)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Fin r → d.completedBCHGroup 𝓛ℚ, Ψ = fun j =>
    SkewLieAlgebra.rayExp βℚ hβℚ (hm j) (hm0 j) (c j • negDilogNeg ℚ) := ⟨_, rfl⟩
  rw [← hΨ] at hmem hc
  obtain ⟨w, hw⟩ : ∃ w, w =
      (((List.finRange r).filter fun j => d.degree (m j) < d.degree (m i)).map Ψ).prod :=
    ⟨_, rfl⟩
  rw [← hw] at hmem hc
  -- Labels whose principal action preserves integral coefficients form a monoid.
  obtain ⟨P, hP⟩ : ∃ P : d.completedBCHGroup 𝓛ℚ → Prop, P = fun h => ∀ x : (Fℚ).completion,
      (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x →
        (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
          ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
            ((D.principalGradedLieHom (R := ℚ) d).completedMap h) x) := ⟨_, rfl⟩
  have hPprod (L : List (d.completedBCHGroup 𝓛ℚ)) (hL : ∀ y ∈ L, P y) : P L.prod := by
    subst hP
    exact fun x hx => D.isPositive_completedBCHAction_list_prod d
      L hL hx
  -- The factors of smaller degree have integral exponents, so the inverse of their product
  -- acts integrally.
  have hPw : P w⁻¹ := by
    rw [hw, List.prod_inv_reverse]
    refine hPprod _ fun y hy => ?_
    simp only [List.mem_reverse, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hy
    obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := hy
    have := d.degree_pos (hm j) (hm0 j)
    obtain ⟨s, hs⟩ := IH _ (by omega) j rfl (by omega)
    rw [hΨ, ← SkewLieAlgebra.rayExp_neg, ← neg_smul, hP]
    exact fun z hz => D.isPositive_completedBCHAction_rayExp_of_eq d (hm j) (hm0 j)
      (s := -s) (by rw [hs, Int.cast_neg, neg_mul]) hz
  have hPh : P (w⁻¹ * g) := by
    have h₂ := hPprod [w⁻¹, g] fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      exacts [hPw, hP ▸ hg]
    simpa only [List.prod_cons, List.prod_nil, mul_one] using h₂
  rw [hP] at hPh
  obtain ⟨s, hs⟩ := RingHom.mem_rangeS.mp
    (D.algebraMap_inv_rayIndex_mul_mem_rangeS_of_isPositive (R := ℚ) d (hm i) (hm0 i)
      (Int.castRingHom ℚ) (hiℓ ▸ hmem) hPh hc)
  have hκ := D.sublattice.toAddSubgroup.rayIndex_pos (n := (m i : N))
    (fun h => hm0 i (Subtype.ext h))
  refine ⟨s, ?_⟩
  rw [eq_intCast, Algebra.algebraMap_self, RingHom.id_apply] at hs
  rw [hs, mul_comm _ (c i), mul_assoc, inv_mul_cancel₀ hκ.ne', mul_one]

/-- A finite product of dilogarithm powers `Ψ[mᵢ]^{cᵢ}` with every `cᵢ ∈ κ(mᵢ) ℤ` preserves
integral principal coefficients. -/
private theorem isPositive_completedBCHAction_ofFn_prod_rayExp {r : ℕ} (m : Fin r → D.unfrozen)
    (hm : ∀ i, m i ∈ d.monoid) (hm0 : ∀ i, m i ≠ 0) (c : Fin r → ℚ)
    (h : ∀ i, ∃ s : ℤ, c i = s * D.sublattice.toAddSubgroup.rayIndex (m i))
    {x : (Fℚ).completion} (hx : (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x) :
    (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
      ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
        ((D.principalGradedLieHom (R := ℚ) d).completedMap (List.ofFn fun i =>
          SkewLieAlgebra.rayExp βℚ hβℚ (hm i) (hm0 i) (c i • negDilogNeg ℚ)).prod) x) := by
  have hfac : ∀ j, ∀ z : (Fℚ).completion,
      (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS z →
        (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
          ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
            ((D.principalGradedLieHom (R := ℚ) d).completedMap
              (SkewLieAlgebra.rayExp βℚ hβℚ (hm j) (hm0 j) (c j • negDilogNeg ℚ))) z) :=
    fun j z hz => (h j).elim fun s hs =>
      D.isPositive_completedBCHAction_rayExp_of_eq d (hm j) (hm0 j) hs hz
  refine D.isPositive_completedBCHAction_list_prod d _ (fun y hy => ?_) hx
  rw [List.ofFn_eq_map, List.mem_map] at hy
  obtain ⟨j, -, rfl⟩ := hy
  exact hfac j

/-- **Integrality criterion for products of dilogarithm powers.** A finite product
`Ψ[m₁]^{c₁} ⋯ Ψ[m_r]^{c_r}` of rational powers of dilogarithm elements at pairwise distinct
nonzero allowed degrees, in any order, preserves the completed principal coefficients with
integer monomial coefficients if and only if every exponent `cᵢ` is an integer multiple of
`κ(mᵢ)`. -/
theorem forall_isPositive_completedBCHAction_prod_rayExp_iff [Module.Free ℤ D.sublattice]
    {r : ℕ} (m : Fin r → D.unfrozen) (hm : ∀ i, m i ∈ d.monoid) (hm0 : ∀ i, m i ≠ 0)
    (hinj : Function.Injective m) (c : Fin r → ℚ) :
    (∀ x : (Fℚ).completion,
      (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS x →
        (Fℚ).IsPositive (mapRingHom Qpr (Int.castRingHom ℚ)).rangeS
          ((Fℚ).completedBCHAction (R := ℚ) e (tropicalVertexGrading (R := ℚ) e ρ)
            ((D.principalGradedLieHom (R := ℚ) d).completedMap (List.ofFn fun i =>
              SkewLieAlgebra.rayExp βℚ hβℚ (hm i) (hm0 i) (c i • negDilogNeg ℚ)).prod) x)) ↔
      ∀ i, ∃ s : ℤ, c i = s * D.sublattice.toAddSubgroup.rayIndex (m i) := by
  constructor
  · intro h i
    exact D.exists_eq_intCast_mul_rayIndex_of_projection_eq_prod d m hm hm0 hinj c h rfl i
      (Int.self_le_toNat _)
  · intro h x hx
    exact D.isPositive_completedBCHAction_ofFn_prod_rayExp d m hm hm0 c h hx

end Product

end Mei.SkewLatticeDatum
