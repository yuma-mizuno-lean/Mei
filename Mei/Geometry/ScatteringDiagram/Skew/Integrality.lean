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

This integrality criterion is the one used to show that the exponents in the ordered
factorization of a rank-two product of normalized dilogarithm powers are integers, so that
its factors are again of the form `Ψ[tn]^(s κ(tn))` with `s` an integer.

## Main statements

* `Mei.SkewLatticeDatum.isPositive_completedBCHAction_rayExp_zsmul`: integral powers
  `Ψ[n]^(s κ(n))` preserve `S`-integral coefficients.
* `Mei.SkewLatticeDatum.algebraMap_div_rayIndex_mem_rangeS_of_isPositive`: if `Ψ[n]^c`
  preserves `S`-integral coefficients, then `c / κ(n)` lies in the image of `S`.
* `Mei.SkewLatticeDatum.forall_isPositive_completedBCHAction_rayExp_iff`: over `ℚ`, `Ψ[n]^c`
  preserves integral coefficients if and only if `c` is an integer multiple of `κ(n)`.

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2, the lemma
  that `Ψ[tn]^(s δ(tn))` acts on `ℤ[[P̃]]` if and only if `s` is an integer,
  arXiv:2111.00800v6.
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

variable {S : Type*} [CommSemiring S]
  [Fact ((D.principalPositiveDegrees d).monoid ≤ D.principalCoefficientMonoid d)]

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

end Mei.SkewLatticeDatum
