/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Embedding
public import Mei.Algebra.Lie.Skew.Dilogarithm
public import Mei.Algebra.Lie.Logarithmic.WallFunction
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Log

/-!
# Binomial wall functions of normalized dilogarithm labels

The principal image of `Ψ[n]^κ(n)` has wall function `1 + z^(r(n))`
with respect to the primitive integral principal normal `κ(n)νₙ`.
The factor `j` from `ν_{jn} = j νₙ` changes the dilogarithm coefficient
`(-1)^(j+1)/j²` into the logarithm coefficient `(-1)^(j+1)/j`.
This retains radical degrees and requires no nondegeneracy of the skew form.

The construction uses `SkewLieAlgebra.rayExp`, `principalGradedLieHom`,
`completedTropicalTangentField` and the tropical wall-function formula.
The normalization follows Nakanishi, *Cluster algebras and scattering diagrams,
Part III*, §5.1, arXiv:2111.00800v6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open _root_.AddMonoidAlgebra PowerSeries

variable {N R : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [CommRing R] [Algebra ℚ R] (D : SkewLatticeDatum N)
  (d : PositiveDegrees D.unfrozen) [DecidableEq D.unfrozen]
  [DecidableEq (Module.Dual ℤ D.sublattice)]
  {n : D.unfrozen} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (s : ℤ)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "e" => D.principalPositiveDegrees d
local notation "ρ" => AddMonoidHom.id Lpr
local notation "χ" => AddMonoidHom.comp (Int.castAddHom R)
  (LinearMap.toAddMonoidHom (s • D.principalNormal n))
local notation "T" => tropicalTangentMonoid e ρ χ
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) e T
local notation "ℳ" => tropicalVertexGrading (R := R) e ρ
local notation "β" => D.coefficientForm R
local notation "hβ" => D.isAlt_coefficientForm R
local notation "κ" => algebraMap ℚ R ((s : ℚ) * D.sublattice.toAddSubgroup.rayIndex n)

private theorem normalized_rayGenerator (q : T) (hq : q.val = D.principalEmbedding n)
    (j : ℕ) :
    D.principalGradedLieHom d
        (SkewLieAlgebra.rayGenerator β hβ hn hn0 j
          (PowerSeries.coeff (j + 1) (κ • negDilogNeg R))) =
      tropicalTangentField e ρ χ
        (single ((j + 1) • q) (PowerSeries.coeff (j + 1) (log R))) := by
  have hne : (((j + 1) • q : T) : Lpr) ≠ 0 := by
    rw [AddSubmonoidClass.coe_nsmul, hq, ← map_nsmul]
    exact fun h => d.succ_nsmul_ne_zero hn hn0 j
      (D.principalEmbedding_injective (h.trans (map_zero _).symm))
  apply Subtype.ext
  rw [coe_principalGradedLieHom_apply, SkewLieAlgebra.coe_rayGenerator,
    principalLieHom_single, coe_tropicalTangentField_single _ _ _ hne]
  apply (LogarithmicVectorField.toFinsupp ρ).injective
  simp only [map_smul, toFinsupp_principalField, LogarithmicVectorField.toFinsupp_single,
    Finsupp.smul_single]
  rw [AddSubmonoidClass.coe_nsmul, hq, ← map_nsmul]
  congr 1
  ext p
  simp only [AddMonoidHom.smul_apply, map_nsmul,
    nsmul_eq_mul, AddMonoidHom.comp_apply, Int.coe_castAddHom,
    LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply, Int.cast_mul,
    D.intCast_principalNormal_apply, map_mul, map_intCast, coeff_succ_negDilogNeg,
    coeff_log, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, smul_eq_mul]
  have hc : ((j + 1 : ℕ) : R) *
      algebraMap ℚ R ((-1) ^ j / ((j : ℚ) + 1) ^ 2) =
      algebraMap ℚ R ((-1) ^ (j + 2) / ((j : ℚ) + 1)) := by
    have hcast : ((j + 1 : ℕ) : R) = algebraMap ℚ R ((j : ℚ) + 1) := by simp
    rw [hcast, ← map_mul]
    congr 1
    field_simp
    ring
  simp only [Nat.cast_add, Nat.cast_one] at hc ⊢
  linear_combination (s : R) * algebraMap ℚ R
    (D.sublattice.toAddSubgroup.rayIndex n) * D.principalEvaluation n p * hc

private theorem normalized_rayPartialSum (q : T) (hq : q.val = D.principalEmbedding n)
    (k : ℕ) :
    D.principalGradedLieHom d
        (SkewLieAlgebra.rayPartialSum β hβ hn hn0 k (κ • negDilogNeg R)) =
      tropicalTangentField e ρ χ (∑ j ∈ Finset.range k,
        single ((j + 1) • q) (PowerSeries.coeff (j + 1) (log R))) := by
  rw [SkewLieAlgebra.rayPartialSum_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    D.normalized_rayGenerator (R := R) d hn hn0 s q hq j

private theorem normalized_rayPartialSum_projection (q : T)
    (hq : q.val = D.principalEmbedding n) (u : (G).completionIdeal 1)
    (hu : u.val = (G).toCompletion (single q 1)) (k : ℕ) :
    ((e).degreeIdeal ℳ k).mkQ (D.principalGradedLieHom d
        (SkewLieAlgebra.rayPartialSum β hβ hn hn0 k (κ • negDilogNeg R))) =
      LieIdeal.completionProjection ((e).degreeIdeal ℳ) ((e).degreeIdeal_antitone ℳ) k
        (completedTropicalTangentField e ρ χ ((G).completedAeval u (log R))) := by
  let v : R[T] := ∑ j ∈ Finset.range k,
    single ((j + 1) • q) (PowerSeries.coeff (j + 1) (log R))
  have hv : (G).projection k ((G).completedAeval u (log R)) =
      Ideal.Quotient.mk _ v := by
    rw [AlgFiltration.projection_completedAeval_eq_sum]
    simp only [hu, AlgFiltration.projection_toCompletion]
    rw [Finset.sum_range_succ']
    simp only [coeff_zero_eq_constantCoeff_apply, constantCoeff_log, zero_smul, add_zero]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← map_pow, single_pow, one_pow]
    simpa only [smul_single, smul_eq_mul, mul_one, Ideal.Quotient.mkₐ_eq_mk] using
      (map_smul (Ideal.Quotient.mkₐ R ((G).ideal (k + 1)))
        (PowerSeries.coeff (j + 1) (log R)) (single ((j + 1) • q) (1 : R))).symm
  rw [completionProjection_completedTropicalTangentField e ρ χ k _ v hv]
  exact congrArg (((e).degreeIdeal ℳ k).mkQ)
    (D.normalized_rayPartialSum (R := R) d hn hn0 s q hq k)

private theorem normalized_rayExp (q : T) (hq : q.val = D.principalEmbedding n)
    (u : (G).completionIdeal 1) (hu : u.val = (G).toCompletion (single q 1)) :
    (D.principalGradedLieHom d).completedMap
        (SkewLieAlgebra.rayExp β hβ hn hn0 (κ • negDilogNeg R)) =
      (e).completedBCHExp ℳ
        (completedTropicalTangentField e ρ χ ((G).completedAeval u (log R))) := by
  apply CompletedGroup.ext
  intro k
  have hp := (D.principalGradedLieHom (R := R) d).projection_completedMap_of_le k
    (a := k) (by simp)
    (SkewLieAlgebra.rayExp β hβ hn hn0 (κ • negDilogNeg R))
  refine hp.trans ?_
  refine (congrArg
    ((D.principalGradedLieHom (R := R) d).truncatedMap k (a := k) (by simp)).bchGroupMap
    (SkewLieAlgebra.projection_rayExp β hβ hn hn0 k (κ • negDilogNeg R))).trans ?_
  refine (LieHom.bchGroupMap_exp _ _).trans ?_
  have hm := (D.principalGradedLieHom (R := R) d).truncatedMap_mk k
    (a := k) (by simp) (SkewLieAlgebra.rayPartialSum β hβ hn hn0 k (κ • negDilogNeg R))
  have hm' := congrArg BCHGroup.exp hm
  simp only [← LieIdeal.mkQ_apply] at hm'
  refine hm'.trans ?_
  have he := (e).projection_completedBCHExp ℳ k
    (completedTropicalTangentField e ρ χ ((G).completedAeval u (log R)))
  exact (congrArg BCHGroup.exp
    (D.normalized_rayPartialSum_projection (R := R) d hn hn0 s q hq u hu k)).trans he.symm

open TropicalVertexCoefficientAction

variable (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees d).monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q

/-- The normalized dilogarithm factor `Ψ[n]^(s κ(n))` acts with the binomial
wall function `(1 + z^(r(n)))^s` at the integral principal normal `κ(n)νₙ`.
The rational power is expressed by scaling its logarithmic ray series.
The unit `f` is specified by its value `1 + z^(r(n))`; negative exponents are
unit powers. Any coefficient monoid containing the positive degrees is allowed. -/
theorem completedBCHAction_completedMap_rayExp_smul_negDilogNeg (q : Q)
    (hq : q.val = D.principalEmbedding n) (f : (F).completionˣ)
    (hf : (f : (F).completion) = 1 + (F).toCompletion (single q 1)) (p : Q) (c : R) :
    (F).completedBCHAction (R := R) e ℳ
        ((D.principalGradedLieHom d).completedMap
          (SkewLieAlgebra.rayExp β hβ hn hn0 (κ • negDilogNeg R)))
        ((F).toCompletion (single p c)) =
      ((f ^ (s * D.principalNormal n p.val) : (F).completionˣ) : (F).completion) *
        (F).toCompletion (single p c) := by
  -- Construct the positive tangent monomial and its binomial unit.
  have hpos : D.principalEmbedding n ∈ (e).monoid := by
    rw [principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
    exact ⟨hn, rfl⟩
  have htan : χ (D.principalEmbedding n) = 0 := by
    simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom, LinearMap.toAddMonoidHom_coe,
      LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, D.intCast_principalNormal_apply,
      principalEmbedding_apply, principalEvaluation_principalEmbedding, form_self,
      map_zero, mul_zero]
  let t : T := ⟨D.principalEmbedding n, (mem_tropicalTangentMonoid e ρ χ _).mpr
    ⟨hpos, htan⟩⟩
  have ht : (t : Lpr) = D.principalEmbedding n := rfl
  have hdegree : (1 : ℤ) ≤ (e).degree t := by
    rw [ht, principalEmbedding_apply, PositiveDegrees.graph_degree]
    exact d.degree_pos hn hn0
  have hfirst : (G).toCompletion (single t (1 : R)) ∈ (G).completionIdeal 1 := by
    rw [AlgFiltration.toCompletion_mem_completionIdeal_iff, filtration_ideal,
      AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
    exact Or.inr ⟨t, hpos, hdegree, 0, by simp⟩
  let u : (G).completionIdeal 1 := ⟨(G).toCompletion (single t 1), hfirst⟩
  let g : (G).completion := 1 + u
  have hg : g - 1 ∈ (G).completionIdeal 1 := by
    simpa only [g, add_sub_cancel_left] using hfirst
  -- Identify the normalized label with the logarithm of the binomial.
  have hlabel := D.normalized_rayExp (R := R) d hn hn0 s t ht u rfl
  have hlog := (G).completedAeval_log (R := R) u
  have hlabel' := hlabel.trans (congrArg (fun x =>
    (e).completedBCHExp ℳ (completedTropicalTangentField e ρ χ x)) hlog)
  refine (congrArg (fun z =>
    (F).completedBCHAction (R := R) e ℳ z ((F).toCompletion (single p c))) hlabel').trans ?_
  -- Apply the integral-normal wall formula and identify its unit.
  have ha := completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog
    e ρ Q ((s • D.principalNormal n).toAddMonoidHom) hg p c
  have hinc : completedTropicalTangentInclusion e ρ χ Q g = f := by
    simp only [g, u, map_add, map_one, completedTropicalTangentInclusion_toCompletion]
    rw [hf]
    congr 2
    rw [mapDomainAlgHom_apply, mapDomain_single]
    congr 1
    exact Subtype.ext (ht.trans hq.symm)
  have hunit : (isUnit_completedTropicalTangentInclusion e ρ χ Q hg).unit = f := by
    apply Units.ext
    exact (IsUnit.unit_spec _).trans hinc
  simpa only [hunit, AddMonoidHom.id_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.smul_apply, smul_eq_mul] using ha

end Mei.SkewLatticeDatum
