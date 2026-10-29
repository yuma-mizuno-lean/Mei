/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Embedding
public import Mei.Algebra.Lie.Skew.Ray
public import Mei.Algebra.Lie.Logarithmic.WallFunction
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Log
public import Mei.RingTheory.PowerSeries.EulerDerivInv

/-!
# Principal actions of arbitrary ray functions

For an integer scale `s`, a scalar ray potential `a(T)` defines a skew label with
logarithm `s κ(n) ∑ a_j X_{jn}`. Its principal image is the tangent label with
logarithmic coefficient `T * derivative a` at the integral normal `s κ(n) νₙ`,
because the normal in degree `jn` is `j νₙ`. Taking `a` to be the inverse Euler
derivation of `logOf f` gives the wall function `f` at the integral normal
`s κ(n) νₙ` (equivalently `f^s` at `κ(n) νₙ`) for every scalar series with constant
coefficient one. The resulting action uses powers in units, so it includes
negative normal weights and inverse crossings.

This connects `SkewLieAlgebra.rayExp`, `principalGradedLieHom`, and
`completedTropicalTangentField`; formal logarithms and finite nilpotent evaluation
supply the passage to arbitrary functions. The normalization and action are those
of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
and Appendix B, arXiv:1411.1394v2, and Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
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

omit [Module.Free ℤ N] [Algebra ℚ R] [DecidableEq D.unfrozen]
  [DecidableEq (Module.Dual ℤ D.sublattice)] in
include hn hn0 in
/-- The monomial at the principal embedding of a positive degree lies in the first
completed ideal, for any coefficient monoid containing it. -/
theorem toCompletion_single_principalEmbedding_mem_first
    (P : AddSubmonoid Lpr) (q : P) (hq : q.val = D.principalEmbedding n) :
    (TropicalVertexCoefficientAction.filtration (R := R) e P).toCompletion (single q 1) ∈
      (TropicalVertexCoefficientAction.filtration (R := R) e P).completionIdeal 1 := by
  have hpos : (q : Lpr) ∈ (e).monoid := by
    rw [hq, principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
    exact ⟨hn, rfl⟩
  have hdegree : (1 : ℤ) ≤ (e).degree q := by
    rw [hq, principalEmbedding_apply, PositiveDegrees.graph_degree]
    exact d.degree_pos hn hn0
  rw [AlgFiltration.toCompletion_mem_completionIdeal_iff,
    TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  exact Or.inr ⟨q, hpos, hdegree, 0, by simp⟩

section Potential

variable (a b : PowerSeries R) (hab : X * d⁄dX a = b)

include hab

private theorem principal_rayGenerator (q : T) (hq : q.val = D.principalEmbedding n)
    (j : ℕ) :
    D.principalGradedLieHom d
        (SkewLieAlgebra.rayGenerator β hβ hn hn0 j
          (PowerSeries.coeff (j + 1) (κ • a))) =
      tropicalTangentField e ρ χ
        (single ((j + 1) • q) (PowerSeries.coeff (j + 1) b)) := by
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
    D.intCast_principalNormal_apply, map_mul, map_intCast, smul_eq_mul]
  have hc : ((j + 1 : ℕ) : R) * PowerSeries.coeff (j + 1) a = PowerSeries.coeff (j + 1) b := by
    simpa only [coeff_succ_X_mul, coeff_derivative, Nat.cast_add, Nat.cast_one, mul_comm] using
      congrArg (PowerSeries.coeff (j + 1)) hab
  simp only [Nat.cast_add, Nat.cast_one] at hc ⊢
  linear_combination (s : R) * algebraMap ℚ R
    (D.sublattice.toAddSubgroup.rayIndex n) * D.principalEvaluation n p * hc

private theorem principal_rayPartialSum (q : T) (hq : q.val = D.principalEmbedding n)
    (k : ℕ) :
    D.principalGradedLieHom d
        (SkewLieAlgebra.rayPartialSum β hβ hn hn0 k (κ • a)) =
      tropicalTangentField e ρ χ (∑ j ∈ Finset.range k,
        single ((j + 1) • q) (PowerSeries.coeff (j + 1) b)) := by
  rw [SkewLieAlgebra.rayPartialSum_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    D.principal_rayGenerator (R := R) d hn hn0 s a b hab q hq j

private theorem principal_rayPartialSum_projection (q : T)
    (hq : q.val = D.principalEmbedding n) (u : (G).completionIdeal 1)
    (hu : u.val = (G).toCompletion (single q 1)) (k : ℕ) :
    ((e).degreeIdeal ℳ k).mkQ (D.principalGradedLieHom d
        (SkewLieAlgebra.rayPartialSum β hβ hn hn0 k (κ • a))) =
      LieIdeal.completionProjection ((e).degreeIdeal ℳ) ((e).degreeIdeal_antitone ℳ) k
        (completedTropicalTangentField e ρ χ ((G).completedAeval u b)) := by
  have hb0 : constantCoeff b = 0 := by rw [← hab]; simp
  let v : R[T] := ∑ j ∈ Finset.range k,
    single ((j + 1) • q) (PowerSeries.coeff (j + 1) b)
  have hv : (G).projection k ((G).completedAeval u b) =
      Ideal.Quotient.mk _ v := by
    rw [AlgFiltration.projection_completedAeval_eq_sum]
    simp only [hu, AlgFiltration.projection_toCompletion]
    rw [Finset.sum_range_succ']
    simp only [coeff_zero_eq_constantCoeff_apply, hb0, zero_smul, add_zero]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← map_pow, single_pow, one_pow]
    simpa only [smul_single, smul_eq_mul, mul_one, Ideal.Quotient.mkₐ_eq_mk] using
      (map_smul (Ideal.Quotient.mkₐ R ((G).ideal (k + 1)))
        (PowerSeries.coeff (j + 1) b) (single ((j + 1) • q) (1 : R))).symm
  rw [completionProjection_completedTropicalTangentField e ρ χ k _ v hv]
  exact congrArg (((e).degreeIdeal ℳ k).mkQ)
    (D.principal_rayPartialSum (R := R) d hn hn0 s a b hab q hq k)

omit b hab in
/-- Mapping a skew ray exponential into the principal tropical algebra
multiplies its scalar coefficients by their degree. Thus the scalar potential
`a` gives tangent logarithmic coefficient `X * derivative a`. -/
theorem principalGradedLieHom_completedMap_rayExp (q : T) (hq : q.val = D.principalEmbedding n)
    (u : (G).completionIdeal 1) (hu : u.val = (G).toCompletion (single q 1)) :
    (D.principalGradedLieHom d).completedMap
        (SkewLieAlgebra.rayExp β hβ hn hn0 (κ • a)) =
      (e).completedBCHExp ℳ
        (completedTropicalTangentField e ρ χ ((G).completedAeval u (X * d⁄dX a))) := by
  apply CompletedGroup.ext
  intro k
  have hp := (D.principalGradedLieHom (R := R) d).projection_completedMap_of_le k
    (a := k) (by simp)
    (SkewLieAlgebra.rayExp β hβ hn hn0 (κ • a))
  refine hp.trans ?_
  refine (congrArg
    ((D.principalGradedLieHom (R := R) d).truncatedMap k (a := k) (by simp)).bchGroupMap
    (SkewLieAlgebra.projection_rayExp β hβ hn hn0 k (κ • a))).trans ?_
  refine (LieHom.bchGroupMap_exp _ _).trans ?_
  have hm := (D.principalGradedLieHom (R := R) d).truncatedMap_mk k
    (a := k) (by simp) (SkewLieAlgebra.rayPartialSum β hβ hn hn0 k (κ • a))
  have hm' := congrArg BCHGroup.exp hm
  simp only [← LieIdeal.mkQ_apply] at hm'
  refine hm'.trans ?_
  have he := (e).projection_completedBCHExp ℳ k
    (completedTropicalTangentField e ρ χ ((G).completedAeval u (X * d⁄dX a)))
  exact (congrArg BCHGroup.exp
    (D.principal_rayPartialSum_projection (R := R) d hn hn0 s a (X * d⁄dX a) rfl q hq u hu k)).trans
      he.symm


end Potential

private theorem principal_rayLog (f : PowerSeries R) (hf : constantCoeff f = 1)
    (q : T) (hq : q.val = D.principalEmbedding n)
    (u : (G).completionIdeal 1) (hu : u.val = (G).toCompletion (single q 1)) :
    (D.principalGradedLieHom d).completedMap
        (SkewLieAlgebra.rayExp β hβ hn hn0 (κ • eulerDerivInv (logOf f))) =
      (e).completedBCHExp ℳ (completedTropicalTangentField e ρ χ
        ((G).completedLog ⟨(G).completedAeval u f,
          (G).completedAeval_sub_one_mem_first u f hf⟩)) := by
  have hlabel := D.principalGradedLieHom_completedMap_rayExp (R := R) d hn hn0 s
    (eulerDerivInv (logOf f)) q hq u hu
  have hlog := (congrArg ((G).completedAeval u)
    (X_mul_derivative_eulerDerivInv (logOf f) (constantCoeff_logOf hf))).trans
      ((G).completedAeval_logOf u f hf)
  exact hlabel.trans (congrArg (fun x =>
    (e).completedBCHExp ℳ (completedTropicalTangentField e ρ χ x)) hlog)


open TropicalVertexCoefficientAction

variable (Q : AddSubmonoid (Module.Dual ℤ D.sublattice × D.unfrozen))
  [Fact ((D.principalPositiveDegrees d).monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) e Q

/-- The principal image of the normalized skew ray label with scalar potential
`eulerDerivInv (logOf f)` acts with wall function `f(z^(r(n)))` at the integral
normal `s κ(n) νₙ`. The unit `fQ` specifies that evaluated ray function.
This allows arbitrary constant-one scalar series, coefficient monoids containing
the positive degrees, radical degrees, and negative powers. -/
theorem completedBCHAction_completedMap_rayExp_eulerDerivInv_logOf
    (f : PowerSeries R) (hconst : constantCoeff f = 1)
    (q : Q) (hq : q.val = D.principalEmbedding n)
    (uQ : (F).completionIdeal 1) (huQ : uQ.val = (F).toCompletion (single q 1))
    (fQ : (F).completionˣ) (hfQ : (fQ : (F).completion) = (F).completedAeval uQ f)
    (p : Q) (c : R) :
    (F).completedBCHAction (R := R) e ℳ
        ((D.principalGradedLieHom d).completedMap
          (SkewLieAlgebra.rayExp β hβ hn hn0 (κ • eulerDerivInv (logOf f))))
        ((F).toCompletion (single p c)) =
      ((fQ ^ (s * D.principalNormal n p.val) : (F).completionˣ) : (F).completion) *
        (F).toCompletion (single p c) := by
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
  let u : (G).completionIdeal 1 := ⟨(G).toCompletion (single t 1),
    D.toCompletion_single_principalEmbedding_mem_first d hn hn0 T t ht⟩
  have hlabel := D.principal_rayLog (R := R) d hn hn0 s f hconst t ht u rfl
  refine (congrArg (fun z =>
    (F).completedBCHAction (R := R) e ℳ z ((F).toCompletion (single p c))) hlabel).trans ?_
  have hg : (G).completedAeval u f - 1 ∈ (G).completionIdeal 1 :=
    (G).completedAeval_sub_one_mem_first u f hconst
  have hmono : completedTropicalTangentInclusion e ρ χ Q u.val = uQ.val := by
    calc
      _ = (F).toCompletion (single q 1) := by
        rw [completedTropicalTangentInclusion_toCompletion]
        apply congrArg (F).toCompletion
        rw [tropicalTangentInclusion, mapDomainAlgHom_apply, mapDomain_single]
        congr 1
        exact Subtype.ext (ht.trans hq.symm)
      _ = uQ := huQ.symm
  have hinc := (completedTropicalTangentInclusion_completedAeval e ρ χ Q u f).trans
    (congrArg (fun x => (F).completedAeval x f) (Subtype.ext hmono))
  have hunit : (isUnit_completedTropicalTangentInclusion e ρ χ Q hg).unit = fQ := by
    apply Units.ext
    exact (IsUnit.unit_spec _).trans (hinc.trans hfQ.symm)
  simpa only [hunit, AddMonoidHom.id_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.smul_apply, smul_eq_mul] using
    completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog
      e ρ Q ((s • D.principalNormal n).toAddMonoidHom) hg p c

end Mei.SkewLatticeDatum
