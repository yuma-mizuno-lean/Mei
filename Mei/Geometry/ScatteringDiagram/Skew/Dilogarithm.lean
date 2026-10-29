/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.RayAction
public import Mei.Algebra.Lie.Skew.Dilogarithm

/-!
# Binomial wall functions of normalized dilogarithm labels

The principal image of `Ψ[n]^κ(n)` has wall function `1 + z^(r(n))`
with respect to the primitive integral principal normal `κ(n)νₙ`.
The factor `j` from `ν_{jn} = j νₙ` changes the dilogarithm coefficient
`(-1)^(j+1)/j²` into the logarithm coefficient `(-1)^(j+1)/j`.
This retains radical degrees and requires no nondegeneracy of the skew form.

The construction uses `SkewLieAlgebra.rayExp`, `principalGradedLieHom`, and
the arbitrary ray-function formula in `Skew.RayAction`.
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
local notation "ℳ" => tropicalVertexGrading (R := R) e ρ
local notation "β" => D.coefficientForm R
local notation "hβ" => D.isAlt_coefficientForm R
local notation "κ" => algebraMap ℚ R ((s : ℚ) * D.sublattice.toAddSubgroup.rayIndex n)

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
  have hpos : (q : Lpr) ∈ (e).monoid := by
    rw [hq, principalEmbedding_apply, PositiveDegrees.mem_graph_monoid]
    exact ⟨hn, rfl⟩
  have hdegree : (1 : ℤ) ≤ (e).degree q := by
    rw [hq, principalEmbedding_apply, PositiveDegrees.graph_degree]
    exact d.degree_pos hn hn0
  have hfirst : (F).toCompletion (single q (1 : R)) ∈ (F).completionIdeal 1 := by
    rw [AlgFiltration.toCompletion_mem_completionIdeal_iff, filtration_ideal,
      AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
    exact Or.inr ⟨q, hpos, hdegree, 0, by simp⟩
  let u : (F).completionIdeal 1 := ⟨(F).toCompletion (single q 1), hfirst⟩
  have hfu : (f : (F).completion) = (F).completedAeval u (1 + X : PowerSeries R) := by
    simpa only [map_add, map_one, AlgFiltration.completedAeval_X] using hf
  simpa only [logOf_one_add_X, eulerIntegral_log] using
    D.completedBCHAction_completedMap_rayExp_eulerIntegral_logOf d hn hn0 s Q
      (1 + X : PowerSeries R) (by simp) q hq u rfl f hfu p c

end Mei.SkewLatticeDatum
