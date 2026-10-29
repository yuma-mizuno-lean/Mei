/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Algebra
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Theta
public import Mei.LinearAlgebra.ModuleFiltration.Basis
public import Mei.RingTheory.FilteredAlgebra.Module
public import Mei.RingTheory.MvPowerSeries.Completion

/-!
# Completed coefficient expansions of the focus-focus algebra

Complete the focus-focus algebra over the one-variable polynomial ring in the
smoothing parameter. Its theta monomials give unique expansions with coefficients
in the power series ring. Exactly finitely many coefficients survive modulo each
power of the smoothing parameter; the full expansion may have infinite support.

We use `NodeAlgebra.laurentBasis`, `Basis.completedCoefficientsEquiv` and
`principalCompletionEquiv`. These are expansions in the algebraic monomial basis;
identification with sections obtained from broken lines is a separate statement.
The algebra follows Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3,
arXiv:0808.2749v2.
-/

public section

noncomputable section

namespace Mei.FocusFocus

open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K]

local notation "S" => MvPolynomial Unit K
local notation "t" => (MvPolynomial.X () : S)
local notation "A" => SlabNode t
local notation "I" => MvPolynomial.idealOfVars Unit K
local notation "F" => AlgFiltration.toModuleFiltration S (AlgFiltration.ofIdeal I)
local notation "b" => Mei.NodeAlgebra.laurentBasis
  (_root_.LaurentPolynomial.C t * (1 + _root_.LaurentPolynomial.T 1))

/-- The smoothing-parameter filtration on the focus-focus algebra. -/
def thetaFiltration : ModuleFiltration S A := (b).coefficientFiltration F

/-- This is the usual ideal-adic module filtration, rather than a condition
on the number of monomials in an expansion. -/
theorem thetaFiltration_submodule (k : ℕ) :
    (thetaFiltration K).submodule k = I ^ k • (⊤ : Submodule S A) := by
  ext x
  rw [thetaFiltration, Module.Basis.mem_coefficientFiltration_submodule,
    (b).mem_ideal_smul_top_iff_repr_mem]
  simp only [AlgFiltration.ofIdeal_ideal, Submodule.restrictScalars_mem]

private def scalarCompletionEquiv : (F).completion ≃ₗ[S] PowerSeries K :=
  ((AlgFiltration.ofIdeal I).moduleCompletionEquiv (R := S)).trans
    (principalCompletionEquiv Unit K).toLinearEquiv

private theorem scalarCompletionEquiv_of (x : S) :
    scalarCompletionEquiv K ((F).of x) = (x : PowerSeries K) := by
  exact (congrArg (principalCompletionEquiv Unit K)
    ((AlgFiltration.ofIdeal I).moduleCompletionEquiv_of x)).trans
      (principalCompletionEquiv_toCompletion Unit K x)

private theorem projection_scalarCompletionEquiv_symm_ne_zero (k : ℕ) (f : PowerSeries K) :
    (F).projection k ((scalarCompletionEquiv K).symm f) ≠ 0 ↔
      Ideal.Quotient.mk (I ^ (k + 1)) (f.truncTotal (k + 1)) ≠ 0 := by
  have hp := (AlgFiltration.ofIdeal I).projection_moduleCompletionEquiv_symm
    (R := S) k ((principalCompletionEquiv Unit K).symm f)
  have hq := projection_principalCompletionEquiv_symm Unit K k f
  rw [hq] at hp
  have hp' : (F).projection k ((scalarCompletionEquiv K).symm f) = _ := hp
  rw [hp']
  simp only [ne_eq, LinearEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
    AlgFiltration.ofIdeal_ideal]

/-- Power series coefficient families with only finitely many nonzero residues
modulo each power of the smoothing parameter. -/
def restrictedThetaCoefficients : Submodule S ((ℤ × ℤ) → PowerSeries K) :=
  ((F).restrictedFamilies (ℤ × ℤ)).comap
    (LinearEquiv.piCongrRight fun _ => (scalarCompletionEquiv K).symm).toLinearMap

/-- Admissibility means finite support after truncating at each order and taking
polynomial classes modulo the corresponding power of the parameter ideal. -/
@[simp]
theorem mem_restrictedThetaCoefficients (f : (ℤ × ℤ) → PowerSeries K) :
    f ∈ restrictedThetaCoefficients K ↔ ∀ k : ℕ,
      (Function.support fun i => Ideal.Quotient.mk (I ^ (k + 1))
        ((f i).truncTotal (k + 1))).Finite := by
  simp only [restrictedThetaCoefficients, Submodule.mem_comap,
    ModuleFiltration.mem_restrictedFamilies, LinearEquiv.coe_coe,
    LinearEquiv.piCongrRight_apply]
  simp only [Function.support, projection_scalarCompletionEquiv_symm_ne_zero]

/-- Completed theta monomial expansions have precisely the power series coefficients
with finite support at every cutoff. -/
def completedThetaCoefficientsEquiv : (thetaFiltration K).completion ≃ₗ[S]
    restrictedThetaCoefficients K :=
  ((b).completedCoefficientsEquiv F).trans
    ((LinearEquiv.piCongrRight fun _ => (scalarCompletionEquiv K).symm).ofSubmodule'
      ((F).restrictedFamilies (ℤ × ℤ))).symm

/-- A finite monomial expansion has its original polynomial coefficients,
viewed in the power series ring. -/
@[simp]
theorem completedThetaCoefficientsEquiv_of (x : A) (i : ℤ × ℤ) :
    (completedThetaCoefficientsEquiv K ((thetaFiltration K).of x)).val i =
      ((b).repr x i : PowerSeries K) := by
  have h := (b).completedCoefficientsEquiv_of (F) x i
  have h' := congrArg (scalarCompletionEquiv K) h
  exact h'.trans (scalarCompletionEquiv_of K ((b).repr x i))

/-- Each theta monomial is the single-coordinate expansion at its own index. -/
@[simp↓]
theorem completedThetaCoefficientsEquiv_of_theta (n w : ℤ) (i : ℤ × ℤ) :
    (completedThetaCoefficientsEquiv K ((thetaFiltration K).of (theta t n w))).val i =
      if (n, w) = i then 1 else 0 := by
  classical
  rw [completedThetaCoefficientsEquiv_of]
  have h := congrArg (fun z : A => ((b).repr z i : PowerSeries K))
    (laurentBasis_apply_eq_theta t n w)
  exact h.symm.trans (by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp)

end Mei.FocusFocus
