/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Algebra
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Theta
public import Mei.LinearAlgebra.ModuleFiltration.Basis
public import Mei.RingTheory.MvPowerSeries.Completion

/-!
# Completed coefficient expansions of the focus-focus algebra

Complete the focus-focus algebra over the one-variable polynomial ring in the
smoothing parameter. Its theta monomials give unique expansions with coefficients
in the power series ring. Exactly finitely many coefficients survive modulo each
power of the smoothing parameter; the full expansion may have infinite support.

We use `NodeAlgebra.laurentBasis`, `Basis.completedCoefficientsEquiv` and
`principalModuleCompletionEquiv`. These are expansions in the algebraic monomial basis;
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
abbrev thetaFiltration : ModuleFiltration S A := (b).coefficientFiltration F

/-- This is the usual ideal-adic module filtration, rather than a condition
on the number of monomials in an expansion. -/
theorem thetaFiltration_submodule (k : ℕ) :
    (thetaFiltration K).submodule k = I ^ k • (⊤ : Submodule S A) := by
  ext x
  rw [thetaFiltration, Module.Basis.mem_coefficientFiltration_submodule,
    (b).mem_ideal_smul_top_iff_repr_mem]
  simp only [AlgFiltration.ofIdeal_ideal, Submodule.restrictScalars_mem]

/-- Power series coefficient families with only finitely many nonzero residues
modulo each power of the smoothing parameter. -/
def restrictedThetaCoefficients : Submodule S ((ℤ × ℤ) → PowerSeries K) :=
  ((F).restrictedFamilies (ℤ × ℤ)).comap
    (LinearEquiv.piCongrRight fun _ => (principalModuleCompletionEquiv Unit K).symm).toLinearMap

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
  simp only [projection_principalModuleCompletionEquiv_symm, ne_eq,
    Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem, AlgFiltration.ofIdeal_ideal,
    Function.support, Ideal.Quotient.eq_zero_iff_mem]

/-- Completed theta monomial expansions have precisely the power series coefficients
with finite support at every cutoff. -/
def completedThetaCoefficientsEquiv : (thetaFiltration K).completion ≃ₗ[S]
    restrictedThetaCoefficients K :=
  ((b).completedCoefficientsEquiv F).trans
    ((LinearEquiv.piCongrRight fun _ => (principalModuleCompletionEquiv Unit K).symm).ofSubmodule'
      ((F).restrictedFamilies (ℤ × ℤ))).symm

/-- The completed theta coefficients are the power series images of the completed
basis coefficients. -/
@[simp]
theorem completedThetaCoefficientsEquiv_apply (x : (thetaFiltration K).completion)
    (i : ℤ × ℤ) :
    (completedThetaCoefficientsEquiv K x).val i =
      principalModuleCompletionEquiv Unit K (((b).completedCoefficientsEquiv F x).val i) := (rfl)

/-- A finite monomial expansion has its original polynomial coefficients,
viewed in the power series ring. -/
@[simp↓]
theorem completedThetaCoefficientsEquiv_of (x : A) (i : ℤ × ℤ) :
    (completedThetaCoefficientsEquiv K ((thetaFiltration K).of x)).val i =
      ((b).repr x i : PowerSeries K) := by
  rw [completedThetaCoefficientsEquiv_apply,
    Module.Basis.completedCoefficientsEquiv_of, principalModuleCompletionEquiv_of]

/-- Each theta monomial is the single-coordinate expansion at its own index. -/
@[simp↓ high]
theorem completedThetaCoefficientsEquiv_of_theta (n w : ℤ) (i : ℤ × ℤ) :
    (completedThetaCoefficientsEquiv K ((thetaFiltration K).of (theta t n w))).val i =
      if (n, w) = i then 1 else 0 := by
  classical
  rw [completedThetaCoefficientsEquiv_of, ← laurentBasis_apply_eq_theta, Module.Basis.repr_self,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- The power series images of the coefficients of a finite expansion are admissible. -/
theorem repr_mem_restrictedThetaCoefficients (x : A) :
    (fun i => ((b).repr x i : PowerSeries K)) ∈ restrictedThetaCoefficients K := by
  have h := (completedThetaCoefficientsEquiv K ((thetaFiltration K).of x)).property
  have hx : (completedThetaCoefficientsEquiv K ((thetaFiltration K).of x)).val =
      fun i => ((b).repr x i : PowerSeries K) :=
    funext (completedThetaCoefficientsEquiv_of K x)
  rwa [hx] at h

/-- The polynomial coefficients of a finite expansion reassemble its canonical image. -/
@[simp]
theorem completedThetaCoefficientsEquiv_symm_of (x : A) :
    (completedThetaCoefficientsEquiv K).symm
        ⟨fun i => ((b).repr x i : PowerSeries K), repr_mem_restrictedThetaCoefficients K x⟩ =
      (thetaFiltration K).of x := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext i
  rw [completedThetaCoefficientsEquiv_of]

/-- At order `k`, an admissible family of power series has the finite expansion
whose coefficients are the classes of the truncations at `k+1`. -/
@[simp]
theorem coefficientQuotientEquiv_projection_completedThetaCoefficientsEquiv_symm
    (f : restrictedThetaCoefficients K) (k : ℕ) (i : ℤ × ℤ) :
    (b).coefficientQuotientEquiv F k
        ((thetaFiltration K).projection k ((completedThetaCoefficientsEquiv K).symm f)) i =
      Submodule.Quotient.mk ((f.val i).truncTotal (k + 1)) := by
  set y := (b).completedCoefficientsEquiv F ((completedThetaCoefficientsEquiv K).symm f)
  have hy :
      (completedThetaCoefficientsEquiv K).symm f = ((b).completedCoefficientsEquiv F).symm y :=
    (LinearEquiv.symm_apply_apply _ _).symm
  have hi : y.val i = (principalModuleCompletionEquiv Unit K).symm (f.val i) := by
    rw [LinearEquiv.eq_symm_apply, ← completedThetaCoefficientsEquiv_apply,
      LinearEquiv.apply_symm_apply]
  rw [hy, Module.Basis.coefficientQuotientEquiv_projection_completedCoefficientsEquiv_symm, hi,
    projection_principalModuleCompletionEquiv_symm]

end Mei.FocusFocus
