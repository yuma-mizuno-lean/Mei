/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Truncation
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.Algebra.Lie.BCH.Conjugation

/-!
# Conjugating charge-one coefficients in finite module probes

The exponential of the charge-one summand is an injective copy of the additive
finite coefficient module. Conjugation by a charge-zero label acts on this copy
by the existing finite BCH coefficient action. The probe retains one more order
than the coefficient module, since module charge contributes one to the degree.

These identities turn transport of probe labels into linear transport of
coefficients. The construction follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
It uses `ModuleProbe.moduleQuotientInclusion`, `BCHGroup.exp_expAd` and Mathlib's
`Module.End.commute_exp_left_of_commute`; no new exponential is constructed.
-/

public section
noncomputable section

namespace Mei.ModuleProbe

variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]

variable [Algebra ℚ R]

/-- Exponentiation embeds the additive finite coefficient module in the probe group. -/
def moduleBCHInclusion (k : ℕ) : Multiplicative ((d.shiftedFiltration ℳ p).quotient k) →*
    BCHGroup ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1)) where
  toFun a := BCHGroup.exp (moduleQuotientInclusion d ℳ p ℒ k a.toAdd)
  map_one' := by simp
  map_mul' a b := by
    simpa using BCHGroup.exp_add_of_lie_eq_zero
      (moduleQuotientInclusion d ℳ p ℒ k a.toAdd)
      (moduleQuotientInclusion d ℳ p ℒ k b.toAdd)
      (lie_moduleQuotientInclusion d ℳ p ℒ k a.toAdd b.toAdd)

/-- A finite coefficient label is the exponential of its charge-one inclusion. -/
@[simp]
theorem moduleBCHInclusion_apply (k : ℕ)
    (a : Multiplicative ((d.shiftedFiltration ℳ p).quotient k)) :
    moduleBCHInclusion d ℳ p ℒ k a =
      BCHGroup.exp (moduleQuotientInclusion d ℳ p ℒ k a.toAdd) := (rfl)

/-- Distinct retained coefficients give distinct probe labels. -/
theorem moduleBCHInclusion_injective (k : ℕ) :
    Function.Injective (moduleBCHInclusion d ℳ p ℒ k) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply moduleQuotientInclusion_injective d ℳ p ℒ k
  simpa using congrArg BCHGroup.log hab

/-- Rational scalars on the finite coefficients are induced from the coefficient ring. -/
local instance quotientRatModule (k : ℕ) :
    Module ℚ ((d.shiftedLieFiltration ℒ ℳ p).quotient k) :=
  Module.compHom _ (algebraMap ℚ R)

/-- Charge-zero adjoint exponentials act on charge-one coefficients by the finite
coefficient exponential, with the one-order shift forced by module charge. -/
theorem expAd_moduleQuotientInclusion (k : ℕ) (x : d.truncatedLie ℒ (k + 1))
    (a : (d.shiftedFiltration ℳ p).quotient k)
    (hx : IsNilpotent (LieAlgebra.ad R
      ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1))
      ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k + 1) (k + 1) (by simp) x))) :
    TauCeti.expAd ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k + 1) (k + 1) (by simp) x) hx
        (moduleQuotientInclusion d ℳ p ℒ k a) =
      moduleQuotientInclusion d ℳ p ℒ k
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedExpLieAction d ℒ k
          (d.truncationMap ℒ (Nat.le_succ k) x) a) := by
  have hc : (LieAlgebra.ad R _
      ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k + 1) (k + 1) (by simp) x)).comp
      (moduleQuotientInclusion d ℳ p ℒ k) =
      (moduleQuotientInclusion d ℳ p ℒ k).comp
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedLieAction d ℒ k
          (d.truncationMap ℒ (Nat.le_succ k) x)) := by
    obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ (k + 1)).surjective_mkQ x
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LieIdeal.mkQ_apply,
      GradedLieHom.truncatedMap_mk, baseGradedLieHom_apply,
      LieAlgebra.ad_apply, PositiveDegrees.truncationMap_mk,
      ModuleFiltration.truncatedLieAction_mk]
    simpa only [LieIdeal.mkQ_apply] using lie_base_moduleQuotientInclusion d ℳ p ℒ k x b
  simpa only [TauCeti.expAd_apply, ModuleFiltration.truncatedExpLieAction_apply,
    LinearMap.comp_apply] using LinearMap.congr_fun
      (Module.End.commute_exp_left_of_commute
        ⟨k + 1, (d.shiftedLieFiltration ℒ ℳ p).truncatedLieAction_pow_eq_zero d ℒ k _⟩
        hx hc) a

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Conjugating a coefficient label by any finite charge-zero BCH label gives
the label of its finite BCH coefficient action. -/
theorem base_conj_moduleBCHInclusion (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ (k + 1)))
    (a : Multiplicative ((d.shiftedFiltration ℳ p).quotient k)) :
    ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k + 1) (k + 1) (by simp)).bchGroupMap g *
        moduleBCHInclusion d ℳ p ℒ k a *
        (((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k + 1) (k + 1) (by simp)).bchGroupMap g)⁻¹ =
      moduleBCHInclusion d ℳ p ℒ k (Multiplicative.ofAdd
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
          ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap g) a.toAdd)) := by
  let x := (baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k + 1) (k + 1) (by simp) (BCHGroup.log g)
  have hx : IsNilpotent (LieAlgebra.ad R _ x) :=
    LieModule.isNilpotent_toEnd_of_isNilpotent R _ _ x
  have he := BCHGroup.exp_expAd x (moduleQuotientInclusion d ℳ p ℒ k a.toAdd) hx
  rw [expAd_moduleQuotientInclusion d ℳ p ℒ k (BCHGroup.log g) a.toAdd hx] at he
  simpa only [ModuleFiltration.truncatedBCHAction_apply, LieHom.log_bchGroupMap,
    moduleBCHInclusion_apply, toAdd_ofAdd,
    x, ← LieHom.bchGroupMap_exp, BCHGroup.exp_log] using he.symm

end Mei.ModuleProbe
