/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.AdicCompletion.Filtered
public import Mei.RingTheory.FilteredAlgebra.Map
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Polynomial completion as multivariate power series

The completion of a multivariate polynomial ring along the ideal of variables
is its power series ring. At filtered order `k`, the inverse equivalence takes
total-degree truncation at `k+1`, then the quotient class. Coefficient changes
commute with this equivalence, so it applies in particular to coefficient rings
that are lattice monoid algebras.

This uses Mathlib's `MvPowerSeries.toAdicCompletionAlgEquiv`, rather than
reconstructing its power series or truncation arguments, and the comparison
between adic and filtered completions.
-/

public section

noncomputable section

namespace Mei

open AlgFiltration

variable (σ R : Type*) [Finite σ] [CommRing R]

/-- The ideal-of-variables completion of a polynomial ring is its power series
ring, compatibly with the polynomial algebra structure. -/
def principalCompletionEquiv :
    (ofIdeal (MvPolynomial.idealOfVars σ R)).completion ≃ₐ[MvPolynomial σ R]
      MvPowerSeries σ R :=
  (adicCompletionEquiv (MvPolynomial.idealOfVars σ R)).symm.trans
    (MvPowerSeries.toAdicCompletionAlgEquiv σ R).symm

/-- At order `k`, the inverse equivalence is total-degree truncation at `k+1`
followed by the quotient map. -/
@[simp]
theorem projection_principalCompletionEquiv_symm (k : ℕ) (p : MvPowerSeries σ R) :
    (ofIdeal (MvPolynomial.idealOfVars σ R)).projection k
      ((principalCompletionEquiv σ R).symm p) =
      Ideal.Quotient.mk ((ofIdeal (MvPolynomial.idealOfVars σ R)).ideal (k + 1))
        (p.truncTotal (k + 1)) := by
  simp only [principalCompletionEquiv, AlgEquiv.symm_trans_apply,
    AlgEquiv.symm_symm, projection_adicCompletionEquiv,
    MvPowerSeries.toAdicCompletionAlgEquiv_apply]
  rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ (le_of_eq (Ideal.mul_top _))]
  simp only [AdicCompletion.eval_apply,
    MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal]
  simp

/-- Completing a polynomial and then passing to power series is the usual inclusion. -/
@[simp]
theorem principalCompletionEquiv_toCompletion (p : MvPolynomial σ R) :
    principalCompletionEquiv σ R
      ((ofIdeal (MvPolynomial.idealOfVars σ R)).toCompletion p) = p := by
  apply (MvPowerSeries.toAdicCompletionAlgEquiv σ R).injective
  simp only [principalCompletionEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    MvPowerSeries.toAdicCompletionAlgEquiv_apply, MvPowerSeries.toAdicCompletion_coe]
  exact (adicCompletionEquiv (MvPolynomial.idealOfVars σ R)).injective (by simp)

/-- Truncating the power series associated to a completed polynomial recovers
its finite-order projection. -/
@[simp]
theorem mk_truncTotal_principalCompletionEquiv (k : ℕ)
    (x : (ofIdeal (MvPolynomial.idealOfVars σ R)).completion) :
    Ideal.Quotient.mk ((ofIdeal (MvPolynomial.idealOfVars σ R)).ideal (k + 1))
      ((principalCompletionEquiv σ R x).truncTotal (k + 1)) =
        (ofIdeal (MvPolynomial.idealOfVars σ R)).projection k x := by
  rw [← projection_principalCompletionEquiv_symm, AlgEquiv.symm_apply_apply]

end Mei

namespace RingHom

open Mei.AlgFiltration

variable {σ R S : Type*} [CommRing R] [CommRing S]

/-- Coefficient change on polynomial completions, with the same cutoff at every order. -/
def principalCompletionMap (φ : R →+* S) :
    (ofIdeal (MvPolynomial.idealOfVars σ R)).completion →+*
      (ofIdeal (MvPolynomial.idealOfVars σ S)).completion :=
  (ofIdeal (MvPolynomial.idealOfVars σ R)).mapCompletion
    (ofIdeal (MvPolynomial.idealOfVars σ S)) (MvPolynomial.map φ) _root_.id monotone_id (by
      intro k p hp
      simp only [ofIdeal_ideal, Ideal.mem_comap] at hp ⊢
      rw [MvPolynomial.mem_pow_idealOfVars_iff'] at hp ⊢
      intro d hd
      simp [MvPolynomial.coeff_map, hp d hd])

end RingHom

namespace Mei

open AlgFiltration

variable {σ R S : Type*} [Finite σ] [CommRing R] [CommRing S]

/-- Coefficient change commutes with the power series description of the completion. -/
@[simp]
theorem principalCompletionEquiv_map (φ : R →+* S)
    (x : (ofIdeal (MvPolynomial.idealOfVars σ R)).completion) :
    principalCompletionEquiv σ S (φ.principalCompletionMap x) =
      MvPowerSeries.map φ (principalCompletionEquiv σ R x) := by
  obtain ⟨p, rfl⟩ := (principalCompletionEquiv σ R).symm.surjective x
  apply (principalCompletionEquiv σ S).symm.injective
  simp only [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]
  apply (ofIdeal (MvPolynomial.idealOfVars σ S)).completion_ext
  intro k
  simp only [RingHom.principalCompletionMap, projection_mapCompletion, id_eq,
    projection_principalCompletionEquiv_symm, Ideal.quotientMap_mk]
  congr 1
  exact (MvPowerSeries.truncFinset_map φ p).symm

end Mei

namespace RingHom

open Mei.AlgFiltration

variable {σ R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The identity coefficient map acts identically on completed polynomials. -/
@[simp]
theorem principalCompletionMap_id :
    (RingHom.id R).principalCompletionMap (σ := σ) =
      RingHom.id (ofIdeal (MvPolynomial.idealOfVars σ R)).completion := by
  have hmap : MvPolynomial.map (RingHom.id R) = RingHom.id (MvPolynomial σ R) :=
    RingHom.ext MvPolynomial.map_id
  simpa only [principalCompletionMap, hmap] using
    (ofIdeal (MvPolynomial.idealOfVars σ R)).mapCompletion_id

/-- Coefficient changes on completed polynomials respect composition. -/
theorem principalCompletionMap_comp (φ : R →+* S) (ψ : S →+* T) :
    (ψ.comp φ).principalCompletionMap (σ := σ) =
      ψ.principalCompletionMap.comp φ.principalCompletionMap := by
  have hmap : MvPolynomial.map (σ := σ) (ψ.comp φ) =
      (MvPolynomial.map ψ).comp (MvPolynomial.map φ) :=
    RingHom.ext fun p => (MvPolynomial.map_map φ ψ p).symm
  simp only [principalCompletionMap, ← mapCompletion_comp, hmap, Function.id_comp]

end RingHom
