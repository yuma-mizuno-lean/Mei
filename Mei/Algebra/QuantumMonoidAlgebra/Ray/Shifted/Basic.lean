/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Action
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Completion
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Monomial
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.TwistedAction

/-!
# Quantum ray actions on arbitrary shifted coefficients

In coordinates `z^p b`, conjugation by a positive ray series has left factor
`(z^p)⁻¹ H(z^n) z^p = H(q^(β(n,p) - β(p,n)) z^n)` and right factor `H(z^n)⁻¹`.
Here `(z^p)⁻¹ = q^(β(p,p)) z^(-p)`. For an alternating form the diagonal
factor is one and the skew exponent becomes `2 β(n,p)`.
The corresponding linear action is defined on the entire shifted completion,
without any positivity assumption on `p`, and preserves every relative order.
The shift does not contribute to relative degree.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

variable (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)

/-- Unit ray series act linearly on every translated coefficient completion. -/
def shiftedRayAction (n : d.monoid) (hn : 0 < d.degree n) (p : Γ) :
    (PowerSeries R)ˣ →*
      (d.ShiftedCoefficients (grade q β) p ≃ₗ[R] d.ShiftedCoefficients (grade q β) p) where
  toFun H :=
    ((positiveCompletionShiftEquiv q β d p).symm.trans
      ((F).completedTwistedSeriesAction
        (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
        ((q ^ (β n p - β p n) : Rˣ) : R) H)).trans
      (positiveCompletionShiftEquiv q β d p)
  map_one' := by ext x; simp
  map_mul' H K := by ext x; simp

/-- The skew part of the bilinear form determines translated ray conjugation. -/
theorem shiftedRayAction_coordinates_skew (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p a) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (PowerSeries.rescale ((q ^ (β n p - β p n) : Rˣ) : R) (H : PowerSeries R)) * a *
          (F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (↑(H⁻¹) : PowerSeries R)) := by
  simp only [shiftedRayAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, AlgFiltration.completedTwistedSeriesAction_apply]

/-- Shifted ray conjugation has the twisted left factor in positive coordinates. -/
theorem shiftedRayAction_coordinates (hβ : β.IsAlt) (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p a) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (H : PowerSeries R)) * a *
          (F).completedAeval
            (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
            (↑(H⁻¹) : PowerSeries R)) := by
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, two_mul] using
    shiftedRayAction_coordinates_skew q β d n hn p H a

/-- At shift zero, the shifted action recovers the positive algebra ray automorphism. -/
theorem shiftedRayAction_zero (n : d.monoid)
    (hn : 0 < d.degree n) (H : (PowerSeries R)ˣ) (a : (F).completion) :
    shiftedRayAction q β d n hn 0 H (positiveCompletionShiftEquiv q β d 0 a) =
      positiveCompletionShiftEquiv q β d 0
        (completedRayAction q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn H a) := by
  have h₀ : PowerSeries.rescale ((q ^ (β n (0 : Γ) - β 0 n) : Rˣ) : R)
      (H : PowerSeries R) = H := by simp
  simpa only [h₀, completedRayAction, AlgFiltration.completedSeriesAction_apply] using
    shiftedRayAction_coordinates_skew q β d n hn 0 H a

/-- The relative-zero monomial transforms by the evaluated ray ratio, for arbitrary
bilinear forms and even negative ambient shifts. -/
theorem shiftedRayAction_base_monomial (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) :
    shiftedRayAction q β d n hn p H
        ((d.shiftedFiltration (grade q β) p).of
          (shiftedMonomial q β d.monoid p 0)) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedAeval
          (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
          (PowerSeries.rescale ((q ^ (β n p - β p n) : Rˣ) : R) (H : PowerSeries R) *
            (↑(H⁻¹) : PowerSeries R))) := by
  have h := congrArg (shiftedRayAction q β d n hn p H)
    (positiveCompletionShiftEquiv_one q β d p)
  refine h.symm.trans ?_
  have hm := map_mul ((F).completedAeval
    (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn))
    (PowerSeries.rescale ((q ^ (β n p - β p n) : Rˣ) : R) (H : PowerSeries R))
    (↑(H⁻¹) : PowerSeries R)
  simpa only [mul_one, hm] using shiftedRayAction_coordinates_skew q β d n hn p H 1

/-- Under `β.IsAlt`, the base-monomial ratio has exponent `2β(n,p)`. -/
theorem shiftedRayAction_base (hβ : β.IsAlt) (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p 1) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedAeval
          (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
          (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (H : PowerSeries R) *
            (↑(H⁻¹) : PowerSeries R))) := by
  have h := congrArg (shiftedRayAction q β d n hn p H)
    (positiveCompletionShiftEquiv_one q β d p)
  refine h.trans ?_
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul] using
    shiftedRayAction_base_monomial q β d n hn p H

/-- Reversing a wall crossing gives the inverse shifted ray action. -/
@[simp]
theorem shiftedRayAction_inv (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) :
    shiftedRayAction q β d n hn p (H⁻¹) =
      (shiftedRayAction q β d n hn p H).symm :=
  map_inv (shiftedRayAction q β d n hn p) H

/-- Every relative filtration term is preserved and reflected by the shifted ray action. -/
@[simp]
theorem shiftedRayAction_mem_iff (n : d.monoid)
    (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ) (k : ℕ)
    (a : d.ShiftedCoefficients (grade q β) p) :
    shiftedRayAction q β d n hn p H a ∈
        (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k ↔
      a ∈ (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k := by
  let e := positiveCompletionShiftEquiv q β d p
  let x := completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn
  let c : R := ((q ^ (β n p - β p n) : Rˣ) : R)
  have h₁ := positiveCompletionShiftEquiv_mem_iff q β d p k
    ((F).completedTwistedSeriesAction x c H (e.symm a))
  have h₂ := (F).completedTwistedSeriesAction_mem_iff x c H k (e.symm a)
  have h₃ := positiveCompletionShiftEquiv_mem_iff q β d p k (e.symm a)
  have h₃' : e.symm a ∈ (F).completionIdeal k ↔
      a ∈ (d.shiftedFiltration (grade q β) p).completedFiltration.submodule k := by
    simpa only [e, LinearEquiv.apply_symm_apply] using h₃.symm
  exact h₁.trans (h₂.trans h₃')

end Mei.QuantumMonoidAlgebra
