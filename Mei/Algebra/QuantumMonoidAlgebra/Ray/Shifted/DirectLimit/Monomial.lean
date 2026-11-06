/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.NormalForm

/-!
# Global quantum ray actions on Laurent monomials

A ray action on an arbitrary ambient monomial is multiplication on the right by
an evaluated ratio of unit series. The exponent in that ratio is the skew part
of the bilinear form, including when the ambient monomial has negative degree.
The explicit spanning hypothesis is the one used to embed every ambient monomial
in the global coefficient algebra. No alternation or characteristic assumption
is needed for this ratio formula.
-/

public noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)
  (n : d.monoid) (hn : 0 < d.degree n)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "x" => completedRayGenerator q β d.monoid d.degree
  (fun _ h => d.degree_nonneg h) n hn

private local instance : Ring (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Algebra R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Module R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : DirectSum.Decomposition (grade q β) := inferInstance
private local instance : Ring (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Algebra R (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Ring (F).completion := inferInstance
private local instance : Algebra R (F).completion := inferInstance
private local instance : Module R (F).completion := inferInstance
private local instance (p : Γ) : AddCommGroup (d.ShiftedCoefficients (grade q β) p) :=
  inferInstance
private local instance (p : Γ) : Module R (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance : AddCommMonoid (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : AddCommGroup (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Ring (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Algebra R (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Module R (d.ShiftedDirectLimit (grade q β)) := inferInstance

/-- Conjugation on an ambient monomial is its skew-rescaled ray ratio, evaluated
in the positive completion and then multiplied inside the global algebra. -/
theorem directLimitRayAction_monomial (p : Γ) (H : (PowerSeries R)ˣ) :
    directLimitRayAction q β d n hn H (directLimitMonomial q β d hspan p) =
      directLimitMonomial q β d hspan p * positiveCompletionToDirectLimit q β d
        ((F).completedAeval x
          (PowerSeries.rescale ((q ^ (β n p - β p n) : Rˣ) : R) (H : PowerSeries R) *
            (↑(H⁻¹) : PowerSeries R))) := by
  refine (d.exists_coefficientOrigin_of_spanning hspan p).elim
    fun (s : Multiset d.monoid) hs => ?_
  let E := d.toShiftedDirectLimitOfChart (grade q β) p s hs
  let a := (d.shiftedFiltration (grade q β) p).of (shiftedMonomial q β d.monoid p 0)
  have hm := directLimitMonomial_eq_toShiftedDirectLimitOfChart q β d hspan p s hs
  have ha := directLimitRayAction_toShiftedDirectLimitOfChart q β d n hn H p s hs a
  have hb := congrArg E (shiftedRayAction_base_monomial q β d n hn p H)
  have hp := directLimitMonomial_mul_positiveCompletionToDirectLimit q β d hspan p s hs
    ((F).completedAeval x
      (PowerSeries.rescale ((q ^ (β n p - β p n) : Rˣ) : R) (H : PowerSeries R) *
        (↑(H⁻¹) : PowerSeries R)))
  exact (congrArg (directLimitRayAction q β d n hn H) hm).trans
    (ha.trans (hb.trans hp.symm))

end Mei.QuantumMonoidAlgebra
