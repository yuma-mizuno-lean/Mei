/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Specialization
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit.Inner
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit.Map
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Commute

/-!
# Global quantum coefficients at the classical parameter

At `q = 1`, global shifted quantum coefficients commute, and every evaluated
ray-series unit acts trivially by conjugation. The statements include infinite
series and negative support origins. The form is retained and may be nonalternating;
no spanning condition on the positive monoid or rational scalar algebra is needed.

This extends the finite and positive specialization checks in
`Mei.Algebra.QuantumMonoidAlgebra.Specialization` to the existing global coefficient
carrier. Only the unnormalized action is considered, not a divided classical limit.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "G" => d.ShiftedDirectLimit (grade (1 : Rˣ) β)

/-- Global coefficients at `q = 1` commute, including infinite shifted families. -/
theorem commute_shiftedDirectLimit_atOne (x y : G) : Commute x y :=
  d.commute_shiftedDirectLimit (grade (1 : Rˣ) β) (commute_atOne β) x y

/-- At `q = 1` every global ray action fixes every global coefficient. -/
@[simp]
theorem directLimitRayAction_atOne (n : d.monoid) (hn : 0 < d.degree n)
    (H : (PowerSeries R)ˣ) (x : G) :
    directLimitRayAction (1 : Rˣ) β d n hn H x = x := by
  let u := directLimitRayUnit (1 : Rˣ) β d n hn H
  have hcancel := Units.commute_iff_mul_inv_cancel.mp
    (commute_shiftedDirectLimit_atOne β d (u : G) x)
  exact (directLimitRayAction_eq_conjugation (1 : Rˣ) β d n hn H x).trans hcancel

section Map

variable {S Γ' : Type*} [CommRing S] [AddCommGroup Γ'] [DecidableEq Γ']
  {q : Rˣ} {β' : LinearMap.BilinForm ℤ Γ'}
  (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e) (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = (1 : Sˣ) ^ β' (T p) (T r))

/-- Any coefficient transport to `q = 1` identifies a global coefficient with its
ray transform. This also allows noninjective coefficient and exponent maps. -/
@[simp]
theorem mapShiftedDirectLimit_directLimitRayAction_atOne
    (n : d.monoid) (hn : 0 < d.degree n) (H : (PowerSeries R)ˣ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit d e T φ h (directLimitRayAction q β d n hn H x) =
      mapShiftedDirectLimit d e T φ h x :=
  (mapShiftedDirectLimit_directLimitRayAction d e T φ h n hn H x).trans
    (directLimitRayAction_atOne β' e _ _ _ _)

end Map

end Mei.QuantumMonoidAlgebra
