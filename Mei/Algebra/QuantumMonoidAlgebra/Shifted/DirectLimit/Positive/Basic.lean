/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Completion
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Embedding
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Inclusion
public import Mei.Logic.Function.Cast

/-!
# The positive completion inside global quantum coefficients

The zero chart embeds the completed positive coefficient algebra in global
coefficients as an algebra. This construction needs neither a spanning condition
on the positive monoid nor alternation of the bilinear form.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => d.ShiftedDirectLimit (grade q β)

private local instance : Ring (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Algebra R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Module R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : DirectSum.Decomposition (grade q β) := inferInstance
private local instance : Ring (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Algebra R (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Ring (F).completion := inferInstance
private local instance : Semiring (F).completion := (inferInstance : Ring (F).completion).toSemiring
private local instance : Monoid (F).completion := (inferInstance : Ring (F).completion).toMonoid
private local instance : One (F).completion := ⟨(inferInstance : Ring (F).completion).one⟩
private local instance : Mul (F).completion := ⟨(inferInstance : Ring (F).completion).mul⟩
private local instance : Algebra R (F).completion := inferInstance
private local instance : Module R (F).completion := inferInstance
private local instance (p : Γ) : AddCommGroup (d.ShiftedCoefficients (grade q β) p) :=
  inferInstance
private local instance (p : Γ) : Module R (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance : AddCommMonoid G := inferInstance
private local instance : AddCommGroup G := inferInstance
private local instance : Ring G := inferInstance
private local instance : Semiring G := (inferInstance : Ring G).toSemiring
private local instance : Monoid G := (inferInstance : Ring G).toMonoid
private local instance : One G := ⟨(inferInstance : Ring G).one⟩
private local instance : Mul G := ⟨(inferInstance : Ring G).mul⟩
private local instance : Algebra R G := inferInstance
private local instance : Module R G := inferInstance

private def positiveGlobalLinearMap : (F).completion →ₗ[R] G :=
  (d.toShiftedDirectLimitOfChart (grade q β) 0 0 (d.zero_coefficientOrigin_mem)).comp
    (positiveCompletionShiftEquiv q β d 0).toLinearMap

private theorem positiveGlobalLinearMap_component (a : (F).completion) (u : Γ) :
    d.shiftedDirectLimitComponents (grade q β) (positiveGlobalLinearMap q β d a) u =
      d.shiftedHomogeneousComponent (grade q β) 0 u
        (positiveCompletionShiftEquiv q β d 0 a) := by
  simp only [positiveGlobalLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    PositiveDegrees.shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]

private theorem component_positiveCompletionShiftEquiv_of_projection
    (a : (F).completion) (u : Γ) (k : ℕ) (hk : d.degree u ≤ k)
    (b : positiveSubalgebra q β d.monoid)
    (hb : (F).projection k a = Ideal.Quotient.mk ((F).ideal (k + 1)) b) :
    d.shiftedHomogeneousComponent (grade q β) 0 u
        (positiveCompletionShiftEquiv q β d 0 a) =
      DirectSum.decompose (grade q β) (b : QuantumMonoidAlgebra q β) u := by
  rw [d.shiftedHomogeneousComponent_eq (grade q β) 0 u k (by simpa using hk),
    projection_positiveCompletionShiftEquiv_of_projection q β d 0 k a b hb,
    PositiveDegrees.shiftedQuotientComponent_mk]
  simp only [coe_positiveShiftEquiv, monomial_zero, one_mul]

private theorem positiveGlobalLinearMap_one : positiveGlobalLinearMap q β d 1 = 1 := by
  apply d.shiftedDirectLimitComponents_injective (grade q β)
  funext u
  have hc := positiveGlobalLinearMap_component q β d 1 u
  have ho := d.shiftedDirectLimitComponents_one (grade q β) u
  have hf := positiveCompletionShiftEquiv_toCompletion q β d 0
    (1 : positiveSubalgebra q β d.monoid)
  have ht := (F).toCompletion.map_one
  have hf1 := (congrArg (positiveCompletionShiftEquiv q β d 0) ht).symm.trans hf
  have hh := d.shiftedHomogeneousComponent_of (grade q β) 0 u
    (positiveShiftEquiv q β d 0 (1 : positiveSubalgebra q β d.monoid))
  have he : (positiveShiftEquiv q β d 0 (1 : positiveSubalgebra q β d.monoid) :
      QuantumMonoidAlgebra q β) = 1 := by
    simp only [coe_positiveShiftEquiv, monomial_zero, one_mul, Subalgebra.coe_one]
  have hc' := congrArg (d.shiftedHomogeneousComponent (grade q β) 0 u) hf1
  have hd := congrArg (fun z : QuantumMonoidAlgebra q β => DirectSum.decompose (grade q β) z u) he
  exact (hc).trans <|
    (hc').trans <|
    (hh).trans <|
    (hd).trans <|
    ho.symm

private theorem positiveGlobalLinearMap_mul (a b : (F).completion) :
    positiveGlobalLinearMap q β d (a * b) =
      positiveGlobalLinearMap q β d a * positiveGlobalLinearMap q β d b := by
  apply d.shiftedDirectLimitComponents_injective (grade q β)
  funext u
  let k := (d.degree u).toNat
  have hk : d.degree u ≤ k := Int.self_le_toNat _
  refine (Ideal.Quotient.mk_surjective ((F).projection k a)).elim fun v hv => ?_
  refine (Ideal.Quotient.mk_surjective ((F).projection k b)).elim fun w hw => ?_
  have hvw : (F).projection k (a * b) =
      Ideal.Quotient.mk ((F).ideal (k + 1)) (v * w) := by
    exact ((F).projection k).map_mul a b |>.trans
      ((congrArg₂ (fun v w => v * w) hv.symm hw.symm).trans
        (map_mul (Ideal.Quotient.mk ((F).ideal (k + 1))) v w).symm)
  have hl := (positiveGlobalLinearMap_component q β d (a * b) u).trans
    (component_positiveCompletionShiftEquiv_of_projection q β d (a * b) u k hk (v * w) hvw)
  let x := positiveCompletionShiftEquiv q β d 0 a
  let y := positiveCompletionShiftEquiv q β d 0 b
  let C := fun z : G => d.shiftedDirectLimitComponents (grade q β) z u
  have hp := d.shiftedDirectLimitMul_toShiftedDirectLimitOfChart (grade q β) 0 0 0 0
    (d.zero_coefficientOrigin_mem) (d.zero_coefficientOrigin_mem) x y
  have hn := d.shiftedDirectLimitMul_eq_mul (grade q β)
    (positiveGlobalLinearMap q β d a) (positiveGlobalLinearMap q β d b)
  have hp' := congrArg C (hn.symm.trans hp)
  have hc := d.shiftedDirectLimitComponents_toShiftedDirectLimitOfChart (grade q β)
    (0 + 0) (0 + 0) (by simpa only [add_zero] using d.zero_coefficientOrigin_mem)
    (d.shiftedCompletionMul (grade q β) 0 0 x y) u
  have hread := d.shiftedHomogeneousComponent_eq (grade q β) (0 + 0) u k
    (by simpa only [add_zero, sub_zero] using hk) (d.shiftedCompletionMul (grade q β) 0 0 x y)
  have hm := d.projection_shiftedCompletionMul (grade q β) 0 0 k x y
    (positiveShiftEquiv q β d 0 v) (positiveShiftEquiv q β d 0 w)
    (projection_positiveCompletionShiftEquiv_of_projection q β d 0 k a v hv.symm).symm
    (projection_positiveCompletionShiftEquiv_of_projection q β d 0 k b w hw.symm).symm
  have hm' := congrArg (d.shiftedQuotientComponent (grade q β) (0 + 0) u k
    (by simpa only [add_zero, sub_zero] using hk)) hm
  have hrep := d.shiftedQuotientComponent_mk (grade q β) (0 + 0) u k
    (by simpa only [add_zero, sub_zero] using hk)
    (shiftedMul (grade q β) d.monoid 0 0
      (positiveShiftEquiv q β d 0 v) (positiveShiftEquiv q β d 0 w))
  have he : (shiftedMul (grade q β) d.monoid 0 0
      (positiveShiftEquiv q β d 0 v) (positiveShiftEquiv q β d 0 w) :
      QuantumMonoidAlgebra q β) = (v * w : positiveSubalgebra q β d.monoid) := by
    simp only [coe_shiftedMul, coe_positiveShiftEquiv, monomial_zero, one_mul, Subalgebra.coe_mul]
  have he' := congrArg (fun z : QuantumMonoidAlgebra q β => DirectSum.decompose (grade q β) z u) he
  exact (hl).trans <|
    (he'.symm).trans <|
    (hrep.symm).trans <|
    (hm'.symm).trans <|
    (hread.symm).trans <|
    (hc.symm).trans <|
    hp'.symm

/-- The completed positive coefficient algebra embeds in the global algebra through shift zero. -/
def positiveCompletionToDirectLimit : (F).completion →ₐ[R] G :=
  AlgHom.ofLinearMap (positiveGlobalLinearMap q β d)
    (positiveGlobalLinearMap_one q β d) (positiveGlobalLinearMap_mul q β d)

/-- The positive completion embedding is the zero-shift chart map. -/
theorem positiveCompletionToDirectLimit_apply (a : (F).completion) :
    positiveCompletionToDirectLimit q β d a =
      d.toShiftedDirectLimitOfChart (grade q β) 0 0
        d.zero_coefficientOrigin_mem
        (positiveCompletionShiftEquiv q β d 0 a) := by
  -- AlgHom.ofLinearMap retains this linear map; comp_apply exposes its two maps.
  change positiveGlobalLinearMap q β d a = _
  simp only [positiveGlobalLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- Equal support degrees give the same global value of positive completed coordinates. -/
theorem toShiftedDirectLimitOfChart_positiveCompletionShiftEquiv_congr
    {p r : Γ} (hpr : p = r) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hr : r - d.coefficientOrigin s ∈ d.monoid) (a : (F).completion) :
    d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (positiveCompletionShiftEquiv q β d p a) =
      d.toShiftedDirectLimitOfChart (grade q β) r s hr
        (positiveCompletionShiftEquiv q β d r a) := by
  have hc := d.toShiftedDirectLimitOfChart_cast (grade q β)
    p r hpr s s hp hr (positiveCompletionShiftEquiv q β d p a)
  have he : cast (congrArg (d.ShiftedCoefficients (grade q β)) hpr)
      (positiveCompletionShiftEquiv q β d p a) =
      positiveCompletionShiftEquiv q β d r a := by
    simpa only [cast_eq] using
      Function.cast_apply (A := fun _ : Γ => (F).completion)
        (fun u => (positiveCompletionShiftEquiv q β d u :
          (F).completion → d.ShiftedCoefficients (grade q β) u)) hpr a
  exact hc.symm.trans
    (congrArg (d.toShiftedDirectLimitOfChart (grade q β) r s hr) he)

/-- No positive completed coefficient is lost in the global algebra. -/
theorem positiveCompletionToDirectLimit_injective :
    Function.Injective (positiveCompletionToDirectLimit q β d) :=
  (d.toShiftedDirectLimitOfChart_injective (grade q β) 0 0 (d.zero_coefficientOrigin_mem)).comp
    (positiveCompletionShiftEquiv q β d 0).injective

/-- Reading a component of the embedded positive completion gives its zero-chart component. -/
@[simp]
theorem shiftedDirectLimitComponents_positiveCompletionToDirectLimit
    (a : (F).completion) (u : Γ) :
    d.shiftedDirectLimitComponents (grade q β) (positiveCompletionToDirectLimit q β d a) u =
      d.shiftedHomogeneousComponent (grade q β) 0 u
        (positiveCompletionShiftEquiv q β d 0 a) :=
  positiveGlobalLinearMap_component q β d a u

/-- An ordinary positive coefficient has the same global image through either completion. -/
theorem positiveCompletionToDirectLimit_toCompletion
    (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)
    (a : positiveSubalgebra q β d.monoid) :
    positiveCompletionToDirectLimit q β d ((F).toCompletion a) =
      d.toShiftedDirectLimitAlgHom (grade q β) hspan (a : QuantumMonoidAlgebra q β) := by
  apply d.shiftedDirectLimitComponents_injective (grade q β)
  funext u
  have hl := shiftedDirectLimitComponents_positiveCompletionToDirectLimit q β d
    ((F).toCompletion a) u
  have hr := d.shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom (grade q β) hspan
    (a : QuantumMonoidAlgebra q β) u
  have hm := component_positiveCompletionShiftEquiv_of_projection q β d _ u
    (d.degree u).toNat (Int.self_le_toNat _) a ((F).projection_toCompletion _ _)
  exact hl.trans (hm.trans hr.symm)

end Mei.QuantumMonoidAlgebra
