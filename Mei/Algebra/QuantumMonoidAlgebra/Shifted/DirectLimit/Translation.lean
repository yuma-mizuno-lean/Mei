/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Monomial
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Monomial
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Inclusion

/-!
# Global monomial multiplication and completed translations

Left multiplication by a global quantum monomial equals completed translation
on every coefficient chart. This includes infinite coefficient families and
arbitrary negative origins. The bilinear form need not be alternating.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

omit [DecidableEq Γ] in
/-- Multiplication by the completed origin monomial is completed translation. -/
theorem shiftedCompletionMul_originMonomial (p s : Γ)
    (x : d.ShiftedCoefficients (grade q β) s) :
    d.shiftedCompletionMul (grade q β) p s
        ((d.shiftedFiltration (grade q β) p).of (shiftedMonomial q β d.monoid p 0)) x =
      shiftedCompletedMonomialEquiv q β p s d x := by
  classical
  apply (d.shiftedFiltration (grade q β) (p + s)).completion_ext
  intro k
  let y : shiftedSubmodule (grade q β) d.monoid s :=
    Quotient.out ((d.shiftedFiltration (grade q β) s).projection k x)
  have hy : Submodule.Quotient.mk y =
      (d.shiftedFiltration (grade q β) s).projection k x := Quotient.out_eq _
  have h0 := ((d.shiftedFiltration (grade q β) p).projection_of k
    (shiftedMonomial q β d.monoid p 0)).symm
  have hleft := d.projection_shiftedCompletionMul (grade q β) p s k
    ((d.shiftedFiltration (grade q β) p).of (shiftedMonomial q β d.monoid p 0)) x
    (shiftedMonomial q β d.monoid p 0) y h0 hy
  have hright := projection_shiftedCompletedMonomialEquiv q β p s d k x
  simp only [← hy, Submodule.mapQ_apply, LinearEquiv.coe_coe] at hright
  have hfinite : shiftedMul (grade q β) d.monoid p s
      (shiftedMonomial q β d.monoid p 0) y = shiftedMonomialEquiv q β d.monoid p s y := by
    apply Subtype.ext
    simp only [coe_shiftedMul, coe_shiftedMonomial, AddSubmonoid.coe_zero, add_zero,
      coe_shiftedMonomialEquiv]
  exact hleft.trans ((congrArg Submodule.Quotient.mk hfinite).trans hright.symm)

variable (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)

/-- A global monomial is the origin monomial in any containing chart. -/
theorem directLimitMonomial_eq_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid) :
    directLimitMonomial q β d hspan p =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        ((d.shiftedFiltration (grade q β) p).of (shiftedMonomial q β d.monoid p 0)) := by
  simpa only [directLimitMonomial_eq, coe_shiftedMonomial, AddSubmonoid.coe_zero, add_zero] using
    d.toShiftedDirectLimitAlgHom_of_supported (grade q β) hspan p s hp
      (shiftedMonomial q β d.monoid p 0)

/-- Multiplication by a global monomial translates every completed chart. -/
theorem directLimitMonomial_mul_toShiftedDirectLimitOfChart (p s : Γ)
    (t u : Multiset d.monoid) (hs : s - d.coefficientOrigin t ∈ d.monoid)
    (hps : p + s - d.coefficientOrigin u ∈ d.monoid)
    (x : d.ShiftedCoefficients (grade q β) s) :
    directLimitMonomial q β d hspan p *
        d.toShiftedDirectLimitOfChart (grade q β) s t hs x =
      d.toShiftedDirectLimitOfChart (grade q β) (p + s) u hps
        (shiftedCompletedMonomialEquiv q β p s d x) := by
  let v := Classical.choose (d.exists_coefficientOrigin_of_spanning hspan p)
  have hv := Classical.choose_spec (d.exists_coefficientOrigin_of_spanning hspan p)
  have hsum : p + s - d.coefficientOrigin (v + t) ∈ d.monoid := by
    rw [d.coefficientOrigin_add]
    have he : p + s - (d.coefficientOrigin v + d.coefficientOrigin t) =
        (p - d.coefficientOrigin v) + (s - d.coefficientOrigin t) := by abel
    rw [he]
    exact d.monoid.add_mem hv hs
  let z := (d.shiftedFiltration (grade q β) p).of (shiftedMonomial q β d.monoid p 0)
  let E := d.toShiftedDirectLimitOfChart (grade q β) (p + s) (v + t) hsum
  let y := d.toShiftedDirectLimitOfChart (grade q β) s t hs x
  have h1 := congrArg (fun a : d.ShiftedDirectLimit (grade q β) => a * y)
    (directLimitMonomial_eq_toShiftedDirectLimitOfChart q β d hspan p v hv)
  have h2 := d.shiftedDirectLimitMul_eq_mul (grade q β)
    (d.toShiftedDirectLimitOfChart (grade q β) p v hv z) y
  have h3 := d.shiftedDirectLimitMul_toShiftedDirectLimitOfChart (grade q β) p s v t hv hs z x
  have h4 := congrArg E (shiftedCompletionMul_originMonomial q β d p s x)
  have h5 : E (shiftedCompletedMonomialEquiv q β p s d x) =
      d.toShiftedDirectLimitOfChart (grade q β) (p + s) u hps
        (shiftedCompletedMonomialEquiv q β p s d x) := by
    simpa only [PositiveDegrees.shiftedCompletedInclusion_refl] using
      d.toShiftedDirectLimitOfChart_inclusion (grade q β) (p + s) (p + s) (by simp)
        u (v + t) hps hsum (shiftedCompletedMonomialEquiv q β p s d x)
  exact h1.trans (h2.symm.trans (h3.trans (h4.trans h5)))

end Mei.QuantumMonoidAlgebra
