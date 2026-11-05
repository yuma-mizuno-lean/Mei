/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map
public import Mei.LinearAlgebra.GradedModule.Shifted.Inclusion

/-!
# Inclusions in positive coordinates for shifted quantum coefficients

An inclusion of translated supports keeps ambient coefficients unchanged.
In positive coordinates it is multiplication by the difference monomial,
with the scalar correction from quantum multiplication. Compatible scalar and
exponent maps commute with these inclusions on finite quotients and completions,
for arbitrary bilinear forms and without injectivity assumptions.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

/-- Including a translated support multiplies positive coordinates by the difference monomial. -/
theorem shiftedSupportInclusion_positiveShiftEquiv (p s : Γ)
    (hps : p - s ∈ d.monoid)
    (a : positiveSubalgebra q β d.monoid) :
    shiftedSupportInclusion (grade q β) d.monoid p s hps
        (positiveShiftEquiv q β d p a) =
      positiveShiftEquiv q β d s
        (((((q ^ β s (p - s))⁻¹ : Rˣ) : R)) •
          (positiveMonomial q β d.monoid ⟨p - s, hps⟩ * a)) := by
  apply Subtype.ext
  simp only [coe_shiftedSupportInclusion, coe_positiveShiftEquiv,
    Subalgebra.coe_smul, Subalgebra.coe_mul, coe_positiveMonomial,
    mul_smul_comm, ← mul_assoc, monomial_mul, smul_mul_assoc, smul_smul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  congr 2
  abel

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)

/-- Completed support inclusion has the same quantum scalar correction as finite inclusion. -/
theorem shiftedCompletedInclusion_positiveCompletionShiftEquiv (p s : Γ)
    (hps : p - s ∈ d.monoid) (a : (F).completion) :
    d.shiftedCompletedInclusion (grade q β) p s hps
        (positiveCompletionShiftEquiv q β d p a) =
      positiveCompletionShiftEquiv q β d s
        (((((q ^ β s (p - s))⁻¹ : Rˣ) : R)) •
          ((F).toCompletion (positiveMonomial q β d.monoid ⟨p - s, hps⟩) * a)) := by
  apply (d.shiftedFiltration (grade q β) s).completion_ext
  intro k
  let b : positiveSubalgebra q β d.monoid := Quotient.out ((F).projection k a)
  have hb : Ideal.Quotient.mk ((F).ideal (k + 1)) b = (F).projection k a :=
    Ideal.Quotient.mk_out _
  have hb' : (F).projection k
        (((((q ^ β s (p - s))⁻¹ : Rˣ) : R)) •
          ((F).toCompletion (positiveMonomial q β d.monoid ⟨p - s, hps⟩) * a)) =
      Ideal.Quotient.mk ((F).ideal (k + 1))
        (((((q ^ β s (p - s))⁻¹ : Rˣ) : R)) •
          (positiveMonomial q β d.monoid ⟨p - s, hps⟩ * b)) :=
    AlgFiltration.projection_smul_mul_of_projection (F)
      (((q ^ β s (p - s))⁻¹ : Rˣ) : R)
      (positiveMonomial q β d.monoid ⟨p - s, hps⟩) b a k hb.symm
  exact (d.projection_shiftedCompletedInclusion (grade q β) p s hps k
    (positiveCompletionShiftEquiv q β d p a)).trans
      ((congrArg (d.shiftedQuotientMap (grade q β) p s hps k)
        (projection_positiveCompletionShiftEquiv_of_projection q β d p k a b hb.symm)).trans
        ((d.shiftedQuotientMap_mk (grade q β) p s hps k
          (positiveShiftEquiv q β d p b)).trans
          ((congrArg (fun z : shiftedSubmodule (grade q β) d.monoid s =>
            (Submodule.Quotient.mk z : (d.shiftedFiltration (grade q β) s).quotient k))
            (shiftedSupportInclusion_positiveShiftEquiv q β d p s hps b)).trans
              (projection_positiveCompletionShiftEquiv_of_projection q β d s k _ _ hb').symm)))

/-- A nonnegative shifted support includes naturally in the completed positive algebra. -/
def shiftedToPositiveCompletion (p : d.monoid) :
    d.ShiftedCoefficients (grade q β) p →ₗ[R] (F).completion :=
  (positiveCompletionShiftEquiv q β d 0).symm.toLinearMap.comp
    (d.shiftedCompletedInclusion (grade q β) p 0 (by simpa only [sub_zero] using p.property))

/-- The positive-completion inclusion first includes the support at origin zero. -/
theorem shiftedToPositiveCompletion_apply (p : d.monoid)
    (a : d.ShiftedCoefficients (grade q β) p) :
    shiftedToPositiveCompletion q β d p a =
      (positiveCompletionShiftEquiv q β d 0).symm
        (d.shiftedCompletedInclusion (grade q β) p 0
          (by simpa only [sub_zero] using p.property) a) := by
  -- The inclusion at shift zero is defined by these completed coordinates.
  rfl

/-- The natural inclusion into positive completion is injective. -/
theorem shiftedToPositiveCompletion_injective (p : d.monoid) :
    Function.Injective (shiftedToPositiveCompletion q β d p) := by
  classical
  intro x y h
  apply d.shiftedCompletedInclusion_injective (grade q β) p 0
    (by simpa only [sub_zero] using p.property)
  exact (positiveCompletionShiftEquiv q β d 0).symm.injective h

/-- In positive coordinates the natural inclusion is multiplication by the shift monomial. -/
theorem shiftedToPositiveCompletion_coordinates (p : d.monoid)
    (a : (F).completion) :
    shiftedToPositiveCompletion q β d p
        (positiveCompletionShiftEquiv q β d p a) =
      (F).toCompletion (positiveMonomial q β d.monoid p) * a := by
  have h := shiftedCompletedInclusion_positiveCompletionShiftEquiv q β d p 0
    (by simpa only [sub_zero] using p.property) a
  simp only [sub_zero, map_zero, LinearMap.zero_apply, zpow_zero, inv_one,
    Units.val_one, one_smul] at h
  exact (congrArg (positiveCompletionShiftEquiv q β d 0).symm h).trans
    ((positiveCompletionShiftEquiv q β d 0).symm_apply_apply _)

section Map

variable {S Γ' : Type*} [CommRing S] [AddCommGroup Γ']
  {q' : Sˣ} {β' : LinearMap.BilinForm ℤ Γ'}
  (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e) (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))
  (p s : Γ) (hps : p - s ∈ d.monoid)

local notation "ψ" => positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
  (fun _ hn => T.map_mem hn)

private theorem map_inclusion_coordinates (a : positiveSubalgebra q β d.monoid) :
    positiveShiftEquiv q' β' e (T s)
      (ψ ((positiveShiftEquiv q β d s).symm
        (shiftedSupportInclusion (grade q β) d.monoid p s hps
          (positiveShiftEquiv q β d p a)))) =
      shiftedSupportInclusion (grade q' β') e.monoid (T p) (T s)
        (by simpa only [map_sub] using T.map_mem hps)
        (positiveShiftEquiv q' β' e (T p) (ψ a)) := by
  apply Subtype.ext
  have hs := map_positiveShiftEquiv d e T φ h s
    ((positiveShiftEquiv q β d s).symm
      (shiftedSupportInclusion (grade q β) d.monoid p s hps
        (positiveShiftEquiv q β d p a)))
  simp only [LinearEquiv.apply_symm_apply, coe_shiftedSupportInclusion] at hs ⊢
  exact hs.symm.trans (map_positiveShiftEquiv d e T φ h p a)

private theorem mapShiftedQuotient_inclusion_mk_coordinates (k : ℕ)
    (a : positiveSubalgebra q β d.monoid) :
    mapShiftedQuotient d e T φ h s k
      (d.shiftedQuotientMap (grade q β) p s hps (T.modulus k)
        (Submodule.Quotient.mk (positiveShiftEquiv q β d p a))) =
      e.shiftedQuotientMap (grade q' β') (T p) (T s)
        (by simpa only [map_sub] using T.map_mem hps) k
        (mapShiftedQuotient d e T φ h p k
          (Submodule.Quotient.mk (positiveShiftEquiv q β d p a))) := by
  let b := shiftedSupportInclusion (grade q β) d.monoid p s hps
    (positiveShiftEquiv q β d p a)
  have hm := mapShiftedQuotient_mk_coordinates d e T φ h s k
    ((positiveShiftEquiv q β d s).symm b)
  simp only [LinearEquiv.apply_symm_apply] at hm
  have hc := congrArg (fun z : shiftedSubmodule (grade q' β') e.monoid (T s) =>
    (Submodule.Quotient.mk z : (e.shiftedFiltration (grade q' β') (T s)).quotient k))
    (map_inclusion_coordinates q β d e T φ h p s hps a)
  simp only [PositiveDegrees.shiftedQuotientMap_mk,
    mapShiftedQuotient_mk_coordinates]
  exact hm.trans hc

/-- Finite coefficient transport commutes with inclusion of translated supports,
using the prescribed source cutoff for both origins. -/
@[simp]
theorem mapShiftedQuotient_shiftedQuotientMap (k : ℕ)
    (a : (d.shiftedFiltration (grade q β) p).quotient (T.modulus k)) :
    mapShiftedQuotient d e T φ h s k
      (d.shiftedQuotientMap (grade q β) p s hps (T.modulus k) a) =
      e.shiftedQuotientMap (grade q' β') (T p) (T s)
        (by simpa only [map_sub] using T.map_mem hps) k
        (mapShiftedQuotient d e T φ h p k a) := by
  obtain ⟨b, rfl⟩ := ((d.shiftedFiltration (grade q β) p).submodule
    (T.modulus k + 1)).mkQ_surjective a
  obtain ⟨c, rfl⟩ := (positiveShiftEquiv q β d p).surjective b
  exact mapShiftedQuotient_inclusion_mk_coordinates q β d e T φ h p s hps k c

/-- Completed coefficient transport commutes with inclusion of translated supports. -/
@[simp]
theorem mapShiftedCompletion_shiftedCompletedInclusion
    (a : d.ShiftedCoefficients (grade q β) p) :
    mapShiftedCompletion d e T φ h s
      (d.shiftedCompletedInclusion (grade q β) p s hps a) =
      e.shiftedCompletedInclusion (grade q' β') (T p) (T s)
        (by simpa only [map_sub] using T.map_mem hps)
        (mapShiftedCompletion d e T φ h p a) := by
  apply (e.shiftedFiltration (grade q' β') (T s)).completion_ext
  intro k
  have h₁ := mapShiftedQuotient_projection d e T φ h s k
    (d.shiftedCompletedInclusion (grade q β) p s hps a)
  have h₂ := congrArg (mapShiftedQuotient d e T φ h s k)
    (d.projection_shiftedCompletedInclusion (grade q β) p s hps (T.modulus k) a)
  have h₃ := mapShiftedQuotient_shiftedQuotientMap q β d e T φ h p s hps k
    ((d.shiftedFiltration (grade q β) p).projection (T.modulus k) a)
  have h₄ := congrArg (e.shiftedQuotientMap (grade q' β') (T p) (T s)
    (by simpa only [map_sub] using T.map_mem hps) k)
    (mapShiftedQuotient_projection d e T φ h p k a)
  have h₅ := e.projection_shiftedCompletedInclusion (grade q' β') (T p) (T s)
    (by simpa only [map_sub] using T.map_mem hps) k
    (mapShiftedCompletion d e T φ h p a)
  exact h₁.symm.trans (h₂.trans (h₃.trans (h₄.trans h₅.symm)))

end Map

end Mei.QuantumMonoidAlgebra
