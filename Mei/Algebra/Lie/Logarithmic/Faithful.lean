/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.Algebra.Lie.Logarithmic.Detection

/-!
# Faithful tropical vertex actions on positive coefficients

If the spatial images of the positive monoid span the rational tangent space,
the tropical vertex action on the completed positive coefficient algebra is
faithful. A surviving Lie degree is detected on a positive monomial; its output
has degree too small to belong to the excluded coefficient filtration term.
The coefficient test may have arbitrarily high degree, so this does not assert
faithfulness of the representations at individual cutoffs.

This connects `exists_action_apply_single_coeff_ne_zero_of_notMem_degreeSubmodule`
to `AlgFiltration.completedBCHAction_injective`, using the monomial ideal support
characterization and `mapDomain_tropicalVertexCoefficientAction`. The action and
its spanning hypothesis are those of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

open scoped TensorProduct Mei.TropicalVertexCoefficientAction

namespace Mei.TropicalVertexCoefficientAction

open _root_.AddMonoidAlgebra

variable {R Γ Λ : Type*} [CommRing R] [Algebra ℚ R]
  [AddCancelCommMonoid Γ] [AddCommGroup Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)

local instance : Fact (d.monoid ≤ d.monoid) := ⟨le_rfl⟩

/-- Rationally spanning positive spatial exponents detect the logarithmic Lie
action in the positive coefficient filtration. -/
theorem isFiltrationDetected
    (hspan : Submodule.span ℚ
      ((fun p : Γ => (1 : ℚ) ⊗ₜ[ℤ] ρ p) '' (d.monoid : Set Γ)) = ⊤) :
    IsFiltrationDetected d (tropicalVertexGrading (R := R) d ρ)
      ((filtration (R := R) d d.monoid).toModuleFiltration R) where
  exists_lie_not_mem {k x} hx := by
    classical
    obtain ⟨n, hn, _, hnk, p, hp, hne⟩ :=
      exists_action_apply_single_coeff_ne_zero_of_notMem_degreeSubmodule d ρ hspan x hx
    let b := (d.degree p).toNat
    have hb : (b : ℤ) = d.degree p := Int.toNat_of_nonneg (d.degree_nonneg hp)
    let a : R[d.monoid] := single ⟨p, hp⟩ 1
    let f := tropicalVertexCoefficientAction d ρ d.monoid le_rfl x a
    have hmap : mapDomainRingHom R d.monoid.subtype f =
        LogarithmicVectorField.action ρ x.val (single p 1) := by
      rw [mapDomain_tropicalVertexCoefficientAction]
      simp [a, mapDomainRingHom_apply]
    -- Embedding the exponent subtype preserves each individual coefficient.
    have hc : f.coeff (⟨n, hn⟩ + ⟨p, hp⟩) ≠ 0 := by
      rw [← hmap] at hne
      have he : (mapDomainRingHom R d.monoid.subtype f).coeff
          ((⟨n, hn⟩ + ⟨p, hp⟩ : d.monoid) : Γ) =
          f.coeff (⟨n, hn⟩ + ⟨p, hp⟩) := by
        exact Finsupp.mapDomain_apply_of_injective d.monoid.subtype_injective
          f.coeff (⟨n, hn⟩ + ⟨p, hp⟩)
      exact fun hz => hne (he.trans hz)
    have htop : d.monoid.comap d.monoid.subtype = ⊤ := by
      ext q
      simp
    refine ⟨b, a, ?_, ?_⟩
    · simp only [Submodule.restrictScalars_mem,
        filtration_ideal, htop,
        AddSubmonoid.mem_monoidAlgebraIdeal_top_iff_of_nonneg
          (δ := d.degree.comp d.monoid.subtype)
          (fun q : d.monoid => d.degree_nonneg q.property)]
      intro q hq
      have hqp : q = ⟨p, hp⟩ := (Finsupp.mem_support_single _ _ _).mp hq |>.1
      subst q
      exact hb.le
    · intro hf
      simp only [Submodule.restrictScalars_mem,
        filtration_ideal, lie_eq, htop,
        AddSubmonoid.mem_monoidAlgebraIdeal_top_iff_of_nonneg
          (δ := d.degree.comp d.monoid.subtype)
          (fun q : d.monoid => d.degree_nonneg q.property)] at hf
      have hd := hf (⟨n, hn⟩ + ⟨p, hp⟩) (Finsupp.mem_support_iff.mpr hc)
      simp only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply,
        map_add, Nat.cast_add, Nat.cast_ofNat] at hd
      omega

variable [DecidableEq Γ]

/-- The completed tropical vertex group acts faithfully on the completed positive
coefficient algebra when its spatial exponents span the rational tangent space. -/
theorem completedBCHAction_injective
    (hspan : Submodule.span ℚ
      ((fun p : Γ => (1 : ℚ) ⊗ₜ[ℤ] ρ p) '' (d.monoid : Set Γ)) = ⊤) :
    Function.Injective ((filtration (R := R) d d.monoid).completedBCHAction d
      (tropicalVertexGrading (R := R) d ρ)) := by
  let := isFiltrationDetected (R := R) d ρ hspan
  exact AlgFiltration.completedBCHAction_injective _ _ _

end Mei.TropicalVertexCoefficientAction
