/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Specialization.Basic
public import Mei.Algebra.Lie.Logarithmic.Coefficient

/-!
# Twisted specialization of tropical coefficient actions

Weighted coefficient specialization intertwines tropical vertex actions on every
coefficient monoid containing the positive degrees. This supplies the ordinary
action comparison needed to extend specialization to completed coefficient algebras.

The proof restricts `LogarithmicVectorField.map_action` along the coefficient
monoid embedding. The twisted action follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section
noncomputable section

namespace Mei.LogarithmicVectorField

open _root_.AddMonoidAlgebra

section Coefficients

variable {K R S Γ Λ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (Q : AddSubmonoid Γ)
  (φ : R →ₐ[K] S) (χ : Multiplicative Γ →* S)

local notation "χQ" => χ.comp (Q.subtype.toMultiplicative)

/-- Weighted specialization intertwines the tropical action on every coefficient
monoid containing the positive degrees. -/
theorem weightedMap_tropicalVertexCoefficientAction (hQ : d.monoid ≤ Q)
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (a : R[Q]) :
    weightedMap φ χQ (tropicalVertexCoefficientAction d ρ Q hQ x a) =
      tropicalVertexCoefficientAction d ρ Q hQ (coefficientGradedLieHom ρ φ χ d x)
        (weightedMap φ χQ a) := by
  have hmap : (mapDomainAlgHom K S Q.subtype).comp (weightedMap φ χQ) =
      (weightedMap φ χ).comp (mapDomainAlgHom K R Q.subtype) := by
    apply algHom_ext
    · intro q
      simp [mapDomainAlgHom, mapDomainRingHom_apply]
    · ext r
      simp [mapDomainAlgHom, mapDomainRingHom_apply]
  have hcomm (a : R[Q]) :
      mapDomainRingHom S Q.subtype (weightedMap φ χQ a) =
        weightedMap φ χ (mapDomainRingHom R Q.subtype a) :=
    DFunLike.congr_fun hmap a
  apply mapDomain_injective Q.subtype_injective
  rw [← mapDomainRingHom_apply, ← mapDomainRingHom_apply, hcomm,
    mapDomain_tropicalVertexCoefficientAction, mapDomain_tropicalVertexCoefficientAction,
    coe_coefficientGradedLieHom, hcomm]
  exact map_action ρ φ χ (weightedMap φ χ) (weightedMap_single φ χ) x.val _

end Coefficients

end Mei.LogarithmicVectorField
