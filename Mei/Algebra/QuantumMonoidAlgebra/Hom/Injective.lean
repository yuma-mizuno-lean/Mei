/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Hom
public import Mei.Algebra.MonoidAlgebra.Twisted.Hom.Injective

/-!
# Coefficients under injective quantum exponent transport

An exponent map that is injective on the allowed source support does not combine
its coefficients. The scalar map may still annihilate coefficients; its
injectivity is a separate hypothesis when reflecting equality.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (φ : R →+* S) (f : Γ →+ Γ')
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))

/-- At an exponent where transport is injective on source support, the basis
coefficient is the image of the original coefficient. -/
theorem repr_map_of_injOn (P : Set Γ) (hf : Set.InjOn f P)
    (x : QuantumMonoidAlgebra q β)
    (hx : ∀ n, (basis q β).repr x n ≠ 0 → n ∈ P) (n : Γ) (hn : n ∈ P) :
    (basis q' β').repr (map φ f h x) (f n) = φ ((basis q β).repr x n) := by
  have hcompat := factorSet_map_compat φ f h
  have hinj : Set.InjOn f.toMultiplicative (Multiplicative.toAdd ⁻¹' P) := by
    intro a ha b hb hab
    exact hf ha hb hab
  have hsupp : ∀ g : Multiplicative Γ,
      (TauCeti.TwistedMonoidAlgebra.basis R (Multiplicative Γ) (factorSet q β)).repr
          (twistedEquiv q β x) g ≠ 0 →
        g ∈ Multiplicative.toAdd ⁻¹' P := by
    intro g hg
    apply hx g.toAdd
    rwa [basis_repr_apply, ofAdd_toAdd]
  rw [basis_repr_apply, basis_repr_apply, twistedEquiv_map]
  exact TwistedMonoidAlgebra.repr_map_of_injOn φ f.toMultiplicative hcompat
    (Multiplicative.toAdd ⁻¹' P) hinj _ hsupp (Multiplicative.ofAdd n) hn

end Mei.QuantumMonoidAlgebra
