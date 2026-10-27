/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Basic
public import Mei.Algebra.MonoidAlgebra.Twisted.Hom

/-!
# Coefficient and exponent maps of quantum algebras

A ring homomorphism carrying the quantum parameter to the target parameter and
an additive map preserving the integral form induce a quantum algebra map.
These maps preserve homogeneous pieces and respect identities and composition.
With fixed coefficients they are algebra homomorphisms; form-preserving additive
equivalences give algebra equivalences. No injectivity of an exponent map or
genericity of the quantum parameter is required.

We specialize `Mei.TwistedMonoidAlgebra.map`, constructed using the universal
property of Tau Ceti's twisted monoid algebra. The quantum multiplication convention
is that of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, Example 2.1(iii).
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S T Γ Γ' Γ'' : Type*}
  [CommRing R] [CommRing S] [CommRing T]
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  {q : Rˣ} {q' : Sˣ} {q'' : Tˣ}
  {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  {β'' : LinearMap.BilinForm ℤ Γ''}

/-- Simultaneous change of coefficients and exponents in a quantum algebra. -/
def map (φ : R →+* S) (f : Γ →+ Γ')
    (hq : Units.map φ.toMonoidHom q = q')
    (hβ : ∀ p r, β' (f p) (f r) = β p r) :
    QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra q' β' :=
  TwistedMonoidAlgebra.map φ f.toMultiplicative (by
    intro p r
    simp only [factorSet_apply, map_zpow, hq, AddMonoidHom.coe_toMultiplicative,
      Function.comp_apply]
    congr 1
    exact (hβ p.toAdd r.toAdd).symm)

/-- Quantum monomials map to monomials at the image exponent. -/
@[simp]
theorem map_monomial (φ : R →+* S) (f : Γ →+ Γ')
    (hq : Units.map φ.toMonoidHom q = q')
    (hβ : ∀ p r, β' (f p) (f r) = β p r) (p : Γ) :
    map φ f hq hβ (monomial q β p) = monomial q' β' (f p) := by
  simp [map, monomial_def]

/-- The quantum map applies the specified coefficient homomorphism to scalars. -/
@[simp]
theorem map_algebraMap (φ : R →+* S) (f : Γ →+ Γ')
    (hq : Units.map φ.toMonoidHom q = q')
    (hβ : ∀ p r, β' (f p) (f r) = β p r) (r : R) :
    map φ f hq hβ (algebraMap R _ r) = algebraMap S _ (φ r) := by
  apply TwistedMonoidAlgebra.map_algebraMap

/-- Quantum algebra maps are semilinear for their coefficient homomorphism. -/
@[simp]
theorem map_smul (φ : R →+* S) (f : Γ →+ Γ')
    (hq : Units.map φ.toMonoidHom q = q')
    (hβ : ∀ p r, β' (f p) (f r) = β p r)
    (r : R) (x : QuantumMonoidAlgebra q β) :
    map φ f hq hβ (r • x) = φ r • map φ f hq hβ x := by
  apply TwistedMonoidAlgebra.map_smul

/-- The identity changes neither coefficients nor exponents. -/
@[simp]
theorem map_id :
    map (RingHom.id R) (AddMonoidHom.id Γ) (q := q) (β := β)
      (by ext; rfl) (by intros; rfl) = RingHom.id _ := by
  apply TwistedMonoidAlgebra.ringHom_ext
  · intro r; simp
  · intro p
    simpa only [monomial_def, ofAdd_toAdd, AddMonoidHom.id_apply,
      RingHom.id_apply] using
      map_monomial (q := q) (β := β) (RingHom.id R) (AddMonoidHom.id Γ)
        (by ext; rfl) (by intros; rfl) p.toAdd

/-- Simultaneous quantum maps compose in both coefficients and exponents. -/
theorem map_comp (φ : R →+* S) (ψ : S →+* T) (f : Γ →+ Γ') (g : Γ' →+ Γ'')
    (hq : Units.map φ.toMonoidHom q = q')
    (hq' : Units.map ψ.toMonoidHom q' = q'')
    (hβ : ∀ p r, β' (f p) (f r) = β p r)
    (hβ' : ∀ p r, β'' (g p) (g r) = β' p r) :
    (map ψ g hq' hβ').comp (map φ f hq hβ) =
      map (ψ.comp φ) (g.comp f)
        (by rw [← hq', ← hq]; rfl)
        (by intro p r; rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hβ', hβ]) := by
  apply TwistedMonoidAlgebra.ringHom_ext
  · intro r; simp
  · intro p
    rw [← ofAdd_toAdd p, ← monomial_def q β p.toAdd]
    simp

/-- A homogeneous element maps into the homogeneous piece of its image exponent. -/
theorem map_mem_grade (φ : R →+* S) (f : Γ →+ Γ')
    (hq : Units.map φ.toMonoidHom q = q')
    (hβ : ∀ p r, β' (f p) (f r) = β p r)
    {p : Γ} {x : QuantumMonoidAlgebra q β} (hx : x ∈ grade q β p) :
    map φ f hq hβ x ∈ grade q' β' (f p) := by
  obtain ⟨r, rfl⟩ := (mem_grade_iff q β p x).mp hx
  exact (mem_grade_iff q' β' (f p) _).mpr ⟨φ r, by simp⟩

/-- A form-preserving exponent map with fixed coefficients is an algebra map. -/
def mapAlgHom (f : Γ →+ Γ') (hβ : ∀ p r, β' (f p) (f r) = β p r) :
    QuantumMonoidAlgebra q β →ₐ[R] QuantumMonoidAlgebra q β' where
  __ := map (RingHom.id R) f (by ext; rfl) hβ
  commutes' r := map_algebraMap (RingHom.id R) f _ hβ r

/-- Forgetting linearity recovers the simultaneous map with identity coefficients. -/
@[simp]
theorem coe_mapAlgHom (f : Γ →+ Γ')
    (hβ : ∀ p r, β' (f p) (f r) = β p r) :
    (mapAlgHom (q := q) f hβ :
      QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra q β') =
      map (RingHom.id R) f (by ext; rfl) hβ := (rfl)

/-- The algebra map has the prescribed effect on every quantum monomial. -/
@[simp]
theorem mapAlgHom_monomial (f : Γ →+ Γ')
    (hβ : ∀ p r, β' (f p) (f r) = β p r) (p : Γ) :
    mapAlgHom (q := q) f hβ (monomial q β p) = monomial q β' (f p) :=
  map_monomial (RingHom.id R) f (by ext; rfl) hβ p

/-- Form-preserving changes of exponent coordinates give quantum algebra equivalences. -/
def mapEquiv (e : Γ ≃+ Γ') (hβ : ∀ p r, β' (e p) (e r) = β p r) :
    QuantumMonoidAlgebra q β ≃ₐ[R] QuantumMonoidAlgebra q β' :=
  AlgEquiv.ofAlgHom (mapAlgHom e.toAddMonoidHom hβ)
    (mapAlgHom e.symm.toAddMonoidHom (by
      intro p r
      simpa using (hβ (e.symm p) (e.symm r)).symm))
    (by
      apply TauCeti.TwistedMonoidAlgebra.algHom_ext
      intro p
      rw [← ofAdd_toAdd p, ← monomial_def q β' p.toAdd]
      simp)
    (by
      apply TauCeti.TwistedMonoidAlgebra.algHom_ext
      intro p
      rw [← ofAdd_toAdd p, ← monomial_def q β p.toAdd]
      simp)

/-- The exponent equivalence is induced by its forward algebra map. -/
@[simp]
theorem mapEquiv_toAlgHom (e : Γ ≃+ Γ')
    (hβ : ∀ p r, β' (e p) (e r) = β p r) :
    (mapEquiv (q := q) e hβ).toAlgHom = mapAlgHom e.toAddMonoidHom hβ := by
  apply AlgEquiv.toAlgHom_ofAlgHom

/-- Coordinate transport preserves the coefficient of each monomial. -/
@[simp]
theorem mapEquiv_monomial (e : Γ ≃+ Γ')
    (hβ : ∀ p r, β' (e p) (e r) = β p r) (p : Γ) :
    mapEquiv (q := q) e hβ (monomial q β p) = monomial q β' (e p) := by
  exact (DFunLike.congr_fun (mapEquiv_toAlgHom e hβ) _).trans
    (mapAlgHom_monomial e.toAddMonoidHom hβ p)

/-- Inverse coordinate transport uses the inverse exponent map. -/
@[simp]
theorem mapEquiv_symm_monomial (e : Γ ≃+ Γ')
    (hβ : ∀ p r, β' (e p) (e r) = β p r) (p : Γ') :
    (mapEquiv (q := q) e hβ).symm (monomial q β' p) =
      monomial q β (e.symm p) := by
  apply (mapEquiv e hβ).injective
  simp

/-- Quantum coordinate transport preserves and reflects homogeneous membership. -/
@[simp]
theorem mapEquiv_mem_grade_iff (e : Γ ≃+ Γ')
    (hβ : ∀ p r, β' (e p) (e r) = β p r)
    (p : Γ) (x : QuantumMonoidAlgebra q β) :
    mapEquiv e hβ x ∈ grade q β' (e p) ↔ x ∈ grade q β p := by
  rw [mem_grade_iff, mem_grade_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, (mapEquiv e hβ).injective ?_⟩
    simpa using hr
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp⟩

end Mei.QuantumMonoidAlgebra
