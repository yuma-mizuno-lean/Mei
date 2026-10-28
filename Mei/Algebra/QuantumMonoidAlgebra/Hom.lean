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

A ring homomorphism `φ` and an additive map `f` induce a quantum algebra map when
they carry the factor sets to each other: `φ (q ^ β p r) = q' ^ β' (f p) (f r)`.
This holds when `φ q = q'` and `f` preserves the integral forms, but also, for
instance, for the specialization `q ↦ 1` onto the zero form. Quantum algebra maps
are determined by their values on scalars and monomials; the induced maps preserve
homogeneous pieces and respect identities and composition. With fixed coefficients
they are algebra homomorphisms, and additive equivalences compatible with the factor
sets give algebra equivalences. No injectivity of an exponent map or genericity of
the quantum parameter is required.

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

/-- Ring homomorphisms from a quantum algebra agree if they agree on scalars
and on all quantum monomials. -/
theorem ringHom_ext {A : Type*} [Semiring A]
    {f g : QuantumMonoidAlgebra q β →+* A}
    (hs : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hm : ∀ p, f (monomial q β p) = g (monomial q β p)) : f = g :=
  TwistedMonoidAlgebra.ringHom_ext hs fun p => by
    simpa only [monomial_def, ofAdd_toAdd] using hm p.toAdd

/-- Algebra homomorphisms from a quantum algebra agree if they agree on all
quantum monomials. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A]
    {f g : QuantumMonoidAlgebra q β →ₐ[R] A}
    (h : ∀ p, f (monomial q β p) = g (monomial q β p)) : f = g :=
  TauCeti.TwistedMonoidAlgebra.algHom_ext fun p => by
    simpa only [monomial_def, ofAdd_toAdd] using h p.toAdd

/-- Simultaneous change of coefficients and exponents in a quantum algebra,
for maps carrying the source factor set to the target factor set. -/
def map (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) :
    QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra q' β' :=
  TwistedMonoidAlgebra.map φ f.toMultiplicative fun p r => by
    simpa only [factorSet_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]
      using h p.toAdd r.toAdd

/-- Quantum monomials map to monomials at the image exponent. -/
@[simp]
theorem map_monomial (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) (p : Γ) :
    map φ f h (monomial q β p) = monomial q' β' (f p) := by
  simp [map, monomial_def]

/-- The quantum map applies the specified coefficient homomorphism to scalars. -/
@[simp]
theorem map_algebraMap (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) (r : R) :
    map φ f h (algebraMap R _ r) = algebraMap S _ (φ r) := by
  unfold map
  exact TwistedMonoidAlgebra.map_algebraMap _ _ _ r

/-- Quantum algebra maps are semilinear for their coefficient homomorphism. -/
@[simp]
theorem map_smul (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (r : R) (x : QuantumMonoidAlgebra q β) :
    map φ f h (r • x) = φ r • map φ f h x := by
  unfold map
  exact TwistedMonoidAlgebra.map_smul _ _ _ r x

/-- The identity changes neither coefficients nor exponents. -/
@[simp]
theorem map_id :
    map (RingHom.id R) (AddMonoidHom.id Γ) (q := q) (β := β) (fun _ _ => rfl) =
      RingHom.id _ := by
  simpa only [map, AddMonoidHom.toMultiplicative_id] using
    (TwistedMonoidAlgebra.map_id (α := factorSet q β))

/-- Simultaneous quantum maps compose in both coefficients and exponents. -/
theorem map_comp (φ : R →+* S) (ψ : S →+* T) (f : Γ →+ Γ') (g : Γ' →+ Γ'')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (g p) (g r)) :
    (map ψ g h').comp (map φ f h) =
      map (ψ.comp φ) (g.comp f) (fun p r => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← h', ← h]; rfl) := by
  unfold map
  exact TwistedMonoidAlgebra.map_comp φ ψ f.toMultiplicative g.toMultiplicative _ _

/-- Applying two simultaneous quantum maps in turn applies their composite. -/
@[simp]
theorem map_map (φ : R →+* S) (ψ : S →+* T) (f : Γ →+ Γ') (g : Γ' →+ Γ'')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (g p) (g r))
    (x : QuantumMonoidAlgebra q β) :
    map ψ g h' (map φ f h x) =
      map (ψ.comp φ) (g.comp f) (fun p r => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← h', ← h]; rfl) x :=
  RingHom.congr_fun (map_comp φ ψ f g h h') x

/-- A homogeneous element maps into the homogeneous piece of its image exponent. -/
theorem map_mem_grade (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    {p : Γ} {x : QuantumMonoidAlgebra q β} (hx : x ∈ grade q β p) :
    map φ f h x ∈ grade q' β' (f p) := by
  unfold map
  exact TwistedMonoidAlgebra.map_mem_grade φ f _ hx

/-- An exponent map compatible with the factor sets, with fixed coefficients,
is an algebra map. -/
def mapDomainAlgHom (f : Γ →+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (f p) (f r)) :
    QuantumMonoidAlgebra q β →ₐ[R] QuantumMonoidAlgebra q β' :=
  TwistedMonoidAlgebra.mapDomainAlgHom f.toMultiplicative fun p r => by
    simpa only [factorSet_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]
      using h p.toAdd r.toAdd

/-- Forgetting linearity recovers the simultaneous map with identity coefficients. -/
@[simp]
theorem coe_mapDomainAlgHom (f : Γ →+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (f p) (f r)) :
    (mapDomainAlgHom f h :
      QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra q β') =
      map (RingHom.id R) f h := by
  unfold mapDomainAlgHom map
  rw [TwistedMonoidAlgebra.coe_mapDomainAlgHom]

/-- The algebra map has the prescribed effect on every quantum monomial. -/
@[simp]
theorem mapDomainAlgHom_monomial (f : Γ →+ Γ')
    (h : ∀ p r, q ^ β p r = q ^ β' (f p) (f r)) (p : Γ) :
    mapDomainAlgHom f h (monomial q β p) = monomial q β' (f p) := by
  unfold mapDomainAlgHom
  simp only [monomial_def, TwistedMonoidAlgebra.mapDomainAlgHom_of,
    AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]

/-- Changes of exponent coordinates compatible with the factor sets give quantum
algebra equivalences. -/
def domCongr (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r)) :
    QuantumMonoidAlgebra q β ≃ₐ[R] QuantumMonoidAlgebra q β' :=
  TwistedMonoidAlgebra.domCongr e.toMultiplicative fun p r => by
    simpa only [factorSet_apply, AddEquiv.toMultiplicative_apply_apply, toAdd_ofAdd]
      using h p.toAdd r.toAdd

/-- The exponent equivalence is induced by its forward algebra map. -/
@[simp]
theorem domCongr_toAlgHom (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r)) :
    (domCongr e h).toAlgHom = mapDomainAlgHom e.toAddMonoidHom h := by
  unfold domCongr mapDomainAlgHom
  exact TwistedMonoidAlgebra.domCongr_toAlgHom _ _

/-- Coordinate transport sends each quantum monomial to the monomial at the
transported exponent. -/
@[simp]
theorem domCongr_monomial (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r))
    (p : Γ) :
    domCongr e h (monomial q β p) = monomial q β' (e p) := by
  unfold domCongr
  simp only [monomial_def, TwistedMonoidAlgebra.domCongr_of,
    AddEquiv.toMultiplicative_apply_apply, toAdd_ofAdd]

/-- Inverse coordinate transport uses the inverse exponent map. -/
@[simp]
theorem domCongr_symm_monomial (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r))
    (p : Γ') :
    (domCongr e h).symm (monomial q β' p) = monomial q β (e.symm p) := by
  unfold domCongr
  simp only [monomial_def, TwistedMonoidAlgebra.domCongr_symm_of,
    AddEquiv.toMultiplicative_apply_symm_apply, toAdd_ofAdd]

/-- Quantum coordinate transport preserves and reflects homogeneous membership. -/
@[simp]
theorem domCongr_mem_grade_iff (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r))
    (p : Γ) (x : QuantumMonoidAlgebra q β) :
    domCongr e h x ∈ grade q β' (e p) ↔ x ∈ grade q β p := by
  unfold domCongr
  exact TwistedMonoidAlgebra.domCongr_mem_grade_iff e _ p x

end Mei.QuantumMonoidAlgebra
