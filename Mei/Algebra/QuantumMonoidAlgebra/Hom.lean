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

We transport `Mei.TwistedMonoidAlgebra.map`, constructed using the universal
property of Tau Ceti's twisted monoid algebra, along `twistedEquiv`. The quantum
multiplication convention is that of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(iii).
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
  RingHom.ext fun x => by
    have h := TwistedMonoidAlgebra.ringHom_ext (α := factorSet q β)
      (f := f.comp ((twistedEquiv q β).symm : _ →+* QuantumMonoidAlgebra q β))
      (g := g.comp ((twistedEquiv q β).symm : _ →+* QuantumMonoidAlgebra q β))
      (fun r => by simpa using hs r) fun p => by simpa using hm p.toAdd
    simpa using RingHom.congr_fun h (twistedEquiv q β x)

/-- Algebra homomorphisms from a quantum algebra agree if they agree on all
quantum monomials. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A]
    {f g : QuantumMonoidAlgebra q β →ₐ[R] A}
    (h : ∀ p, f (monomial q β p) = g (monomial q β p)) : f = g :=
  AlgHom.toRingHom_injective <| ringHom_ext (fun r => by simp) h

/-- Factor-set compatibility in the original additive exponents gives compatibility
in the multiplicative exponents of the twisted algebra. -/
theorem factorSet_map_compat (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (p r : Multiplicative Γ) :
    Units.map φ.toMonoidHom (factorSet q β p r) =
      factorSet q' β' (f.toMultiplicative p) (f.toMultiplicative r) := by
  simpa only [factorSet_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]
    using h p.toAdd r.toAdd

/-- Simultaneous change of coefficients and exponents in a quantum algebra,
for maps carrying the source factor set to the target factor set. -/
def map (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) :
    QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra q' β' :=
  ((twistedEquiv q' β').symm : _ →+* _).comp <|
    (TwistedMonoidAlgebra.map φ f.toMultiplicative (factorSet_map_compat φ f h)).comp
      (twistedEquiv q β : _ →+* _)

/-- The equivalence and the quantum map compose to the twisted map. -/
theorem twistedEquiv_comp_map (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) :
    (twistedEquiv q' β' : _ →+* _).comp (map φ f h) =
      (TwistedMonoidAlgebra.map φ f.toMultiplicative (factorSet_map_compat φ f h)).comp
        (twistedEquiv q β : _ →+* _) := by
  ext x
  simp [map]

/-- Transporting a quantum map to the twisted algebra gives the twisted map. -/
@[simp]
theorem twistedEquiv_map (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (x : QuantumMonoidAlgebra q β) :
    twistedEquiv q' β' (map φ f h x) =
      TwistedMonoidAlgebra.map φ f.toMultiplicative (factorSet_map_compat φ f h)
        (twistedEquiv q β x) :=
  RingHom.congr_fun (twistedEquiv_comp_map φ f h) x

/-- Transporting a twisted map back to the quantum algebra gives the quantum map. -/
theorem twistedEquiv_symm_twistedMap (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (x : TauCeti.twistedMonoidAlgebra R (Multiplicative Γ) (factorSet q β)) :
    (twistedEquiv q' β').symm
        (TwistedMonoidAlgebra.map φ f.toMultiplicative (factorSet_map_compat φ f h) x) =
      map φ f h ((twistedEquiv q β).symm x) := by
  apply (twistedEquiv q' β').injective
  rw [twistedEquiv_map]
  simp

/-- Quantum monomials map to monomials at the image exponent. -/
@[simp]
theorem map_monomial (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) (p : Γ) :
    map φ f h (monomial q β p) = monomial q' β' (f p) := by
  simp [map, TwistedMonoidAlgebra.map_of]

/-- The quantum map applies the specified coefficient homomorphism to scalars. -/
@[simp]
theorem map_algebraMap (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) (r : R) :
    map φ f h (algebraMap R _ r) = algebraMap S _ (φ r) := by
  simp [map, TwistedMonoidAlgebra.map_algebraMap]

/-- Quantum algebra maps are semilinear for their coefficient homomorphism. -/
@[simp↓]
theorem map_smul (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (r : R) (x : QuantumMonoidAlgebra q β) :
    map φ f h (r • x) = φ r • map φ f h x := by
  simp only [Algebra.smul_def, _root_.map_mul, map_algebraMap]

/-- The identity changes neither coefficients nor exponents. -/
@[simp]
theorem map_id :
    map (RingHom.id R) (AddMonoidHom.id Γ) (q := q) (β := β) (fun _ _ => rfl) =
      RingHom.id _ :=
  ringHom_ext (fun r => map_algebraMap _ _ _ r) fun p => map_monomial _ _ _ p

/-- Factor-set compatibility is preserved by composition of scalar and exponent maps. -/
theorem map_comp_compat (φ : R →+* S) (ψ : S →+* T) (f : Γ →+ Γ') (g : Γ' →+ Γ'')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (g p) (g r))
    (p r : Γ) :
    Units.map (ψ.comp φ).toMonoidHom (q ^ β p r) = q'' ^ β'' ((g.comp f) p) ((g.comp f) r) := by
  -- The multiplicative projection of a ring-hom composition is the monoid-hom composition.
  change Units.map (ψ.toMonoidHom.comp φ.toMonoidHom) (q ^ β p r) = _
  rw [Units.map_comp, MonoidHom.comp_apply, h, h']
  simp only [AddMonoidHom.comp_apply]

/-- Simultaneous quantum maps compose in both coefficients and exponents. -/
theorem map_comp (φ : R →+* S) (ψ : S →+* T) (f : Γ →+ Γ') (g : Γ' →+ Γ'')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (h' : ∀ p r, Units.map ψ.toMonoidHom (q' ^ β' p r) = q'' ^ β'' (g p) (g r)) :
    (map ψ g h').comp (map φ f h) =
      map (ψ.comp φ) (g.comp f) (fun p r => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← h', ← h]; rfl) :=
  ringHom_ext (fun r => by simp) fun p => by simp

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
  obtain ⟨r, rfl⟩ := (mem_grade_iff q β p x).mp hx
  exact (mem_grade_iff q' β' (f p) _).mpr ⟨φ r, by simp⟩

/-- A coefficient algebra map and a compatible exponent map induce an algebra map
over the common scalar ring. -/
def mapAlgHom {k : Type*} [CommRing k] [Algebra k R] [Algebra k S]
    (φ : R →ₐ[k] S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) :
    QuantumMonoidAlgebra q β →ₐ[k] QuantumMonoidAlgebra q' β' where
  toRingHom := map φ.toRingHom f h
  commutes' r := by
    simpa only [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, φ.commutes,
      ← IsScalarTower.algebraMap_apply] using
      map_algebraMap φ.toRingHom f h (algebraMap k R r)

/-- Forgetting the common scalar structure recovers the simultaneous quantum map. -/
@[simp]
theorem coe_mapAlgHom {k : Type*} [CommRing k] [Algebra k R] [Algebra k S]
    (φ : R →ₐ[k] S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r)) :
    (mapAlgHom φ f h : QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra q' β') =
      map φ.toRingHom f h := (rfl)

/-- The common-base algebra map agrees pointwise with the quantum ring map. -/
@[simp]
theorem mapAlgHom_apply {k : Type*} [CommRing k] [Algebra k R] [Algebra k S]
    (φ : R →ₐ[k] S) (f : Γ →+ Γ')
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
    (x : QuantumMonoidAlgebra q β) :
    mapAlgHom φ f h x = map φ.toRingHom f h x := (rfl)

/-- Restricting scalars to the common base preserves homogeneity of coefficient change. -/
theorem coefficientMap_mem_grade {k : Type*} {β' : LinearMap.BilinForm ℤ Γ}
    [CommRing k] [Algebra k R] [Algebra k S]
    (φ : R →ₐ[k] S)
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' p r) (u : Γ) :
    (grade q β u).restrictScalars k ≤ ((grade q' β' u).restrictScalars k).comap
      (mapAlgHom φ (AddMonoidHom.id Γ) h).toLinearMap := by
  intro x hx
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, AlgHom.toLinearMap_apply,
    mapAlgHom_apply]
  exact map_mem_grade φ.toRingHom (AddMonoidHom.id Γ) h hx

/-- An exponent map compatible with the factor sets, with fixed coefficients,
is an algebra map. -/
def mapDomainAlgHom (f : Γ →+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (f p) (f r)) :
    QuantumMonoidAlgebra q β →ₐ[R] QuantumMonoidAlgebra q β' where
  __ := map (RingHom.id R) f h
  commutes' r := map_algebraMap (RingHom.id R) f h r

/-- Forgetting linearity recovers the simultaneous map with identity coefficients. -/
@[simp]
theorem coe_mapDomainAlgHom (f : Γ →+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (f p) (f r)) :
    (mapDomainAlgHom f h :
      QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra q β') =
      map (RingHom.id R) f h := (rfl)

/-- The algebra map has the prescribed effect on every quantum monomial. -/
@[simp]
theorem mapDomainAlgHom_monomial (f : Γ →+ Γ')
    (h : ∀ p r, q ^ β p r = q ^ β' (f p) (f r)) (p : Γ) :
    mapDomainAlgHom f h (monomial q β p) = monomial q β' (f p) :=
  map_monomial (RingHom.id R) f h p

/-- Changes of exponent coordinates compatible with the factor sets give quantum
algebra equivalences. -/
def domCongr (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r)) :
    QuantumMonoidAlgebra q β ≃ₐ[R] QuantumMonoidAlgebra q β' :=
  AlgEquiv.ofAlgHom (mapDomainAlgHom e.toAddMonoidHom h)
    (mapDomainAlgHom e.symm.toAddMonoidHom fun p r => by
      simpa using (h (e.symm p) (e.symm r)).symm)
    (algHom_ext fun p => by simp) (algHom_ext fun p => by simp)

/-- The exponent equivalence is induced by its forward algebra map. -/
@[simp]
theorem domCongr_toAlgHom (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r)) :
    (domCongr e h).toAlgHom = mapDomainAlgHom e.toAddMonoidHom h :=
  AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

/-- Coordinate transport sends each quantum monomial to the monomial at the
transported exponent. -/
@[simp]
theorem domCongr_monomial (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r))
    (p : Γ) :
    domCongr e h (monomial q β p) = monomial q β' (e p) :=
  mapDomainAlgHom_monomial e.toAddMonoidHom h p

/-- Inverse coordinate transport uses the inverse exponent map. -/
@[simp]
theorem domCongr_symm_monomial (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r))
    (p : Γ') :
    (domCongr e h).symm (monomial q β' p) = monomial q β (e.symm p) := by
  apply (domCongr e h).injective
  simp

/-- Quantum coordinate transport preserves and reflects homogeneous membership. -/
@[simp]
theorem domCongr_mem_grade_iff (e : Γ ≃+ Γ') (h : ∀ p r, q ^ β p r = q ^ β' (e p) (e r))
    (p : Γ) (x : QuantumMonoidAlgebra q β) :
    domCongr e h x ∈ grade q β' (e p) ↔ x ∈ grade q β p := by
  simp only [mem_grade_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, (domCongr e h).injective (by simp [hr])⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp⟩

end Mei.QuantumMonoidAlgebra
