/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Twisted.Grading

/-!
# Maps of twisted monoid algebras

A coefficient homomorphism and a monoid homomorphism induce a ring homomorphism
when they carry the source factor set to the target factor set. The map sends
each basis vector to the vector at the image exponent and applies the coefficient
homomorphism to scalars. These maps respect identity, composition, and exponent
grades. With fixed coefficients they give algebra maps, and compatible monoid
equivalences give algebra equivalences. This allows specialization and coordinate
transport of twisted coefficient algebras.

The construction uses `TauCeti.TwistedMonoidAlgebra.lift`, with scalars restricted
along the coefficient homomorphism using `Algebra.compHom`.
-/

public section

noncomputable section

namespace Mei.TwistedMonoidAlgebra

open TauCeti TauCeti.TwistedMonoidAlgebra

variable {R S G H : Type*} [CommSemiring R] [CommSemiring S] [Monoid G] [Monoid H]
  {α : G → G → Rˣ} {β : H → H → Sˣ} [IsFactorSet α] [IsFactorSet β]

/-- Change coefficients and exponents, preserving the twisting factor set. -/
def map (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j)) :
    twistedMonoidAlgebra R G α →+* twistedMonoidAlgebra S H β :=
  letI := Algebra.compHom (twistedMonoidAlgebra S H β) φ
  (lift (fun g => of (f g)) (by simp) (by
    intro g j
    rw [of_mul_of, map_mul]
    exact congrArg (fun u : Sˣ => (u : S) • (of (f g * f j) :
      twistedMonoidAlgebra S H β)) (h g j).symm)).toRingHom

/-- A twisted basis vector maps to the vector at the image exponent. -/
@[simp]
theorem map_of (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j)) (g : G) :
    map φ f h (of g) = of (f g) := by
  simp [map]

/-- The coefficient map on a twisted algebra restricts to the given scalar map. -/
@[simp]
theorem map_algebraMap (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j)) (r : R) :
    map φ f h (algebraMap R _ r) = algebraMap S _ (φ r) := by
  -- `map` is the ring map underlying `lift`, an algebra map for `Algebra.compHom`, whose
  -- `algebraMap` is by definition `algebraMap S _ ∘ φ`.
  let := Algebra.compHom (twistedMonoidAlgebra S H β) φ
  exact (lift (fun g => of (f g)) _ _).commutes r

/-- Coefficients transform semilinearly under a twisted algebra map. -/
theorem map_smul (φ : R →+* S) (f : G →* H)
    (h : ∀ g j, Units.map φ.toMonoidHom (α g j) = β (f g) (f j))
    (r : R) (x : twistedMonoidAlgebra R G α) :
    map φ f h (r • x) = φ r • map φ f h x := by
  simp only [Algebra.smul_def, map_mul, map_algebraMap]

/-- Ring homomorphisms from a twisted algebra agree if they agree on scalars
and on all twisted basis vectors. -/
theorem ringHom_ext {A : Type*} [Semiring A]
    {f g : twistedMonoidAlgebra R G α →+* A}
    (hs : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hb : ∀ j, f (of j) = g (of j)) : f = g := by
  ext x
  rw [← (basis R G α).linearCombination_repr x, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, Algebra.smul_def, map_mul, basis_apply, hs, hb]

/-- The identity changes neither coefficients nor exponents. -/
@[simp]
theorem map_id :
    map (RingHom.id R) (MonoidHom.id G) (α := α) (fun _ _ => rfl) = RingHom.id _ :=
  ringHom_ext (fun r => map_algebraMap _ _ _ r) fun g => map_of _ _ _ g

variable {T K : Type*} [CommSemiring T] [Monoid K]
  {γ : K → K → Tˣ} [IsFactorSet γ]

/-- Compatible twisted algebra maps compose in both coefficients and exponents. -/
theorem map_comp (φ : R →+* S) (ψ : S →+* T) (f : G →* H) (g : H →* K)
    (h : ∀ i j, Units.map φ.toMonoidHom (α i j) = β (f i) (f j))
    (h' : ∀ i j, Units.map ψ.toMonoidHom (β i j) = γ (g i) (g j)) :
    (map ψ g h').comp (map φ f h) =
      map (ψ.comp φ) (g.comp f) (fun i j => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← h', ← h]; rfl) :=
  ringHom_ext (fun r => by simp) fun i => by simp

/-- Applying two twisted algebra maps in turn applies their composite. -/
@[simp]
theorem map_map (φ : R →+* S) (ψ : S →+* T) (f : G →* H) (g : H →* K)
    (h : ∀ i j, Units.map φ.toMonoidHom (α i j) = β (f i) (f j))
    (h' : ∀ i j, Units.map ψ.toMonoidHom (β i j) = γ (g i) (g j))
    (x : twistedMonoidAlgebra R G α) :
    map ψ g h' (map φ f h x) =
      map (ψ.comp φ) (g.comp f) (fun i j => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← h', ← h]; rfl) x :=
  RingHom.congr_fun (map_comp φ ψ f g h h') x

variable {δ : H → H → Rˣ} [IsFactorSet δ]

/-- A compatible exponent map with fixed coefficients is an algebra map. -/
def mapDomainAlgHom (f : G →* H) (h : ∀ i j, α i j = δ (f i) (f j)) :
    twistedMonoidAlgebra R G α →ₐ[R] twistedMonoidAlgebra R H δ where
  __ := map (RingHom.id R) f h
  commutes' r := map_algebraMap (RingHom.id R) f h r

/-- Forgetting linearity recovers the map with identity coefficients. -/
@[simp]
theorem coe_mapDomainAlgHom (f : G →* H) (h : ∀ i j, α i j = δ (f i) (f j)) :
    (mapDomainAlgHom f h : twistedMonoidAlgebra R G α →+* twistedMonoidAlgebra R H δ) =
      map (RingHom.id R) f h := (rfl)

/-- An exponent algebra map sends basis vectors to the indicated basis vectors. -/
@[simp]
theorem mapDomainAlgHom_of (f : G →* H) (h : ∀ i j, α i j = δ (f i) (f j)) (i : G) :
    mapDomainAlgHom f h (of i) = of (f i) :=
  map_of (RingHom.id R) f h i

/-- Compatible monoid equivalences induce twisted algebra equivalences. -/
def domCongr (e : G ≃* H) (h : ∀ i j, α i j = δ (e i) (e j)) :
    twistedMonoidAlgebra R G α ≃ₐ[R] twistedMonoidAlgebra R H δ :=
  AlgEquiv.ofAlgHom (mapDomainAlgHom e.toMonoidHom h)
    (mapDomainAlgHom e.symm.toMonoidHom fun i j => by
      simpa using (h (e.symm i) (e.symm j)).symm)
    (algHom_ext fun i => by simp)
    (algHom_ext fun i => by simp)

/-- Coordinate transport is induced by its forward algebra map. -/
@[simp]
theorem domCongr_toAlgHom (e : G ≃* H) (h : ∀ i j, α i j = δ (e i) (e j)) :
    (domCongr e h).toAlgHom = mapDomainAlgHom e.toMonoidHom h := by
  apply AlgEquiv.toAlgHom_ofAlgHom

/-- Coordinate transport sends basis vectors to the transported exponents. -/
@[simp]
theorem domCongr_of (e : G ≃* H) (h : ∀ i j, α i j = δ (e i) (e j)) (i : G) :
    domCongr e h (of i) = of (e i) :=
  (DFunLike.congr_fun (domCongr_toAlgHom e h) _).trans
    (mapDomainAlgHom_of e.toMonoidHom h i)

/-- Inverse coordinate transport uses the inverse monoid equivalence. -/
@[simp]
theorem domCongr_symm_of (e : G ≃* H) (h : ∀ i j, α i j = δ (e i) (e j)) (i : H) :
    (domCongr e h).symm (of i) = of (e.symm i) := by
  apply (domCongr e h).injective
  simp

section Grading

variable {M N : Type*} [AddMonoid M] [AddMonoid N]
  {α : Multiplicative M → Multiplicative M → Rˣ}
  {β : Multiplicative N → Multiplicative N → Sˣ}
  {δ : Multiplicative N → Multiplicative N → Rˣ}
  [IsFactorSet α] [IsFactorSet β] [IsFactorSet δ]

/-- A homogeneous element maps into the homogeneous piece at its image exponent. -/
theorem map_mem_grade (φ : R →+* S) (f : M →+ N)
    (h : ∀ i j, Units.map φ.toMonoidHom (α i j) =
      β (f.toMultiplicative i) (f.toMultiplicative j))
    {m : M} {x : twistedMonoidAlgebra R (Multiplicative M) α}
    (hx : x ∈ grade R α m) :
    map φ f.toMultiplicative h x ∈ grade S β (f m) := by
  obtain ⟨r, rfl⟩ := (mem_grade_iff R α m x).mp hx
  exact (mem_grade_iff S β (f m) _).mpr ⟨φ r, by simp [map_smul]⟩

/-- Coordinate transport preserves and reflects homogeneous membership. -/
@[simp]
theorem domCongr_mem_grade_iff (e : M ≃+ N)
    (h : ∀ i j, α i j = δ (e.toMultiplicative i) (e.toMultiplicative j))
    (m : M) (x : twistedMonoidAlgebra R (Multiplicative M) α) :
    domCongr e.toMultiplicative h x ∈ grade R δ (e m) ↔ x ∈ grade R α m := by
  simpa [mem_grade_iff, Submodule.mem_span_singleton] using
    Submodule.apply_mem_span_image_iff_mem_span
    (f := (domCongr e.toMultiplicative h).toLinearMap)
    (s := {of (Multiplicative.ofAdd m)}) (x := x)
    (domCongr e.toMultiplicative h).injective

end Grading

end Mei.TwistedMonoidAlgebra
