/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Specialization
public import Mei.RingTheory.FilteredAlgebra.Positive.Basic

/-!
# Positive specializations of tropical vertex coefficients

A twisted coefficient change `r z^q ↦ φ(r) χ(q) z^q` on a coefficient monoid algebra
`R[Q]`, possibly followed by the monomial map `z^q ↦ z^(T q)` of a tropical pairing, is
filtered for the positive-increment filtrations, with the identity cutoff modulus
respectively the cutoff modulus of `T`. If it also maps a chosen positive subsemiring of
`R[Q]` into one of the target, it is a positive specialization
(`Mei.PositiveSpecialization`). Its completion map then intertwines the completed BCH
actions of the coefficient Lie algebras with the induced map of labels. In particular it
sends the represented action of a path product to the represented action of the
transported path product. Consequently, if a label carries an element to a positive
element, then the transported label carries the specialized element to a positive element.

The positive subsemirings of interest are images `ι(A)[Q]` of coefficient semirings, such
as `ℕ[A][Q] ⊆ ℚ[A][Q]`. The twisted maps send `ι(A)[Q]` into `ι'(A')[Q']` when `φ` sends
`ι(A)` into `ι'(A')` and the weights `χ` lie in `ι'(A')`
(`AddMonoidAlgebra.map_mem_rangeS_mapRingHom`). Coefficientwise substitutions of the
variables `A` by elements of a positive subsemiring, as at `a = 1`, are of this form.

## Main definitions

* `Mei.LogarithmicVectorField.coefficientMonoidPositiveSpecialization`: a monoid-local
  twisted coefficient change as a positive specialization with identity cutoff modulus.
* `Mei.TropicalPairing.coefficientPositiveSpecialization`: a twisted coefficient change
  followed by the monomial map of a tropical pairing as a positive specialization.

## Main statements

* `Mei.LogarithmicVectorField.coefficientMonoidPositiveSpecialization_completedBCHAction`
  and `Mei.TropicalPairing.coefficientPositiveSpecialization_completedBCHAction`: the
  completion maps intertwine completed BCH actions.
* `Mei.LogarithmicVectorField.isPositive_completedBCHAction_coefficientMonoidGradedLieHom` and
  `Mei.TropicalPairing.isPositive_completedBCHAction_coefficientGradedLieHom`: positivity of
  the action of a label is preserved by specialization.

The coefficient maps are the twisted coefficient changes of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
Positivity of wall functions and its preservation under coefficient specialization appear in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1,
arXiv:1411.1394v2, and Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §8.1, arXiv:2503.03719v1.
-/

public section

noncomputable section

namespace AddMonoidAlgebra

variable {A A' R S M M' : Type*} [Semiring A] [Semiring A'] [Semiring R] [Semiring S]
  [AddMonoid M] [AddMonoid M']

/-- An additive map between monoid algebras sends the image `ι(A)[M]` of the coefficients
`A` into the image `ι'(A')[M']` as soon as it does so on the monomials `ι(a) z^m`. -/
theorem map_mem_rangeS_mapRingHom (ι : A →+* R) (ι' : A' →+* S) (f : R[M] →+ S[M'])
    (hf : ∀ (m : M) (a : A), f (single m (ι a)) ∈ (mapRingHom M' ι').rangeS)
    {x : R[M]} (hx : x ∈ (mapRingHom M ι).rangeS) :
    f x ∈ (mapRingHom M' ι').rangeS := by
  obtain ⟨y, rfl⟩ := hx
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => simpa only [map_add] using add_mem hy hz
  | single m a => simpa only [mapRingHom_single] using hf m a

end AddMonoidAlgebra

namespace Mei.LogarithmicVectorField

open _root_.AddMonoidAlgebra

section Specialization

variable {K R S Γ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ]
  (d : PositiveDegrees Γ) (Q : AddSubmonoid Γ)
  (φ : R →ₐ[K] S) (χ : Multiplicative Q →* S)
  (f : R[Q] →ₐ[K] S[Q])
  (hf : ∀ (p : Q) r, f (_root_.AddMonoidAlgebra.single p r) =
    _root_.AddMonoidAlgebra.single p (φ r * χ (.ofAdd p)))
  (P : Subsemiring R[Q]) (P' : Subsemiring S[Q]) (hP : ∀ a ∈ P, f a ∈ P')

/-- A monoid-local twisted coefficient change `r z^q ↦ φ(r) χ(q) z^q` mapping the chosen
positive subsemirings into each other is a positive specialization of coefficient algebras,
with the identity cutoff modulus. -/
def coefficientMonoidPositiveSpecialization :
    PositiveSpecialization (TropicalVertexCoefficientAction.filtration (R := R) d Q)
      (TropicalVertexCoefficientAction.filtration (R := S) d Q) P P' where
  toRingHom := f
  exists_modulus := ⟨id, monotone_id, fun k =>
    filtration_ideal_le_comap_coefficientMonoidMap d Q φ χ f hf (k + 1)⟩
  map_mem := hP

@[simp]
theorem coefficientMonoidPositiveSpecialization_toRingHom :
    (coefficientMonoidPositiveSpecialization d Q φ χ f hf P P' hP).toRingHom = f :=
  (rfl)

/-- The completion map of the specialization is the completed algebra map with the
identity cutoff modulus. -/
theorem coe_completionMap_coefficientMonoidPositiveSpecialization :
    ⇑(coefficientMonoidPositiveSpecialization d Q φ χ f hf P P' hP).completionMap =
      (TropicalVertexCoefficientAction.filtration (R := R) d Q).mapCompletionₐ
        (TropicalVertexCoefficientAction.filtration (R := S) d Q) f id monotone_id
        (fun k => filtration_ideal_le_comap_coefficientMonoidMap d Q φ χ f hf (k + 1)) := by
  rw [PositiveSpecialization.completionMap_eq_mapCompletion _ id monotone_id
    (fun k => filtration_ideal_le_comap_coefficientMonoidMap d Q φ χ f hf (k + 1))]
  exact congrArg DFunLike.coe (AlgFiltration.coe_mapCompletionₐ _ _ f id monotone_id _).symm

include hf in
/-- If `φ` sends `ι(A)` into `ι'(A')` and every weight `χ(q)` lies in `ι'(A')`, the twisted
coefficient change sends `ι(A)[Q]` into `ι'(A')[Q]`. -/
theorem map_mem_rangeS_mapRingHom_coefficientMonoidMap {A A' : Type*} [Semiring A]
    [Semiring A'] (ι : A →+* R) (ι' : A' →+* S) (hφ : ∀ a, φ (ι a) ∈ ι'.rangeS)
    (hχ : ∀ q, χ q ∈ ι'.rangeS) {x : R[Q]} (hx : x ∈ (mapRingHom Q ι).rangeS) :
    f x ∈ (mapRingHom Q ι').rangeS := by
  refine AddMonoidAlgebra.map_mem_rangeS_mapRingHom ι ι' f.toAddMonoidHom (fun q a => ?_) hx
  obtain ⟨c, hc⟩ := ι'.rangeS.mul_mem (hφ a) (hχ (.ofAdd q))
  exact ⟨_root_.AddMonoidAlgebra.single q c, by simp [hf, hc]⟩

end Specialization

section Action

open scoped TropicalVertexCoefficientAction

variable {R S : Type u} {Γ : Type v} {Λ : Type w}
  [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (Q : AddSubmonoid Γ)
  [Fact (d.monoid ≤ Q)] (φ : R →ₐ[ℚ] S) (χ : Multiplicative Q →* S)
  (f : R[Q] →ₐ[ℚ] S[Q])
  (hf : ∀ (p : Q) r, f (_root_.AddMonoidAlgebra.single p r) =
    _root_.AddMonoidAlgebra.single p (φ r * χ (.ofAdd p)))
  {P : Subsemiring R[Q]} {P' : Subsemiring S[Q]} (hP : ∀ a ∈ P, f a ∈ P')

local instance : LieModule ℚ (tropicalVertexLieAlgebra (R := R) d ρ) R[Q] :=
  LieModule.restrictScalars ℚ R _ _

local instance : LieModule ℚ (tropicalVertexLieAlgebra (R := S) d ρ) S[Q] :=
  LieModule.restrictScalars ℚ S _ _

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := S) d Q
local notation "ℒ" => (fun n => Submodule.restrictScalars ℚ (tropicalVertexGrading (R := R) d ρ n))
local notation "ℳ" => (fun n => Submodule.restrictScalars ℚ (tropicalVertexGrading (R := S) d ρ n))

local instance : IsFiltrationRaising d ℒ ((F).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := R) (F) d
    (tropicalVertexGrading (R := R) d ρ)

local instance : IsFiltrationRaising d ℳ ((G).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := S) (G) d
    (tropicalVertexGrading (R := S) d ρ)

/-- A monoid-local positive specialization intertwines completed BCH actions: the
specialized action of a label, such as a path product, is the action of the specialized
label on the specialized coefficient. -/
theorem coefficientMonoidPositiveSpecialization_completedBCHAction
    (g : d.completedBCHGroup ℒ) (a : (F).completion) :
    (coefficientMonoidPositiveSpecialization d Q φ χ f hf P P' hP).completionMap
        ((F).completedBCHAction (R := ℚ) d ℒ g a) =
      (G).completedBCHAction (R := ℚ) d ℳ
        ((coefficientMonoidGradedLieHom ρ φ Q χ d Fact.out).completedMap g)
        ((coefficientMonoidPositiveSpecialization d Q φ χ f hf P P' hP).completionMap a) := by
  simp only [coe_completionMap_coefficientMonoidPositiveSpecialization]
  exact mapCompletionₐ_coefficientMonoidGradedLieHom d ρ Q φ χ f hf g a

/-- If a label carries a coefficient to an element positive for `P`, then the specialized
label carries the specialized coefficient to an element positive for `P'`. -/
theorem isPositive_completedBCHAction_coefficientMonoidGradedLieHom
    {g : d.completedBCHGroup ℒ} {a : (F).completion}
    (h : (F).IsPositive P ((F).completedBCHAction (R := ℚ) d ℒ g a)) :
    (G).IsPositive P' ((G).completedBCHAction (R := ℚ) d ℳ
      ((coefficientMonoidGradedLieHom ρ φ Q χ d Fact.out).completedMap g)
      ((coefficientMonoidPositiveSpecialization d Q φ χ f hf P P' hP).completionMap a)) := by
  rw [← coefficientMonoidPositiveSpecialization_completedBCHAction]
  exact (coefficientMonoidPositiveSpecialization d Q φ χ f hf P P' hP).map_isPositive h

end Action

end Mei.LogarithmicVectorField

namespace Mei.TropicalPairing

open LogarithmicVectorField _root_.AddMonoidAlgebra

section Specialization

variable {K R S Γ Λ Γ' Λ' : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  {V : Submodule S (Λ →+ S)}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') V)
  (φ : R →ₐ[K] S) (χ : Multiplicative Q →* S)
  (hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q')
  (f : R[Q] →ₐ[K] S[Q])
  (hf : ∀ (q : Q) r, f (_root_.AddMonoidAlgebra.single q r) =
    _root_.AddMonoidAlgebra.single q (φ r * χ (.ofAdd q)))
  (P : Subsemiring R[Q]) (P' : Subsemiring S[Q'])

local notation "ψ" => AlgHom.comp (AlgHom.restrictScalars K (mapDomainAlgHom S S
  (AddMonoidHom.comp (AddSubmonoid.inclusion hT)
    (AddMonoidHom.addSubmonoidMap p.degreeMap.toAddMonoidHom Q)))) f

/-- A twisted coefficient change followed by the monomial map `z^q ↦ z^(T q)` of a tropical
pairing, mapping the chosen positive subsemirings into each other, is a positive
specialization of coefficient algebras with the cutoff modulus of `T`. -/
def coefficientPositiveSpecialization (hP : ∀ a ∈ P, ψ a ∈ P') :
    PositiveSpecialization (TropicalVertexCoefficientAction.filtration (R := R) d Q)
      (TropicalVertexCoefficientAction.filtration (R := S) e Q') P P' where
  toRingHom := ψ
  exists_modulus := ⟨p.degreeMap.modulus, p.degreeMap.monotone_modulus,
    filtration_ideal_le_comap_coefficientDegreeMap d Q φ χ f hf p.degreeMap hT⟩
  map_mem := hP

@[simp]
theorem coefficientPositiveSpecialization_toRingHom (hP : ∀ a ∈ P, ψ a ∈ P') :
    (p.coefficientPositiveSpecialization φ χ hT f hf P P' hP).toRingHom = ψ :=
  (rfl)

/-- The completion map of the specialization is the completed algebra map with the cutoff
modulus of the pairing. -/
theorem coe_completionMap_coefficientPositiveSpecialization (hP : ∀ a ∈ P, ψ a ∈ P') :
    ⇑(p.coefficientPositiveSpecialization φ χ hT f hf P P' hP).completionMap =
      (TropicalVertexCoefficientAction.filtration (R := R) d Q).mapCompletionₐ
        (TropicalVertexCoefficientAction.filtration (R := S) e Q') ψ p.degreeMap.modulus
        p.degreeMap.monotone_modulus
        (filtration_ideal_le_comap_coefficientDegreeMap d Q φ χ f hf p.degreeMap hT) := by
  rw [PositiveSpecialization.completionMap_eq_mapCompletion _ p.degreeMap.modulus
    p.degreeMap.monotone_modulus
    (filtration_ideal_le_comap_coefficientDegreeMap d Q φ χ f hf p.degreeMap hT)]
  exact congrArg DFunLike.coe (AlgFiltration.coe_mapCompletionₐ _ _ (ψ) _ _ _).symm

omit P P' in
include hf in
/-- If `φ` sends `ι(A)` into `ι'(A')` and every weight `χ(q)` lies in `ι'(A')`, the twisted
tropical coefficient map sends `ι(A)[Q]` into `ι'(A')[Q']`. -/
theorem map_mem_rangeS_mapRingHom_coefficientMap {A A' : Type*} [Semiring A] [Semiring A']
    (ι : A →+* R) (ι' : A' →+* S) (hφ : ∀ a, φ (ι a) ∈ ι'.rangeS)
    (hχ : ∀ q, χ q ∈ ι'.rangeS) {x : R[Q]} (hx : x ∈ (mapRingHom Q ι).rangeS) :
    ψ x ∈ (mapRingHom Q' ι').rangeS := by
  refine AddMonoidAlgebra.map_mem_rangeS_mapRingHom ι ι' (ψ).toAddMonoidHom
    (fun q a => ?_) hx
  obtain ⟨c, hc⟩ := ι'.rangeS.mul_mem (hφ a) (hχ (.ofAdd q))
  refine ⟨single (AddSubmonoid.inclusion hT
    (p.degreeMap.toAddMonoidHom.addSubmonoidMap Q q)) c, ?_⟩
  simp [hf, hc]

end Specialization

section Action

open scoped TropicalVertexCoefficientAction

variable {R S : Type u} {Γ Γ' : Type v} {Λ Λ' : Type w}
  [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [AddCommMonoid Γ] [AddCommMonoid Γ'] [AddCommMonoid Λ] [AddCommMonoid Λ']
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  {U : Submodule R (Λ →+ R)} {V : Submodule S (Λ →+ S)}
  [Fact (d.monoid ≤ Q)] [Fact (e.monoid ≤ Q')]
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') V)
  (φ : R →ₐ[ℚ] S) (χ : Multiplicative Q →* S)
  (hφ : ∀ m : U, (φ : R →+ S).comp m.val ∈ V)
  (hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q')
  (f : R[Q] →ₐ[ℚ] S[Q])
  (hf : ∀ (q : Q) r, f (_root_.AddMonoidAlgebra.single q r) =
    _root_.AddMonoidAlgebra.single q (φ r * χ (.ofAdd q)))
  {P : Subsemiring R[Q]} {P' : Subsemiring S[Q']}

local instance : LieModule ℚ (tropicalSubalgebra ρ U d) R[Q] :=
  LieModule.restrictScalars ℚ R _ _

local instance : LieModule ℚ (tropicalVertexLieAlgebra (R := S) e ρ') S[Q'] :=
  LieModule.restrictScalars ℚ S _ _

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := S) e Q'
local notation "ℒ" => (fun n => Submodule.restrictScalars ℚ (tropicalSubalgebraGrading ρ U d n))
local notation "ℳ" => (fun n => Submodule.restrictScalars ℚ (tropicalVertexGrading (R := S) e ρ' n))
local notation "ψ" => AlgHom.comp (AlgHom.restrictScalars ℚ (mapDomainAlgHom S S
  (AddMonoidHom.comp (AddSubmonoid.inclusion hT)
    (AddMonoidHom.addSubmonoidMap p.degreeMap.toAddMonoidHom Q)))) f

local instance : IsFiltrationRaising d ℒ ((F).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := R) (F) d
    (tropicalSubalgebraGrading ρ U d)

local instance : IsFiltrationRaising e ℳ ((G).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := S) (G) e
    (tropicalVertexGrading (R := S) e ρ')

/-- A positive specialization along a twisted tropical coefficient map intertwines
completed BCH actions: the specialized action of a label, such as a path product, is the
action of the transported label on the specialized coefficient. The pairing identity is
required on all coefficient exponents. -/
theorem coefficientPositiveSpecialization_completedBCHAction (hP : ∀ a ∈ P, ψ a ∈ P')
    (heval : ∀ (m : V) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    (g : d.completedBCHGroup ℒ) (a : (F).completion) :
    (p.coefficientPositiveSpecialization φ χ hT f hf P P' hP).completionMap
        ((F).completedBCHAction (R := ℚ) d ℒ g a) =
      (G).completedBCHAction (R := ℚ) e ℳ
        ((p.coefficientGradedLieHom φ χ Fact.out hφ).completedMap g)
        ((p.coefficientPositiveSpecialization φ χ hT f hf P P' hP).completionMap a) := by
  simp only [coe_completionMap_coefficientPositiveSpecialization]
  exact p.mapCompletionₐ_coefficientGradedLieHom φ χ hφ hT f hf heval g a

/-- If a label carries a coefficient to an element positive for `P`, then the transported
label carries the specialized coefficient to an element positive for `P'`. -/
theorem isPositive_completedBCHAction_coefficientGradedLieHom (hP : ∀ a ∈ P, ψ a ∈ P')
    (heval : ∀ (m : V) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    {g : d.completedBCHGroup ℒ} {a : (F).completion}
    (h : (F).IsPositive P ((F).completedBCHAction (R := ℚ) d ℒ g a)) :
    (G).IsPositive P' ((G).completedBCHAction (R := ℚ) e ℳ
      ((p.coefficientGradedLieHom φ χ Fact.out hφ).completedMap g)
      ((p.coefficientPositiveSpecialization φ χ hT f hf P P' hP).completionMap a)) := by
  rw [← p.coefficientPositiveSpecialization_completedBCHAction φ χ hφ hT f hf hP heval]
  exact (p.coefficientPositiveSpecialization φ χ hT f hf P P' hP).map_isPositive h

end Action

end Mei.TropicalPairing
