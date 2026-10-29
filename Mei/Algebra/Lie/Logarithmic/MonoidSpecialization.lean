/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Specialization
public import Mei.Algebra.Lie.Filtered.Map
public import Mei.Algebra.Lie.Filtered.RestrictScalars

/-!
# Completed coefficient-monoid specialization

A twisted coefficient map on a monoid algebra preserves the positive-increment
filtration, even when a monomial weight vanishes. It therefore extends to the
completion and intertwines the completed tropical vertex actions. The weights
need only be defined on the coefficient monoid, which permits polynomial
specializations unavailable on the ambient Laurent algebra. Combining the map
with positive degree transport retains the degree map's cutoff modulus.

We use `LogarithmicVectorField.coefficientMonoidGradedLieHom` and
`AlgFiltration.mapCompletionₐ_completedBCHAction_of_gradedLieHom`, restricting
both coefficient Lie algebras to rational scalars. The coefficient maps are
specified by their monomial formula; Mathlib's `AddMonoidAlgebra.liftNCAlgHom`
constructs them. Twisted coefficient changes follow Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

namespace Mei.LogarithmicVectorField

open _root_.AddMonoidAlgebra

variable {K R S Γ : Type*} [CommSemiring K] [CommSemiring R] [CommSemiring S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ]
  (d : PositiveDegrees Γ) (Q : AddSubmonoid Γ)
  (φ : R →ₐ[K] S) (χ : Multiplicative Q →* S)
  (f : R[Q] →ₐ[K] S[Q])
  (hf : ∀ (p : Q) r, f (_root_.AddMonoidAlgebra.single p r) =
    _root_.AddMonoidAlgebra.single p (φ r * χ (.ofAdd p)))

include hf

/-- Twisted coefficient-monoid maps preserve each positive-increment ideal.
No injectivity or invertibility of the monomial weights is needed. -/
theorem filtration_ideal_le_comap_coefficientMonoidMap (k : ℕ) :
    (TropicalVertexCoefficientAction.filtration (R := R) d Q).ideal k ≤
      ((TropicalVertexCoefficientAction.filtration (R := S) d Q).ideal k).comap f := by
  rw [TropicalVertexCoefficientAction.filtration_ideal,
    TropicalVertexCoefficientAction.filtration_ideal,
    AddSubmonoid.monoidAlgebraIdeal_le_iff]
  intro n hn hd
  simp only [Ideal.mem_comap, of'_apply, hf, map_one, one_mul,
    AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  exact Or.inr ⟨n, hn, hd, 0, by simp⟩

/-- Combining a monoid-local coefficient specialization with a positive degree
map preserves the coefficient filtration with that degree map's cutoff modulus. -/
theorem filtration_ideal_le_comap_coefficientDegreeMap
    {Γ' : Type*} [AddCommMonoid Γ'] {e : PositiveDegrees Γ'} {Q' : AddSubmonoid Γ'}
    (T : PositiveDegreeMap d e) (hT : Q.map T.toAddMonoidHom ≤ Q') (k : ℕ) :
    (TropicalVertexCoefficientAction.filtration (R := R) d Q).ideal (T.modulus k + 1) ≤
      ((TropicalVertexCoefficientAction.filtration (R := S) e Q').ideal (k + 1)).comap
        ((mapDomainAlgHom S S
          ((AddSubmonoid.inclusion hT).comp (T.toAddMonoidHom.addSubmonoidMap Q))).restrictScalars K
          |>.comp f) := by
  intro a ha
  exact TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom T hT k
    (filtration_ideal_le_comap_coefficientMonoidMap d Q φ χ f hf _ ha)

end Mei.LogarithmicVectorField

noncomputable section

namespace Mei.LogarithmicVectorField

open _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

variable {R S : Type u} {Γ : Type v} {Λ : Type w}
  [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (Q : AddSubmonoid Γ)
  [Fact (d.monoid ≤ Q)] (φ : R →ₐ[ℚ] S) (χ : Multiplicative Q →* S)
  (f : R[Q] →ₐ[ℚ] S[Q])
  (hf : ∀ (p : Q) r, f (_root_.AddMonoidAlgebra.single p r) =
    _root_.AddMonoidAlgebra.single p (φ r * χ (.ofAdd p)))

local instance : LieModule ℚ (tropicalVertexLieAlgebra (R := R) d ρ) R[Q] :=
  LieModule.restrictScalars ℚ R _ _

local instance : LieModule ℚ (tropicalVertexLieAlgebra (R := S) d ρ) S[Q] :=
  LieModule.restrictScalars ℚ S _ _

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := S) d Q
local notation "ℒ" => (fun n => Submodule.restrictScalars ℚ (tropicalVertexGrading (R := R) d ρ n))
local notation "ℳ" => (fun n => Submodule.restrictScalars ℚ (tropicalVertexGrading (R := S) d ρ n))
local notation "hmap" => fun k =>
  filtration_ideal_le_comap_coefficientMonoidMap d Q φ χ f hf (k + 1)

local instance : IsFiltrationRaising d ℒ ((F).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := R) (F) d
    (tropicalVertexGrading (R := R) d ρ)

local instance : IsFiltrationRaising d ℳ ((G).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := S) (G) d
    (tropicalVertexGrading (R := S) d ρ)

/-- Monoid-local twisted coefficient change intertwines completed BCH actions on
arbitrary completed coefficients, using the identity cutoff modulus. The group
labels are viewed over the common rational scalar ring. -/
theorem mapCompletionₐ_coefficientMonoidGradedLieHom
    (g : d.completedBCHGroup ℒ) (a : (F).completion) :
    (F).mapCompletionₐ G f id monotone_id hmap
        ((F).completedBCHAction (R := ℚ) d ℒ g a) =
      (G).completedBCHAction (R := ℚ) d ℳ
        ((coefficientMonoidGradedLieHom ρ φ Q χ d Fact.out).completedMap g)
        ((F).mapCompletionₐ G f id monotone_id hmap a) := by
  apply (F).mapCompletionₐ_completedBCHAction_of_gradedLieHom G
    (coefficientMonoidGradedLieHom ρ φ Q χ d Fact.out) f
  intro x b
  exact map_coefficientAction ρ φ Q χ d Fact.out f hf x b

end Mei.LogarithmicVectorField
