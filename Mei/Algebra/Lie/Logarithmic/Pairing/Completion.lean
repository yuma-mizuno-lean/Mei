/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Coefficient
public import Mei.Algebra.Lie.Filtered.Map

/-!
# Tropical pairings intertwine completed coefficient actions

A tropical pairing transports completed BCH labels and intertwines their actions
on completed coefficient algebras via the monomial map `z^q ↦ z^(T q)`.
The character domain may be a proper subspace. The coefficient monoids need only
contain the positive monoids, and the evaluation identity is required on the
source coefficient monoid. On the positive monoid it is the pairing axiom itself.

The action on the character-domain subalgebra is Mathlib's inherited Lie action.
We use `TropicalPairing.mapDomainAlgHom_tropicalVertexCoefficientAction`, the
positive-increment filtration bound, and
`AlgFiltration.mapCompletionₐ_completedBCHAction_of_gradedLieHom`.
The pairing follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.TropicalPairing

open LogarithmicVectorField _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

variable {R : Type*} [CommRing R] [Algebra ℚ R]
  {Γ Γ' : Type v} {Λ Λ' : Type w} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [AddCommMonoid Γ'] [AddCommMonoid Λ'] [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {U : Submodule R (Λ →+ R)}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U)
  {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  [Fact (d.monoid ≤ Q)] [Fact (e.monoid ≤ Q')]
  (hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q')

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) e Q'
local notation "ψ" => mapDomainAlgHom R R
  (AddMonoidHom.comp (AddSubmonoid.inclusion hT)
    (AddMonoidHom.addSubmonoidMap p.degreeMap.toAddMonoidHom Q))
local notation "hψ" => fun k =>
  TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom p.degreeMap hT k

/-- A tropical pairing intertwines its completed BCH action on any coefficient
monoids where its character-evaluation identity holds. This includes noninjective
degree maps, arbitrary cutoff moduli and arbitrary completed coefficients. -/
theorem mapCompletionₐ_completedBCHAction
    (heval : ∀ (m : U) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    (g : d.completedBCHGroup (tropicalSubalgebraGrading ρ U d)) (a : (F).completion) :
    (F).mapCompletionₐ G ψ p.degreeMap.modulus p.degreeMap.monotone_modulus hψ
        ((F).completedBCHAction (R := R) d (tropicalSubalgebraGrading ρ U d) g a) =
      (G).completedBCHAction (R := R) e (tropicalVertexGrading (R := R) e ρ')
        (p.gradedLieHom.completedMap g)
        ((F).mapCompletionₐ G ψ p.degreeMap.modulus p.degreeMap.monotone_modulus hψ a) := by
  apply (F).mapCompletionₐ_completedBCHAction_of_gradedLieHom G p.gradedLieHom ψ
  intro x a
  exact p.mapDomainAlgHom_tropicalVertexCoefficientAction Fact.out Fact.out hT heval x a

end Mei.TropicalPairing
