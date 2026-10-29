/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Coefficient
public import Mei.Algebra.Lie.Filtered.Intertwiner.Algebra

/-!
# Represented algebra intertwiners for tropical pairings

A tropical pairing and its monomial coefficient map give an algebra-valued
`ActionIntertwiner`. The labels are the finite BCH maps of the pairing and the
coefficient components send `z^q` to `z^(T q)` on quotient algebras. Thus the
section-limit comparison and completed-label equivariance apply to tropical
coefficient algebras, including coefficient monoids larger than the positive monoid.

This uses `TropicalPairing.gradedLieHom`, its coefficient-action equivariance and
`AlgFiltration.bchActionIntertwiner`. The pairing follows Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i)
(arXiv:1503.06183v5).
-/

public noncomputable section

open CategoryTheory

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
  (heval : ∀ (m : U) {q : Γ}, q ∈ Q →
    p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) e Q'
local notation "ψ" => mapDomainAlgHom R R
  (AddMonoidHom.comp (AddSubmonoid.inclusion hT)
    (AddMonoidHom.addSubmonoidMap p.degreeMap.toAddMonoidHom Q))
local notation "hψ" => fun k =>
  TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom p.degreeMap hT k

/-- A tropical pairing represents its coefficient maps as an algebra-valued
intertwiner, with the original cutoff modulus. -/
def bchActionIntertwiner :
    ActionIntertwiner
      (⟨p.degreeMap.modulus, p.degreeMap.monotone_modulus⟩ : ℕ →o ℕ).toFunctor.op
      ((F).bchRepresentation d (tropicalSubalgebraGrading ρ U d))
      ((G).bchRepresentation e (tropicalVertexGrading (R := R) e ρ')) :=
  (F).bchActionIntertwiner d (tropicalSubalgebraGrading ρ U d)
    G p.gradedLieHom ψ p.degreeMap.modulus p.degreeMap.monotone_modulus
    (fun _ => le_rfl) hψ
    (fun x a => p.mapDomainAlgHom_tropicalVertexCoefficientAction
      Fact.out Fact.out hT heval x a)

/-- The represented coefficient map is the monomial map on the corresponding
quotient algebras. -/
@[simp]
theorem bchActionIntertwiner_coefficient_app
    (a : Grothendieck
      ((⟨p.degreeMap.modulus, p.degreeMap.monotone_modulus⟩ : ℕ →o ℕ).toFunctor.op ⋙
        (d.groupTower (tropicalSubalgebraGrading ρ U d) ⋙
          forget₂ GrpCat MonCat ⋙ MonCat.toCat))) :
    (p.bchActionIntertwiner hT heval).coefficient.app a =
      AlgCat.ofHom (Ideal.quotientMapₐ ((G).ideal (a.base.unop + 1)) ψ (hψ a.base.unop)) :=
  (F).bchActionIntertwiner_coefficient_app d (tropicalSubalgebraGrading ρ U d)
    G p.gradedLieHom ψ p.degreeMap.modulus p.degreeMap.monotone_modulus
    (fun _ => le_rfl) hψ
    (fun x a => p.mapDomainAlgHom_tropicalVertexCoefficientAction
      Fact.out Fact.out hT heval x a) a

/-- The represented label map is the pairing's BCH homomorphism on the
corresponding finite Lie quotients. -/
@[simp]
theorem bchActionIntertwiner_labelMap_map (k : ℕᵒᵖ)
    (g : BCHGroup (d.truncatedLie (tropicalSubalgebraGrading ρ U d)
      (p.degreeMap.modulus k.unop))) :
    (((p.bchActionIntertwiner hT heval).labelMap.app k).toFunctor.map
      (X := SingleObj.star (BCHGroup (d.truncatedLie (tropicalSubalgebraGrading ρ U d)
        (p.degreeMap.modulus k.unop))))
      (Y := SingleObj.star (BCHGroup (d.truncatedLie (tropicalSubalgebraGrading ρ U d)
        (p.degreeMap.modulus k.unop)))) g) =
      (p.gradedLieHom.truncatedMap k.unop le_rfl).bchGroupMap g :=
  (F).bchActionIntertwiner_labelMap_map d (tropicalSubalgebraGrading ρ U d)
    G p.gradedLieHom ψ p.degreeMap.modulus p.degreeMap.monotone_modulus
    (fun _ => le_rfl) hψ
    (fun x a => p.mapDomainAlgHom_tropicalVertexCoefficientAction
      Fact.out Fact.out hT heval x a) k g

end Mei.TropicalPairing
