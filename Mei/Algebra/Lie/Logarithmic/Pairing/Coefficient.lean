/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.Algebra.Lie.Logarithmic.Pairing.Basic

/-!
# Tropical pairings and coefficient actions

A tropical pairing `(T, S)` intertwines the tropical vertex actions on coefficient
algebras with the monomial map `z^q ↦ z^(T q)`, provided its evaluation identity also
holds on the coefficient exponents; on the positive coefficient algebras this is automatic.
Combined with `TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom`,
the monomial map extends to completed coefficient algebras with the cutoff modulus of `T`.

The coefficient action and pairing condition follow Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (Q : AddSubmonoid Γ)

namespace TropicalPairing

open LogarithmicVectorField

variable {Γ' Λ' : Type*} [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d ρ Q} {e : PositiveDegrees Γ'} {ρ' : Γ' →+ Λ'} {Q' : AddSubmonoid Γ'}
  {U : Submodule R (Λ →+ R)} (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U)

/-- A tropical pairing intertwines the coefficient actions with the monomial map
`z^q ↦ z^(T q)`, whenever the pairing identity also holds on the coefficient exponents.
Taking `Q = P` and `Q' = P'`, this hypothesis is the defining identity of the pairing;
see `mapDomainAlgHom_tropicalVertexCoefficientAction_monoid`. -/
theorem mapDomainAlgHom_tropicalVertexCoefficientAction (hQ : d.monoid ≤ Q)
    (hQ' : e.monoid ≤ Q') (hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q')
    (heval : ∀ (m : U) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    (x : tropicalSubalgebra ρ U d) (a : R[Q]) :
    mapDomainAlgHom R R
        ((AddSubmonoid.inclusion hT).comp (p.degreeMap.toAddMonoidHom.addSubmonoidMap Q))
        (tropicalVertexCoefficientAction d ρ Q hQ x a) =
      tropicalVertexCoefficientAction e ρ' Q' hQ' (p.gradedLieHom x)
        (mapDomainAlgHom R R
          ((AddSubmonoid.inclusion hT).comp (p.degreeMap.toAddMonoidHom.addSubmonoidMap Q)) a) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn (tropicalSubalgebraGrading ρ U d) with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ d.monoid
    · obtain ⟨m, hm⟩ := (mem_tropicalSubalgebraGrading_iff d ρ U n x).mp x.property
      rw [tropicalVertexCoefficientAction_of_homogeneous d ρ Q hQ hn _ m.val hm,
        tropicalVertexCoefficientAction_of_homogeneous e ρ' Q' hQ' (p.degreeMap.map_mem hn) _
          (p.characterMap m) (p.coe_gradedLieHom_of_homogeneous x m hm).symm]
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single q r =>
        simp only [mapDomainAlgHom_apply, mapDomain_single,
          AddMonoidAlgebra.monomialDerivation_single, AddMonoidHom.comp_apply,
          AddSubmonoid.subtype_apply, map_add]
        congr 1
        simp [heval m q.2]
    · have hx : (x : tropicalSubalgebra ρ U d) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d)
          (ℒ := tropicalSubalgebraGrading ρ U d) n (Or.inl hn), Submodule.mem_bot]
          using x.property
      simp [hx]
  | add x y hx hy =>
    simp only [AddMemClass.coe_add, map_add, Derivation.add_apply]
    rw [hx, hy]

/-- On the positive coefficient algebras, a tropical pairing intertwines the
coefficient actions with the monomial map `z^p ↦ z^(T p)` without further hypotheses. -/
theorem mapDomainAlgHom_tropicalVertexCoefficientAction_monoid
    (x : tropicalSubalgebra ρ U d) (a : R[d.monoid]) :
    mapDomainAlgHom R R ((AddSubmonoid.inclusion p.degreeMap.map_monoid_le).comp
        (p.degreeMap.toAddMonoidHom.addSubmonoidMap d.monoid))
        (tropicalVertexCoefficientAction d ρ d.monoid le_rfl x a) =
      tropicalVertexCoefficientAction e ρ' e.monoid le_rfl (p.gradedLieHom x)
        (mapDomainAlgHom R R ((AddSubmonoid.inclusion p.degreeMap.map_monoid_le).comp
          (p.degreeMap.toAddMonoidHom.addSubmonoidMap d.monoid)) a) :=
  p.mapDomainAlgHom_tropicalVertexCoefficientAction le_rfl le_rfl p.degreeMap.map_monoid_le
    (fun m _ hq => p.eval_eq m hq) x a

end TropicalPairing

end Mei
