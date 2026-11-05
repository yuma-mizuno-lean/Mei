/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Completion

/-!
# Tropical pairings on the full tropical vertex Lie algebra

A tropical pairing whose character domain is the whole character space is defined on the
character restriction `tropicalSubalgebra ρ ⊤ d`, which is all of the positive tangent Lie
algebra `tropicalVertexLieAlgebra d ρ`. Composing with this identification gives a graded Lie
map between the tropical vertex Lie algebras themselves, over the degree map of the pairing.
On a homogeneous field `z^n ∂_m` it gives `z^{T n} ∂_{S m}`. Directed walls labelled in
`tropicalVertexWallSpaces` take their labels in these algebras.

When the evaluation identity of the pairing also holds on the exponents of coefficient monoids
`Q` and `Q'` with `T(Q) ⊆ Q'`, the monomial map `z^q ↦ z^{T q}` on completed coefficients
intertwines the completed BCH actions of the two full tropical vertex Lie algebras along this
map (`TropicalPairing.mapCompletionₐ_completedBCHAction_tropicalVertexGradedLieHom`). This is
`TropicalPairing.mapCompletionₐ_completedBCHAction` for the full algebras.

The pairing and the logarithmic bracket follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

namespace LogarithmicVectorField

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)

/-- Every positive tangent field has its characters in the full character space. -/
theorem mem_tropicalSubalgebra_top (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    x ∈ tropicalSubalgebra ρ (⊤ : Submodule R (Λ →+ R)) d := by
  simp

/-- The positive tangent Lie algebra, viewed in its restriction to all characters. -/
def toTropicalSubalgebraTop :
    tropicalVertexLieAlgebra (R := R) d ρ →ₗ⁅R⁆
      tropicalSubalgebra ρ (⊤ : Submodule R (Λ →+ R)) d :=
  { LinearMap.id.codRestrict (tropicalSubalgebra ρ (⊤ : Submodule R (Λ →+ R)) d).toSubmodule
      (mem_tropicalSubalgebra_top d ρ) with
    map_lie' := fun {_ _} => Subtype.ext (by simp) }

/-- The identification does not change the underlying field. -/
@[simp]
theorem coe_toTropicalSubalgebraTop (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    (toTropicalSubalgebraTop d ρ x).val = x := (rfl)

end LogarithmicVectorField

namespace TropicalPairing

open LogarithmicVectorField

variable {R Γ Λ Γ' Λ' : Type*} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') (⊤ : Submodule R (Λ →+ R)))

/-- A pairing on all characters as a graded Lie map between the tropical vertex Lie
algebras, over its degree map. -/
def tropicalVertexGradedLieHom :
    GradedLieHom p.degreeMap (tropicalVertexGrading (R := R) d ρ) (tropicalVertexGrading e ρ')
    where
  toLieHom := p.gradedLieHom.toLieHom.comp (toTropicalSubalgebraTop d ρ)
  map_mem {n x} hx := p.gradedLieHom.map_mem (n := n) (x := toTropicalSubalgebraTop d ρ x) (by
    rw [tropicalSubalgebraGrading_def, Submodule.mem_comap]
    exact hx)

/-- The map on the full algebra is the pairing map on the restriction to all characters. -/
theorem tropicalVertexGradedLieHom_apply (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    p.tropicalVertexGradedLieHom x = p.gradedLieHom (toTropicalSubalgebraTop d ρ x) := (rfl)

/-- On a homogeneous field `z^n ∂_m`, the pairing gives `z^{T n} ∂_{S m}`. -/
theorem coe_tropicalVertexGradedLieHom_of_homogeneous {n : Γ}
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (m : Λ →+ R) (hm : single ρ n m = x.val) :
    (p.tropicalVertexGradedLieHom x).val =
      single ρ' (p.degreeMap n) (p.characterMap ⟨m, Submodule.mem_top⟩) :=
  p.coe_gradedLieHom_of_homogeneous _ ⟨m, Submodule.mem_top⟩ hm

end TropicalPairing

namespace TropicalPairing

open LogarithmicVectorField _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

universe v w

variable {R : Type*} [CommRing R] [Algebra ℚ R]
  {Γ Γ' : Type v} {Λ Λ' : Type w} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [AddCommMonoid Γ'] [AddCommMonoid Λ'] [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') (⊤ : Submodule R (Λ →+ R)))
  {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'} [Fact (d.monoid ≤ Q)] [Fact (e.monoid ≤ Q')]
  (hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q')

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) e Q'
local notation "ψ" => mapDomainAlgHom R R
  (AddMonoidHom.comp (AddSubmonoid.inclusion hT)
    (AddMonoidHom.addSubmonoidMap p.degreeMap.toAddMonoidHom Q))
local notation "hψ" => fun k =>
  TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom p.degreeMap hT k

/-- A pairing on all characters intertwines the completed BCH actions of the full tropical
vertex Lie algebras with the monomial map `z^q ↦ z^{T q}` of completed coefficients, provided
its evaluation identity `S(m)(ρ'(T q)) = m(ρ q)` holds on every exponent `q ∈ Q`. -/
theorem mapCompletionₐ_completedBCHAction_tropicalVertexGradedLieHom
    (heval : ∀ (m : (⊤ : Submodule R (Λ →+ R))) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    (g : d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)) (a : (F).completion) :
    (F).mapCompletionₐ G ψ p.degreeMap.modulus p.degreeMap.monotone_modulus hψ
        ((F).completedBCHAction (R := R) d (tropicalVertexGrading (R := R) d ρ) g a) =
      (G).completedBCHAction (R := R) e (tropicalVertexGrading (R := R) e ρ')
        (p.tropicalVertexGradedLieHom.completedMap g)
        ((F).mapCompletionₐ G ψ p.degreeMap.modulus p.degreeMap.monotone_modulus hψ a) := by
  apply (F).mapCompletionₐ_completedBCHAction_of_gradedLieHom G p.tropicalVertexGradedLieHom ψ
  intro x a
  rw [TropicalVertexCoefficientAction.lie_eq, TropicalVertexCoefficientAction.lie_eq,
    tropicalVertexGradedLieHom_apply]
  exact p.mapDomainAlgHom_tropicalVertexCoefficientAction Fact.out Fact.out hT heval
    (toTropicalSubalgebraTop d ρ x) a

end TropicalPairing

end Mei
