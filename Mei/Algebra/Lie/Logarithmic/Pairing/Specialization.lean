/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.MonoidSpecialization
public import Mei.Algebra.Lie.Logarithmic.Pairing.Coefficient

/-!
# Twisted coefficient change along tropical pairings

First specialize coefficients and monoid-local weights, then transport degrees
and characters along a tropical pairing. The weights are applied before degrees
are merged, so they need not descend through the degree map. They may vanish.
Only the specified character subspaces are used, and the pairing's cutoff
modulus controls the completed coefficient map and completed BCH action.

The construction combines `coefficientMonoidGradedLieHom` with
`TropicalPairing.gradedLieHom`. The coefficient algebra map is the composite of a
monoid-local specialization and Mathlib's `AddMonoidAlgebra.mapDomainAlgHom`.
These twisted tropical maps follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section
noncomputable section

namespace Mei.TropicalPairing

open LogarithmicVectorField _root_.AddMonoidAlgebra

variable {K R S Γ Λ Γ' Λ' : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ] [AddCommMonoid Λ]
  [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {Q : AddSubmonoid Γ} {Q' : AddSubmonoid Γ'}
  {U : Submodule R (Λ →+ R)} {V : Submodule S (Λ →+ S)}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') V)
  (φ : R →ₐ[K] S) (χ : Multiplicative Q →* S) (hQ : d.monoid ≤ Q)
  (hφ : ∀ m : U, (φ : R →+ S).comp m.val ∈ V)

/-- Twisted coefficient and degree transport on selected character subalgebras.
The degree map and cutoff modulus are exactly those of the tropical pairing. -/
def coefficientGradedLieHom :
    GradedLieHom (R := K) (L := tropicalSubalgebra ρ U d)
      (L' := tropicalVertexLieAlgebra (R := S) e ρ') p.degreeMap
      (fun n => (tropicalSubalgebraGrading ρ U d n).restrictScalars K)
      (fun n => (tropicalVertexGrading (R := S) e ρ' n).restrictScalars K) where
  toLieHom := ((p.gradedLieHom.restrictScalars K).comp
    (restrictCoefficientMonoidGradedLieHom φ χ hQ hφ)).toLieHom
  map_mem hx := by
    simpa only [PositiveDegreeMap.comp_id] using
      ((p.gradedLieHom.restrictScalars K).comp
        (restrictCoefficientMonoidGradedLieHom φ χ hQ hφ)).map_mem hx

/-- Coefficient transport is specialization followed by the pairing map. -/
theorem coefficientGradedLieHom_apply (x : tropicalSubalgebra ρ U d) :
    p.coefficientGradedLieHom φ χ hQ hφ x =
      p.gradedLieHom (restrictCoefficientMonoidGradedLieHom φ χ hQ hφ x) := by
  simp only [← GradedLieHom.coe_toLieHom, coefficientGradedLieHom,
    GradedLieHom.toLieHom_comp, GradedLieHom.toLieHom_restrictScalars,
    LieHom.comp_apply, LieHom.restrictScalars_apply]

/-- A homogeneous field acquires its source weight before its degree and
coefficient-changed character are transported. Distinct source degrees may merge. -/
theorem coe_coefficientGradedLieHom_of_homogeneous {n : Γ} (hn : n ∈ d.monoid)
    (x : tropicalSubalgebra ρ U d) (m : U) (hm : single ρ n m.val = x.val.val) :
    (p.coefficientGradedLieHom φ χ hQ hφ x).val =
      single ρ' (p.degreeMap n)
        (χ (.ofAdd ⟨n, hQ hn⟩) • p.characterMap ⟨(φ : R →+ S).comp m.val, hφ m⟩) := by
  rw [coefficientGradedLieHom_apply]
  let m' : V := ⟨(φ : R →+ S).comp m.val, hφ m⟩
  have hs := coe_coefficientMonoidGradedLieHom_of_homogeneous ρ φ Q χ d hQ hn x.val m.val hm
  have ht := p.coe_gradedLieHom_of_homogeneous
    (restrictCoefficientMonoidGradedLieHom φ χ hQ hφ x)
    (χ (.ofAdd ⟨n, hQ hn⟩) • m') (by
      simpa only [Submodule.coe_smul, coe_restrictCoefficientMonoidGradedLieHom, m'] using hs.symm)
  exact ht.trans (congrArg (single ρ' (p.degreeMap n)) (p.characterMap.map_smul _ m'))

/-- The twisted pairing formula on a positive tangent generator. -/
@[simp]
theorem coe_coefficientGradedLieHom_tropicalSingle {n : Γ}
    (hn : n ∈ d.monoid) (hne : n ≠ 0) (m : U) (hm : m.val (ρ n) = 0) :
    (p.coefficientGradedLieHom φ χ hQ hφ (tropicalSingle d ρ U hn hne m hm)).val =
      single ρ' (p.degreeMap n)
        (χ (.ofAdd ⟨n, hQ hn⟩) • p.characterMap ⟨(φ : R →+ S).comp m.val, hφ m⟩) :=
  p.coe_coefficientGradedLieHom_of_homogeneous φ χ hQ hφ hn _ m
    (coe_tropicalSingle d ρ U hn hne m hm).symm

variable (hQ' : e.monoid ≤ Q') (hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q')
  (f : R[Q] →ₐ[K] S[Q])
  (hf : ∀ (q : Q) r, f (_root_.AddMonoidAlgebra.single q r) =
    _root_.AddMonoidAlgebra.single q (φ r * χ (.ofAdd q)))

local notation "ψ" => AlgHom.restrictScalars K (mapDomainAlgHom S S
  (AddMonoidHom.comp (AddSubmonoid.inclusion hT)
    (AddMonoidHom.addSubmonoidMap p.degreeMap.toAddMonoidHom Q)))

include hf in
/-- The composite coefficient map `ψ ∘ f` intertwines the tropical vertex coefficient
actions along `coefficientGradedLieHom`, provided `Q` maps into `Q'` and the pairing
identity holds on all of `Q`. -/
theorem map_coefficientAction
    (heval : ∀ (m : V) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    (x : tropicalSubalgebra ρ U d) (a : R[Q]) :
    (AlgHom.comp ψ f) (tropicalVertexCoefficientAction d ρ Q hQ x.val a) =
      tropicalVertexCoefficientAction e ρ' Q' hQ'
        (p.coefficientGradedLieHom φ χ hQ hφ x) ((AlgHom.comp ψ f) a) := by
  rw [AlgHom.comp_apply, LogarithmicVectorField.map_coefficientAction ρ φ Q χ d hQ f hf]
  simpa only [AlgHom.restrictScalars_apply, AlgHom.comp_apply,
    coefficientGradedLieHom_apply, coe_restrictCoefficientMonoidGradedLieHom] using
    p.mapDomainAlgHom_tropicalVertexCoefficientAction hQ hQ' hT heval
      (restrictCoefficientMonoidGradedLieHom φ χ hQ hφ x) (f a)

end Mei.TropicalPairing

namespace Mei.TropicalPairing

open LogarithmicVectorField _root_.AddMonoidAlgebra
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
local notation "hmap" => filtration_ideal_le_comap_coefficientDegreeMap d Q φ χ f hf
  p.degreeMap hT

local instance : IsFiltrationRaising d ℒ ((F).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := R) (F) d
    (tropicalSubalgebraGrading ρ U d)

local instance : IsFiltrationRaising e ℳ ((G).toModuleFiltration ℚ) :=
  IsFiltrationRaising.restrictScalars_algebra (R := ℚ) (S := S) (G) e
    (tropicalVertexGrading (R := S) e ρ')

/-- Twisted tropical coefficient maps intertwine completed BCH actions with the
pairing's cutoff modulus. Labels use the common rational scalar ring; coefficients
and weights may be killed and distinct degrees may have the same image. -/
theorem mapCompletionₐ_coefficientGradedLieHom
    (heval : ∀ (m : V) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    (g : d.completedBCHGroup ℒ) (a : (F).completion) :
    (F).mapCompletionₐ G ψ p.degreeMap.modulus p.degreeMap.monotone_modulus hmap
        ((F).completedBCHAction (R := ℚ) d ℒ g a) =
      (G).completedBCHAction (R := ℚ) e ℳ
        ((p.coefficientGradedLieHom φ χ Fact.out hφ).completedMap g)
        ((F).mapCompletionₐ G ψ p.degreeMap.modulus p.degreeMap.monotone_modulus hmap a) := by
  apply (F).mapCompletionₐ_completedBCHAction_of_gradedLieHom G
    (p.coefficientGradedLieHom φ χ Fact.out hφ) ψ
  intro x b
  exact p.map_coefficientAction φ χ Fact.out hφ Fact.out hT f hf heval x b

end Mei.TropicalPairing
