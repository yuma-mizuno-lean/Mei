/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit.Product
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit

public import Mei.Algebra.Group.Hom.Algebra

/-!
# Global completed BCH algebra actions

If the original unit has degree zero, the global linear action of each completed
BCH label is an algebra automorphism. Product preservation is supplied by the
nonunital result; the unit law follows from invertibility of that multiplicative map.

The shifted coefficient setting is motivated by Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §2.1 and Definition 2.10
([arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5)).
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)
noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ R L A : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [Ring A] [Algebra R A] [LieRingModule L A] [LieModule R L A]
  [IsDerivationAction L A] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (𝒜 : Γ → Submodule R A)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition 𝒜] [SetLike.GradedBracket ℒ 𝒜]
  [SetLike.GradedMonoid 𝒜]

/-- Completed BCH labels act on global coefficients by algebra automorphisms. -/
def shiftedDirectLimitBCHAlgAction : d.completedBCHGroup ℒ →*
    (d.ShiftedDirectLimit 𝒜 ≃ₐ[R] d.ShiftedDirectLimit 𝒜) :=
  (d.shiftedDirectLimitBCHAction ℒ 𝒜).toAlgAut
    (d.shiftedDirectLimitBCHAction_map_mul ℒ 𝒜)

/-- The algebra action has the original global linear action as underlying map. -/
@[simp]
theorem shiftedDirectLimitBCHAlgAction_apply (g : d.completedBCHGroup ℒ)
    (x : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g x = d.shiftedDirectLimitBCHAction ℒ 𝒜 g x := by
  simp only [shiftedDirectLimitBCHAlgAction, MonoidHom.toAlgAut_apply]

/-- Arbitrary-origin chart embeddings intertwine the completed algebra action. -/
theorem shiftedDirectLimitBCHAlgAction_toShiftedDirectLimitOfChart (g : d.completedBCHGroup ℒ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients 𝒜 p) :
    d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g
        (d.toShiftedDirectLimitOfChart 𝒜 p s hp x) =
      d.toShiftedDirectLimitOfChart 𝒜 p s hp
        ((d.shiftedLieFiltration ℒ 𝒜 p).completedBCHAction d ℒ g x) := by
  rw [shiftedDirectLimitBCHAlgAction_apply,
    shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart]

/-- Inverting the label reverses its global algebra action. -/
@[simp]
theorem shiftedDirectLimitBCHAlgAction_inv (g : d.completedBCHGroup ℒ) :
    d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g⁻¹ = (d.shiftedDirectLimitBCHAlgAction ℒ 𝒜 g).symm :=
  map_inv (d.shiftedDirectLimitBCHAlgAction ℒ 𝒜) g

end TauCeti.PositiveDegrees
