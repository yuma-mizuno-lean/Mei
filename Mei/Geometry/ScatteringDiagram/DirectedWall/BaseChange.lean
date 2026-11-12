/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.RestrictScalars
public import Mei.Geometry.ScatteringDiagram.WallSpace.BaseChange

/-!
# Scalar extension of directed walls

Let `H` be directed wall spaces of a positively graded Lie algebra `g` over a commutative
`ℚ`-algebra `R`, and let `S` be a commutative `R`-algebra that is also a `ℚ`-algebra, in the
universe of `g`. The `R`-linear fixed-degree graded Lie homomorphism `x ↦ 1 ⊗ x`
(`Mei.GradedLieHom.includeRight`) maps each wall space `h_{n,m}` into the extended wall space
`im(S ⊗[R] h_{n,m} → S ⊗[R] g)` (`DirectedWallSpaces.baseChange`). Hence every directed wall
`W` for `H` gives a directed wall `W.baseChange S` for `H.baseChange S`
(`DirectedWall.baseChange`), with the same normal, supported ray and support, by
`DirectedWall.mapRestrictScalars` over the common base ring `R`. No flatness of `S` is assumed.

The scalar extension takes place at finite order: the truncation comparison
`PositiveDegrees.truncatedBaseChangeEquiv` sends the order-`k` label of `W.baseChange S` to
`exp (1 ⊗ log g_k)` in `S ⊗[R] g≤k`, where `g_k` is the order-`k` label of `W`
(`DirectedWall.bchGroupMap_projection_baseChange_label`).

This is the change of coefficient ring of Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, Example 2.1(i) (arXiv:1503.06183v5), for scalar extension.
-/

public section

noncomputable section

open TensorProduct

namespace Mei.DirectedWall

universe u

variable {Γ Λ R V : Type*} {L : Type u} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
  [IsScalarTower ℚ R L] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  (S : Type u) [CommRing S] [Algebra R S] [Algebra ℚ S]

variable (W : DirectedWall (d := d) h H)

/-- Extend the scalars of a directed wall along `x ↦ 1 ⊗ x`, retaining its normal, supported
ray and support. -/
def baseChange : DirectedWall (d := d) h (H.baseChange S) :=
  W.mapRestrictScalars (GradedLieHom.includeRight S ℒ)
    (H.includeRight_mem_restrictScalars_baseChange_wall S)

/-- Scalar extension is the coefficient change along `x ↦ 1 ⊗ x`. -/
theorem baseChange_def :
    W.baseChange S = W.mapRestrictScalars (GradedLieHom.includeRight S ℒ)
      (H.includeRight_mem_restrictScalars_baseChange_wall S) := (rfl)

/-- Scalar extension keeps the normal. -/
@[simp]
theorem baseChange_normal : (W.baseChange S).normal = W.normal :=
  W.mapRestrictScalars_normal _ _

/-- Scalar extension keeps the supported ray. -/
@[simp]
theorem baseChange_ray : (W.baseChange S).ray = W.ray :=
  W.mapRestrictScalars_ray _ _

/-- Scalar extension keeps the support. -/
@[simp]
theorem baseChange_support : (W.baseChange S).support = W.support :=
  W.mapRestrictScalars_support _ _

/-- Scalar extension preserves and reflects incomingness. -/
@[simp]
theorem incoming_baseChange_iff : (W.baseChange S).Incoming ↔ W.Incoming :=
  W.incoming_mapRestrictScalars_iff _ _

/-- Scalar extension preserves and reflects outgoingness. -/
@[simp]
theorem outgoing_baseChange_iff : (W.baseChange S).Outgoing ↔ W.Outgoing :=
  W.outgoing_mapRestrictScalars_iff _ _

/-- The truncation comparison `(S ⊗[R] g)≤k ≃ S ⊗[R] g≤k` sends the order-`k` label of the
scalar extension to `exp (1 ⊗ log g_k)`, for the order-`k` label `g_k` of `W`. -/
theorem bchGroupMap_projection_baseChange_label (k : ℕ) :
    (d.truncatedBaseChangeEquiv (S := S) ℒ k).toLieHom.bchGroupMap
        (CompletedGroup.projection k (W.baseChange S).label) =
      (LieAlgebra.ExtendScalars.includeRight R S (d.truncatedLie ℒ k)).bchGroupMap
        (CompletedGroup.projection k W.label) := by
  rw [baseChange_def, mapRestrictScalars_label,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv,
    GradedLieHom.projection_completedMap_of_le _ k (PositiveDegreeMap.id_modulus k).le,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv_symm]
  apply BCHGroup.log_injective
  have hk := LieHom.congr_fun (GradedLieHom.truncatedMap_includeRight S ℒ k)
    ((d.truncatedRestrictScalarsEquiv (R := R) ℒ k).symm
      (BCHGroup.log (CompletedGroup.projection k W.label)))
  simp only [LieHom.comp_apply, LieHom.restrictScalars_apply, LieEquiv.coe_toLieHom,
    LieEquiv.apply_symm_apply] at hk
  simp only [LieHom.log_bchGroupMap, BCHGroup.log_exp, LieEquiv.coe_toLieHom, hk]
  -- The projection has a categorical tower-object type; read it as a BCH group element.
  exact (LieHom.log_bchGroupMap _ _).symm

end Mei.DirectedWall
