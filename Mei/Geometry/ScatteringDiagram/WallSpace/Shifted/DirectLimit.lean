/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Shifted
public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.ZeroDirection

/-!
# Tangent and zero-direction components of global wall actions

An ordinary completed wall label preserves every tangent component of a global
shifted coefficient, including coefficients with infinite support. Homogeneous
finite coefficients tangent to the normal are fixed in every containing chart.
In particular, zero-direction inputs are fixed, and distinct homogeneous inputs
have no output component of zero direction.

These statements descend the completed shifted wall-action laws through the
existing global BCH action and its chart-independent component maps. They require
no spanning assumption on the positive monoid. The annihilation and coefficient
conventions follow Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §2.1 and the proof of Theorem 2.14 (arXiv:1503.06183v5).
-/

public section
noncomputable section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] [IsWallAnnihilating H ℳ]

/-- A wall label preserves every tangent component of an arbitrary global coefficient. -/
theorem shiftedDirectLimitComponents_BCHAction_of_normal_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {q : Γ} (hq : m (ρ q) = 0)
    (a : d.ShiftedDirectLimit ℳ) :
    d.shiftedDirectLimitComponents ℳ (d.shiftedDirectLimitBCHAction ℒ ℳ g a) q =
      d.shiftedDirectLimitComponents ℳ a q := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ a
  rw [PositiveDegrees.shiftedDirectLimitBCHAction_toShiftedDirectLimit,
    PositiveDegrees.shiftedDirectLimitComponents_toShiftedDirectLimit,
    PositiveDegrees.shiftedDirectLimitComponents_toShiftedDirectLimit]
  exact H.shiftedHomogeneousComponent_completedBCHAction_of_normal_eq_zero
    ℳ (d.coefficientOrigin s) hg hq a

/-- A tangent homogeneous finite coefficient is fixed in any containing global chart. -/
theorem shiftedDirectLimitBCHAction_of_eq_self_of_normal_eq_zero
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {r : Γ}
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) (hr : m (ρ r) = 0) :
    d.shiftedDirectLimitBCHAction ℒ ℳ g
      (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a)) =
        d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a) := by
  rw [PositiveDegrees.shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart]
  exact congrArg (d.toShiftedDirectLimitOfChart ℳ p s hp)
    (H.completedBCHAction_of_eq_self_of_normal_eq_zero
      (fun q => (ℳ q).comap (d.shiftedLieSubmodule ℒ ℳ p).incl.toLinearMap)
      (d.shiftedLieFiltration ℒ ℳ p) hg ha hr)

/-- Ordinary wall labels fix homogeneous zero-direction coefficients in every global chart. -/
theorem shiftedDirectLimitBCHAction_of_eq_self_of_direction_eq_zero
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {r : Γ}
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) (hr : ρ r = 0) :
    d.shiftedDirectLimitBCHAction ℒ ℳ g
      (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a)) =
        d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a) :=
  H.shiftedDirectLimitBCHAction_of_eq_self_of_normal_eq_zero ℳ p s hp hg a ha (by simp [hr])

/-- Ordinary wall labels fix every zero-direction coefficient. -/
theorem smul_eq_self_of_mem_zeroDirectionCoefficients
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {x : d.ShiftedDirectLimit ℳ}
    (hx : x ∈ d.zeroDirectionCoefficients ρ ℳ) : g • x = x := by
  rw [PositiveDegrees.zeroDirectionCoefficients_def] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, s, hp, r, a, ha, hr, rfl⟩ := hx
    rw [PositiveDegrees.smul_eq_shiftedDirectLimitBCHAction]
    exact H.shiftedDirectLimitBCHAction_of_eq_self_of_direction_eq_zero ℳ p s hp hg a ha hr
  | zero => exact smul_zero g
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | smul r x _ hx => rw [smul_comm, hx]

/-- A homogeneous input has no distinct zero-direction output under a global wall action. -/
theorem shiftedDirectLimitComponents_BCHAction_eq_zero_of_direction_eq_zero
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {r q : Γ} (hrq : r ≠ q) (hq : ρ q = 0)
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) :
    d.shiftedDirectLimitComponents ℳ
      (d.shiftedDirectLimitBCHAction ℒ ℳ g
        (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a))) q = 0 := by
  rw [PositiveDegrees.shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    PositiveDegrees.shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]
  exact H.shiftedHomogeneousComponent_completedBCHAction_eq_zero_of_direction_eq_zero
    ℳ p hg hrq hq a ha

end Mei.DirectedWallSpaces
