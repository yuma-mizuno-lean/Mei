/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Action
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.Component

/-!
# Tangent components of completed shifted wall actions

A wall label preserves every homogeneous coefficient component whose degree is
annihilated by its normal. This holds on finite shifted quotients and on arbitrary
completed shifted coefficients, even when the wall logarithm has infinitely many
homogeneous terms. In particular, a homogeneous input cannot acquire a distinct
output degree with zero geometric direction. Such components can therefore be
handled separately in recursions for broken-line coefficients.

The finite comparison uses `DirectedWallSpaces.decompose_lie_eq_zero_of_mem_ray_of_normal_eq_zero`
and Mathlib's `Module.End.commute_exp_left_of_commute`. The completed comparison
uses the existing shifted component maps and the levelwise BCH action. The
annihilation condition and its application to zero-direction coefficients follow
Travis Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §2.1 and the proof of Theorem 2.14 (arXiv:1503.06183v5).
-/

public section

noncomputable section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]
  [IsWallAnnihilating H ℳ] (p : Γ)

/-- A finite wall exponential preserves each retained shifted component tangent
to its normal. The coefficient input may contain several homogeneous degrees. -/
theorem shiftedQuotientComponent_truncatedExpLieAction_of_normal_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {k : ℕ} {x : d.truncatedLie ℒ k}
    (hx : x ∈ H.truncatedRayLieSubalgebra w m k) {q : Γ}
    (hq : m (ρ q) = 0) (hk : d.degree (q - p) ≤ k)
    (a : (d.shiftedLieFiltration ℒ ℳ p).quotient k) :
    d.shiftedQuotientComponent ℳ p q k hk
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedExpLieAction d ℒ k x a) =
      d.shiftedQuotientComponent ℳ p q k hk a := by
  let F := d.shiftedLieFiltration ℒ ℳ p
  let f := d.shiftedQuotientComponent ℳ p q k hk
  let : Module ℚ (F.quotient k) := Module.compHom _ (algebraMap ℚ R)
  let : Module ℚ (ℳ q) := Module.compHom _ (algebraMap ℚ R)
  have hf : (0 : Module.End R (ℳ q)).comp f =
      f.comp (F.truncatedLieAction d ℒ k x) := by
    apply LinearMap.ext
    intro b
    obtain ⟨y, hy, rfl⟩ := (H.mem_truncatedRayLieSubalgebra w m k x).mp hx
    obtain ⟨b, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective b
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LieIdeal.mkQ_apply,
      ModuleFiltration.truncatedLieAction_mk, Submodule.mkQ_apply,
      ModuleFiltration.quotientLieAction_mk]
    have hb := d.shiftedQuotientComponent_mk ℳ p q k hk
      (⁅y, b⁆ : d.shiftedLieSubmodule ℒ ℳ p)
    exact (hb.trans
      (H.decompose_lie_eq_zero_of_mem_ray_of_normal_eq_zero ℳ hy hq (b : M))).symm
  have he := LinearMap.congr_fun
    (Module.End.commute_exp_left_of_commute
      ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩ IsNilpotent.zero hf) a
  simpa only [ModuleFiltration.truncatedExpLieAction_apply, IsNilpotent.exp_zero,
    LinearMap.comp_apply, Module.End.one_apply] using he.symm

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A completed wall label preserves every tangent homogeneous component of an
arbitrary completed shifted coefficient, without a finite logarithm hypothesis. -/
theorem shiftedHomogeneousComponent_completedBCHAction_of_normal_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {q : Γ} (hq : m (ρ q) = 0)
    (a : d.ShiftedCoefficients ℳ p) :
    d.shiftedHomogeneousComponent ℳ p q
        ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g a) =
      d.shiftedHomogeneousComponent ℳ p q a := by
  let F := d.shiftedLieFiltration ℒ ℳ p
  let k := (d.degree (q - p)).toNat
  let gk : BCHGroup (d.truncatedLie ℒ k) := CompletedGroup.projection k g
  have hk : d.degree (q - p) ≤ k := Int.self_le_toNat _
  have hp : F.projection k (F.completedBCHAction d ℒ g a) =
      F.truncatedExpLieAction d ℒ k (BCHGroup.log gk) (F.projection k a) :=
    (F.projection_completedBCHAction d ℒ g a k).trans
      (F.truncatedBCHAction_apply d ℒ k gk (F.projection k a))
  calc
    _ = d.shiftedQuotientComponent ℳ p q k hk
        (F.projection k (F.completedBCHAction d ℒ g a)) :=
      d.shiftedHomogeneousComponent_eq ℳ p q k hk _
    _ = d.shiftedQuotientComponent ℳ p q k hk (F.projection k a) := by
      rw [hp]
      exact H.shiftedQuotientComponent_truncatedExpLieAction_of_normal_eq_zero ℳ p
        ((H.mem_wallGroup w m g).mp hg k) hq hk _
    _ = _ := (d.shiftedHomogeneousComponent_eq ℳ p q k hk a).symm

/-- No off-diagonal component of a homogeneous coefficient can enter a degree
of zero geometric direction under a completed wall action. The shift `p` is
independent of both the input and the output degree. -/
theorem shiftedHomogeneousComponent_completedBCHAction_eq_zero_of_direction_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {r q : Γ} (hrq : r ≠ q) (hq : ρ q = 0)
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) :
    d.shiftedHomogeneousComponent ℳ p q
        ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g
          ((d.shiftedFiltration ℳ p).of a)) = 0 := by
  rw [H.shiftedHomogeneousComponent_completedBCHAction_of_normal_eq_zero ℳ p hg
    (by simp [hq]), d.shiftedHomogeneousComponent_of]
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne ℳ ha hrq

end Mei.DirectedWallSpaces
