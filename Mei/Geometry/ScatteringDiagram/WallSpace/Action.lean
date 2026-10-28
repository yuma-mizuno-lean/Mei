/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Algebra.Lie.Filtered.BCH

/-!
# Wall actions on tangent coefficients

An action is wall-annihilating if a homogeneous wall element kills a homogeneous
coefficient whenever its normal vanishes on that coefficient's geometric degree.
The same holds for the supported-ray sum. Consequently finite wall exponentials
and completed wall labels fix such coefficients, including every coefficient of
zero geometric direction.

The condition is independent of the graded-action condition and applies to Lie
modules as well as coefficient algebras. Exponential component statements require
a nilpotent acting endomorphism. For a filtration-raising action, the finite
quotient actions are nilpotent and completed wall labels fix the coefficient
images in the completion.

The annihilation condition is from Travis Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

namespace Mei

section Monoid

variable {Γ Λ R L M : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}

/-- Homogeneous wall elements annihilate coefficient pieces tangent to their normal.
This is an additional condition on the action, not a consequence of the wall-space
bracket laws or the degree-shifting condition. -/
class IsWallAnnihilating (H : DirectedWallSpaces ρ ℒ) (𝒜 : Γ → Submodule R M) : Prop where
  /-- A wall normal vanishing on the coefficient degree forces the action to vanish. -/
  lie_eq_zero : ∀ {n p : Γ} {m : Λ →+ ℤ} {x : L} {a : M},
    x ∈ H.wall n m → a ∈ 𝒜 p → m (ρ p) = 0 → ⁅x, a⁆ = 0

/-- Restricting a wall-annihilating action to a Lie submodule preserves annihilation
for its inherited ambient homogeneous pieces. -/
instance IsWallAnnihilating.comap (H : DirectedWallSpaces ρ ℒ)
    (𝒜 : Γ → Submodule R M) [IsWallAnnihilating H 𝒜] (S : LieSubmodule R L M) :
    IsWallAnnihilating H (fun p => (𝒜 p).comap S.incl.toLinearMap) where
  lie_eq_zero hx ha hm := by
    apply Subtype.ext
    exact IsWallAnnihilating.lie_eq_zero (H := H) (𝒜 := 𝒜) hx ha hm

namespace DirectedWallSpaces

variable (H : DirectedWallSpaces ρ ℒ) (𝒜 : Γ → Submodule R M)
  [IsWallAnnihilating H 𝒜] {d : PositiveDegrees Γ}

variable [DecidableEq Γ] [DirectSum.Decomposition 𝒜] [SetLike.GradedBracket ℒ 𝒜]

/-- A homogeneous wall action has no component at a degree tangent to its normal. -/
theorem decompose_lie_eq_zero_of_mem_wall_of_normal_eq_zero
    {n q : Γ} {m : Λ →+ ℤ} {x : L} (hx : x ∈ H.wall n m)
    (hq : m (ρ q) = 0) (a : M) : DirectSum.decompose 𝒜 ⁅x, a⁆ q = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hn := H.normal_apply_eq_zero hx hx0
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous p a =>
    by_cases hp : m (ρ p) = 0
    · rw [IsWallAnnihilating.lie_eq_zero (H := H) (𝒜 := 𝒜) hx a.property hp]
      simp
    · have hne : n + p ≠ q := by
        intro he
        exact hp (by simpa only [← he, map_add, hn, zero_add] using hq)
      apply Subtype.ext
      simpa only [ZeroMemClass.coe_zero] using
        DirectSum.decompose_of_mem_ne 𝒜
          (SetLike.GradedBracket.bracket_mem (H.wall_le_piece n m hx) a.property) hne
  | add a b ha hb =>
    simp only [lie_add, DirectSum.decompose_add, DirectSum.add_apply, ha, hb, add_zero]

end DirectedWallSpaces

end Monoid

variable {Γ Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}

namespace DirectedWallSpaces

variable (H : DirectedWallSpaces ρ ℒ) (𝒜 : Γ → Submodule R M)
  [IsWallAnnihilating H 𝒜] {d : PositiveDegrees Γ}

/-- The full supported-ray wall algebra annihilates every coefficient tangent
to its normal. No decomposition of the coefficient module is required. -/
theorem lie_eq_zero_of_mem_ray_of_normal_eq_zero {w : SupportedRay d}
    {m : Λ →+ ℤ} {x : L} (hx : x ∈ H.raySubmodule w m)
    {p : Γ} {a : M} (ha : a ∈ 𝒜 p) (hm : m (ρ p) = 0) : ⁅x, a⁆ = 0 := by
  rw [raySubmodule_def] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ⁅x, a⁆ = 0) hx ?_ ?_ ?_
  · intro n x hx
    exact IsWallAnnihilating.lie_eq_zero (H := H) (𝒜 := 𝒜) hx ha hm
  · exact zero_lie a
  · intro x y hx hy
    simp only [add_lie, hx, hy, add_zero]

/-- In particular, every wall-ray algebra kills pieces of zero geometric direction. -/
theorem lie_eq_zero_of_mem_ray_of_direction_eq_zero {w : SupportedRay d}
    {m : Λ →+ ℤ} {x : L} (hx : x ∈ H.raySubmodule w m)
    {p : Γ} {a : M} (ha : a ∈ 𝒜 p) (hp : ρ p = 0) : ⁅x, a⁆ = 0 :=
  H.lie_eq_zero_of_mem_ray_of_normal_eq_zero 𝒜 hx ha (by simp [hp])

section Components

variable [DecidableEq Γ] [DirectSum.Decomposition 𝒜] [SetLike.GradedBracket ℒ 𝒜]

/-- A supported-ray wall action has no component at a degree tangent to its normal. -/
theorem decompose_lie_eq_zero_of_mem_ray_of_normal_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {x : L} (hx : x ∈ H.raySubmodule w m)
    {q : Γ} (hq : m (ρ q) = 0) (a : M) : DirectSum.decompose 𝒜 ⁅x, a⁆ q = 0 := by
  rw [raySubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => DirectSum.decompose 𝒜 ⁅x, a⁆ q = 0) hx ?_ ?_ ?_
  · intro n x hx
    exact H.decompose_lie_eq_zero_of_mem_wall_of_normal_eq_zero 𝒜 hx hq a
  · simp
  · intro x y hx hy
    simp only [add_lie, DirectSum.decompose_add, DirectSum.add_apply, hx, hy, add_zero]

variable [LieModule R L M] [Algebra ℚ R] [Module ℚ M]

/-- A nilpotent wall exponential preserves every coefficient component tangent
to its normal. Thus no distinct homogeneous input contributes to that component. -/
theorem decompose_exp_eq_of_normal_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {x : L} (hx : x ∈ H.raySubmodule w m)
    (hnil : IsNilpotent (LieModule.toEnd R L M x)) {q : Γ}
    (hq : m (ρ q) = 0) (a : M) :
    DirectSum.decompose 𝒜 (IsNilpotent.exp (LieModule.toEnd R L M x) a) q =
      DirectSum.decompose 𝒜 a q := by
  let : Module ℚ (𝒜 q) := Module.compHom (𝒜 q) (algebraMap ℚ R)
  let f : M →ₗ[R] 𝒜 q := (DirectSum.component R Γ (fun q => 𝒜 q) q).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hf_apply (a : M) : f a = DirectSum.decompose 𝒜 a q := rfl
  have hf : (0 : Module.End R (𝒜 q)).comp f = f.comp (LieModule.toEnd R L M x) := by
    apply LinearMap.ext
    intro a
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, hf_apply,
      LieModule.toEnd_apply_apply] using
      (H.decompose_lie_eq_zero_of_mem_ray_of_normal_eq_zero 𝒜 hx hq a).symm
  have he := LinearMap.congr_fun
    (Module.End.commute_exp_left_of_commute hnil (IsNilpotent.zero) hf) a
  simpa only [IsNilpotent.exp_zero, LinearMap.comp_apply, Module.End.one_apply,
    hf_apply] using he.symm

/-- A wall exponential has no off-diagonal component into a zero-direction piece. -/
theorem decompose_exp_eq_zero_of_direction_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {x : L} (hx : x ∈ H.raySubmodule w m)
    (hnil : IsNilpotent (LieModule.toEnd R L M x)) {p q : Γ}
    {a : M} (ha : a ∈ 𝒜 p) (hpq : p ≠ q) (hq : ρ q = 0) :
    DirectSum.decompose 𝒜 (IsNilpotent.exp (LieModule.toEnd R L M x) a) q = 0 := by
  rw [H.decompose_exp_eq_of_normal_eq_zero 𝒜 hx hnil (by simp [hq])]
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne 𝒜 ha hpq

end Components

section Filtered

variable [LieModule R L M] [Algebra ℚ R]
  [DecidableEq Γ] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F]

/-- The coefficient quotient inherits rational scalars from the scalar ring. -/
local instance quotientRatModule (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom (F.quotient k) (algebraMap ℚ R)

/-- Finite wall exponentials fix tangent homogeneous coefficients in every
coefficient quotient, even when the logarithm has several degrees on its ray. -/
theorem truncatedExpLieAction_mk_eq_self_of_normal_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {k : ℕ} {x : d.truncatedLie ℒ k}
    (hx : x ∈ H.truncatedRayLieSubalgebra w m k)
    {p : Γ} {a : M} (ha : a ∈ 𝒜 p) (hm : m (ρ p) = 0) :
    F.truncatedExpLieAction d ℒ k x (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk a := by
  rw [ModuleFiltration.truncatedExpLieAction_apply]
  apply Module.End.exp_apply_eq_self _ ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩
  obtain ⟨y, hy, rfl⟩ := (H.mem_truncatedRayLieSubalgebra w m k x).mp hx
  rw [LieIdeal.mkQ_apply, ModuleFiltration.truncatedLieAction_mk,
    ModuleFiltration.quotientLieAction_mk,
    H.lie_eq_zero_of_mem_ray_of_normal_eq_zero 𝒜 hy ha hm]
  exact Submodule.Quotient.mk_zero _

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A completed wall label fixes the image of each homogeneous coefficient
tangent to its normal. No separatedness assumption on the original module is needed. -/
theorem completedBCHAction_of_eq_self_of_normal_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m)
    {p : Γ} {a : M} (ha : a ∈ 𝒜 p) (hm : m (ρ p) = 0) :
    F.completedBCHAction d ℒ g (F.of a) = F.of a := by
  apply F.completion_ext
  intro k
  rw [ModuleFiltration.projection_completedBCHAction, ModuleFiltration.projection_of]
  exact (F.truncatedBCHAction_apply d ℒ k (CompletedGroup.projection k g)
    (Submodule.Quotient.mk a)).trans
      (H.truncatedExpLieAction_mk_eq_self_of_normal_eq_zero 𝒜 F
        ((H.mem_wallGroup w m g).mp hg k) ha hm)

/-- Every ordinary wall label fixes homogeneous coefficients of zero geometric direction. -/
theorem completedBCHAction_of_eq_self_of_direction_eq_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m)
    {p : Γ} {a : M} (ha : a ∈ 𝒜 p) (hp : ρ p = 0) :
    F.completedBCHAction d ℒ g (F.of a) = F.of a :=
  H.completedBCHAction_of_eq_self_of_normal_eq_zero 𝒜 F hg ha (by simp [hp])

end Filtered

end DirectedWallSpaces
end Mei
