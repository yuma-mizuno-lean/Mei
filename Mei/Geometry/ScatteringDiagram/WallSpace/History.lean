/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.NormalVelocity
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.LinearAlgebra.GradedModule.History.Basic

/-!
# Normal velocities of whole wall-action histories

Every encounter in a surviving homogeneous history of finite BCH wall actions
preserves normal degree. This includes the encounter adjacent to the incoming
coefficient and applies to arbitrary homogeneous quotient classes. On shifted
coefficients it preserves the normal evaluation of the ambient coefficient
degree, even though the quotient grading records relative degrees.

The argument combines
`DirectedWallSpaces.normal_eq_of_decompose_truncatedBCHAction_ne_zero` with
`homogeneousHistoryStage_mem_snoc` and `homogeneousHistoryStage_ne_zero`.
No wall-annihilation hypothesis is needed: normal conservation follows from
homogeneity and the tangent degrees of wall logarithms. Inverse labels and
nonzero shifts of zero spatial direction are included.

For these whole-component and normal-velocity conventions, see Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§2.1 and Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.DirectedWallSpaces

section Quotient

variable {Γ Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M)
  [SetLike.GradedBracket ℒ ℳ]

/-- Normal degree is conserved at every step of a nonzero whole-component
history. The last comparison uses the incoming degree, not a selected output
degree. Each encounter may have a different ray and normal. -/
theorem homogeneousHistory_truncatedBCHAction_normal_eq
    (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F] (k : ℕ)
    (𝓝 : Γ → Submodule R (F.quotient k)) [DirectSum.Decomposition 𝓝]
    (h𝓝 : ∀ q, 𝓝 q = (ℳ q).map (F.submodule (k + 1)).mkQ)
    {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (w : Fin n → SupportedRay d) (m : Fin n → Λ →+ ℤ)
    (hg : ∀ j, BCHGroup.log (g j) ∈ H.truncatedRayLieSubalgebra (w j) (m j) k)
    (r : Fin n → Γ) (r₀ : Γ) (a : 𝓝 r₀)
    (hne : homogeneousHistory 𝓝
      (fun j => (F.truncatedBCHAction d ℒ k (g j)).toLinearMap) r a ≠ 0)
    (j : Fin n) :
    m j (ρ (r j)) = m j (ρ (Fin.snoc (α := fun _ => Γ) r r₀ j.succ)) := by
  let T := fun j => (F.truncatedBCHAction d ℒ k (g j)).toLinearMap
  apply H.normal_eq_of_decompose_truncatedBCHAction_ne_zero ℳ F (hg j) 𝓝 h𝓝
    (homogeneousHistoryStage_mem_snoc 𝓝 T r r₀ a j.succ)
  intro hz
  apply homogeneousHistoryStage_ne_zero 𝓝 T r hne j.castSucc
  rw [homogeneousHistoryStage_castSucc_apply]
  exact congrArg Subtype.val hz

end Quotient

variable {Γ : Type} {Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M)
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ] (p : Γ)

/-- A finite BCH wall history on shifted coefficients preserves the ambient
normal velocity at each encounter. The ambient shift can have any degree. -/
theorem homogeneousHistory_shiftedBCHAction_normal_eq
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (w : Fin n → SupportedRay d) (m : Fin n → Λ →+ ℤ)
    (hg : ∀ j, BCHGroup.log (g j) ∈ H.truncatedRayLieSubalgebra (w j) (m j) k)
    (r : Fin n → Γ) (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
    (hne : homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        (g j)).toLinearMap) r a ≠ 0) (j : Fin n) :
    m j (ρ (p + r j)) =
      m j (ρ (p + Fin.snoc (α := fun _ => Γ) r r₀ j.succ)) := by
  have := d.shiftedGrading_gradedBracket ℒ ℳ p
  have he := H.homogeneousHistory_truncatedBCHAction_normal_eq
    (M := d.shiftedLieSubmodule ℒ ℳ p)
    (shiftedGrading ℳ d.monoid p) (d.shiftedLieFiltration ℒ ℳ p) k
    (d.shiftedQuotientGrading ℳ p k).piece
    (d.shiftedQuotientGrading_piece ℳ p k) g w m hg r r₀ a hne j
  simp only [map_add, he]

end Mei.DirectedWallSpaces
