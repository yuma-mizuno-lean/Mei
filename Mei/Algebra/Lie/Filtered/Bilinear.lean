/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.ModuleFiltration.Bilinear
public import Mei.LinearAlgebra.End.Exp

/-!
# BCH actions and filtered bilinear pairings

A filtration-compatible bilinear pairing satisfying the Leibniz rule for three
Lie actions intertwines the associated finite exponential actions and completed
BCH actions. The quotients and completed pairing use the existing bilinear
filtration API, and the finite exponential step uses the general tensor-product
intertwining theorem. The three coefficient modules may be different.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei.ModuleFiltration

variable {Γ R L M N P : Type*} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N) (H : ModuleFiltration R P)
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  [DecidableEq Γ] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F] [IsFiltrationRaising d ℒ G] [IsFiltrationRaising d ℒ H]
  (f : M →ₗ[R] N →ₗ[R] P)
  (hf : ∀ (a b : ℕ) {x y}, x ∈ F.submodule a → y ∈ G.submodule b →
    f x y ∈ H.submodule (a + b))
  (hequiv : ∀ (z : L) (x : M) (y : N), ⁅z, f x y⁆ = f x ⁅z, y⁆ + f ⁅z, x⁆ y)

include hequiv

omit [Algebra ℚ R] in
/-- The Leibniz rule descends to matching finite Lie and coefficient quotients. -/
theorem truncatedLieAction_quotientBilinear (k : ℕ) (z : d.truncatedLie ℒ k)
    (x : F.quotient k) (y : G.quotient k) :
    H.truncatedLieAction d ℒ k z (quotientBilinear F G H f hf k x y) =
      quotientBilinear F G H f hf k x (G.truncatedLieAction d ℒ k z y) +
        quotientBilinear F G H f hf k (F.truncatedLieAction d ℒ k z x) y := by
  obtain ⟨z, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ z
  obtain ⟨x, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (G.submodule (k + 1)).mkQ_surjective y
  simp only [Submodule.mkQ_apply, LieIdeal.mkQ_apply, truncatedLieAction_mk,
    quotientBilinear_mk, quotientLieAction_mk, hequiv]
  exact map_add ((H.submodule (k + 1)).mkQ) _ _

/-- Matching finite exponential actions preserve a filtered bilinear pairing. -/
theorem truncatedExpLieAction_quotientBilinear (k : ℕ) (z : d.truncatedLie ℒ k)
    (x : F.quotient k) (y : G.quotient k) :
    H.truncatedExpLieAction d ℒ k z (quotientBilinear F G H f hf k x y) =
      quotientBilinear F G H f hf k (F.truncatedExpLieAction d ℒ k z x)
        (G.truncatedExpLieAction d ℒ k z y) := by
  let : Module ℚ (F.quotient k) := Module.compHom _ (algebraMap ℚ R)
  let : Module ℚ (G.quotient k) := Module.compHom _ (algebraMap ℚ R)
  let : Module ℚ (H.quotient k) := Module.compHom _ (algebraMap ℚ R)
  simp only [truncatedExpLieAction_apply]
  exact (quotientBilinear F G H f hf k).exp_bilinear_of_leibniz
    (F.truncatedLieAction d ℒ k z) (G.truncatedLieAction d ℒ k z)
    (H.truncatedLieAction d ℒ k z)
    (truncatedLieAction_quotientBilinear F G H d ℒ f hf hequiv k z)
    ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k z⟩
    ⟨k + 1, G.truncatedLieAction_pow_eq_zero d ℒ k z⟩
    ⟨k + 1, H.truncatedLieAction_pow_eq_zero d ℒ k z⟩ x y

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Matching finite BCH actions preserve a filtered bilinear pairing. -/
theorem truncatedBCHAction_quotientBilinear (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k))
    (x : F.quotient k) (y : G.quotient k) :
    H.truncatedBCHAction d ℒ k g (quotientBilinear F G H f hf k x y) =
      quotientBilinear F G H f hf k (F.truncatedBCHAction d ℒ k g x)
        (G.truncatedBCHAction d ℒ k g y) := by
  rw [H.truncatedBCHAction_apply, F.truncatedBCHAction_apply, G.truncatedBCHAction_apply]
  exact truncatedExpLieAction_quotientBilinear F G H d ℒ f hf hequiv k _ _ _

/-- Completed BCH actions preserve every Leibniz-compatible filtered bilinear pairing. -/
theorem completedBCHAction_completionBilinear (g : d.completedBCHGroup ℒ)
    (x : F.completion) (y : G.completion) :
    H.completedBCHAction d ℒ g (completionBilinear F G H f hf x y) =
      completionBilinear F G H f hf (F.completedBCHAction d ℒ g x)
        (G.completedBCHAction d ℒ g y) := by
  apply H.completion_ext
  intro k
  let : Module ℚ (F.quotient k) := Module.compHom _ (algebraMap ℚ R)
  let : Module ℚ (G.quotient k) := Module.compHom _ (algebraMap ℚ R)
  let : Module ℚ (H.quotient k) := Module.compHom _ (algebraMap ℚ R)
  simp only [projection_completedBCHAction, projection_completionBilinear]
  exact truncatedBCHAction_quotientBilinear F G H d ℒ f hf hequiv k
    (TauCeti.CompletedGroup.projection k g) (F.projection k x) (G.projection k y)

end Mei.ModuleFiltration
