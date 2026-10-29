/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import Mei.CategoryTheory.Limits.Reindex

/-!
# Maps of filtered module completions

A linear map sending the source term at `ρ k + 1` into the target term at
`k + 1`, for a monotone cutoff modulus `ρ`, induces a linear map of completions.
Its order-`k` component is Mathlib's `Submodule.mapQ` applied to the source
projection at order `ρ k`.

The induced map is independent of the cutoff modulus. It commutes with the
canonical maps, preserves the indicated filtration orders, and respects identity
and composition. Successive moduli compose in the order `ρ ∘ μ`. These maps
allow coefficient modules to be compared even when their truncation orders differ.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Mei.ModuleFiltration

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N)
  (f : M →ₗ[R] N) (ρ : ℕ → ℕ)

/-- The map of completions induced by a linear map with a monotone cutoff modulus. -/
def completionMap (hρ : Monotone ρ)
    (hf : ∀ k, F.submodule (ρ k + 1) ≤ (G.submodule (k + 1)).comap f) :
    F.completion →ₗ[R] G.completion :=
  G.lift (fun k => ((F.submodule (ρ k + 1)).mapQ (G.submodule (k + 1)) f (hf k)).comp
    (F.projection (ρ k))) (by
      intro k l h
      apply LinearMap.ext
      intro x
      obtain ⟨a, ha⟩ := (F.submodule (ρ l + 1)).mkQ_surjective (F.projection (ρ l) x)
      simp only [Submodule.mkQ_apply] at ha
      have hk := F.transition_projection (hρ h) x
      rw [← ha, transition_mk] at hk
      simp only [LinearMap.comp_apply]
      rw [← hk, ← ha, Submodule.mapQ_apply, transition_mk, Submodule.mapQ_apply])

variable (hρ : Monotone ρ)
  (hf : ∀ k, F.submodule (ρ k + 1) ≤ (G.submodule (k + 1)).comap f)

/-- Projection computes the induced map using the quotient map at the chosen cutoff. -/
@[simp]
theorem projection_completionMap (k : ℕ) (x : F.completion) :
    G.projection k (F.completionMap G f ρ hρ hf x) =
      (F.submodule (ρ k + 1)).mapQ (G.submodule (k + 1)) f (hf k)
        (F.projection (ρ k) x) :=
  G.projection_lift _ _ k x

/-- Any finer source cutoff computes the same target component. -/
theorem projection_completionMap_of_le (k n : ℕ) (h : ρ k ≤ n) (x : F.completion) :
    G.projection k (F.completionMap G f ρ hρ hf x) =
      (F.submodule (n + 1)).mapQ (G.submodule (k + 1)) f
        ((F.antitone (Nat.add_le_add_right h 1)).trans (hf k)) (F.projection n x) := by
  rw [projection_completionMap]
  obtain ⟨a, ha⟩ := (F.submodule (n + 1)).mkQ_surjective (F.projection n x)
  simp only [Submodule.mkQ_apply] at ha
  have hk := F.transition_projection h x
  rw [← ha, transition_mk] at hk
  rw [← hk, ← ha, Submodule.mapQ_apply, Submodule.mapQ_apply]

/-- Completion maps extend the original linear maps. -/
@[simp]
theorem completionMap_of (x : M) :
    F.completionMap G f ρ hρ hf (F.of x) = G.of (f x) := by
  apply G.completion_ext
  intro k
  simp

/-- The original cutoff bound also holds for the induced filtrations. -/
theorem completionMap_mem_completedFiltration (k : ℕ) {x : F.completion}
    (hx : x ∈ F.completedFiltration.submodule (ρ k + 1)) :
    F.completionMap G f ρ hρ hf x ∈ G.completedFiltration.submodule (k + 1) := by
  rw [completedFiltration_succ, LinearMap.mem_ker] at hx ⊢
  rw [projection_completionMap, hx, map_zero]

/-- The induced linear map depends only on the original map, not on its cutoff modulus. -/
theorem completionMap_eq (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hfμ : ∀ k, F.submodule (μ k + 1) ≤ (G.submodule (k + 1)).comap f) :
    F.completionMap G f ρ hρ hf = F.completionMap G f μ hμ hfμ := by
  apply LinearMap.ext
  intro x
  apply G.completion_ext
  intro k
  rw [F.projection_completionMap_of_le G f ρ hρ hf k (max (ρ k) (μ k))
      (le_max_left _ _) x,
    F.projection_completionMap_of_le G f μ hμ hfμ k (max (ρ k) (μ k))
      (le_max_right _ _) x]

/-- The identity map with the identity cutoff modulus induces the identity. -/
@[simp]
theorem completionMap_id :
    F.completionMap F LinearMap.id id monotone_id (fun _ => le_rfl) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply F.completion_ext
  intro k
  simp

/-- The zero linear map induces the zero map of completions for every cutoff modulus. -/
@[simp]
theorem completionMap_zero :
    F.completionMap G 0 ρ hρ (fun _ => by simp) = 0 := by
  apply LinearMap.ext
  intro x
  apply G.completion_ext
  intro k
  simp

variable (H : ModuleFiltration R P) (g : N →ₗ[R] P)
  (μ : ℕ → ℕ) (hμ : Monotone μ)
  (hg : ∀ k, G.submodule (μ k + 1) ≤ (H.submodule (k + 1)).comap g)

/-- Completion respects composition; the source cutoff is `ρ (μ k)`. -/
theorem completionMap_comp :
    F.completionMap H (g.comp f) (ρ ∘ μ) (hρ.comp hμ)
      (fun k => (hf (μ k)).trans (Submodule.comap_mono (hg k))) =
      (G.completionMap H g μ hμ hg).comp (F.completionMap G f ρ hρ hf) := by
  apply LinearMap.ext
  intro x
  apply H.completion_ext
  intro k
  simp only [LinearMap.comp_apply, projection_completionMap, Function.comp_apply]
  rw [Submodule.mapQ_comp, LinearMap.comp_apply]

section TowerMap

variable {R : Type u} {M N : Type v} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N) (f : M →ₗ[R] N)
  (ρ : ℕ → ℕ) (hρ : Monotone ρ)
  (hf : ∀ k, F.submodule (ρ k + 1) ≤ (G.submodule (k + 1)).comap f)

/-- A filtered linear map gives a natural comparison of the quotient towers,
reindexed by its cutoff modulus. -/
def quotientTowerMap :
    (⟨ρ, hρ⟩ : ℕ →o ℕ).toFunctor.op ⋙ F.quotientTower ⟶ G.quotientTower where
  app k := ModuleCat.ofHom ((F.submodule (ρ k.unop + 1)).mapQ
    (G.submodule (k.unop + 1)) f (hf k.unop))
  naturality {k l} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (F.submodule (ρ k.unop + 1)).mkQ_surjective x
    -- Express categorical composition in the concrete quotient modules.
    change (F.submodule (ρ l.unop + 1)).mapQ (G.submodule (l.unop + 1)) f (hf l.unop)
        (F.transition (hρ (leOfHom g.unop)) (Submodule.Quotient.mk x)) =
      G.transition (leOfHom g.unop)
        ((F.submodule (ρ k.unop + 1)).mapQ (G.submodule (k.unop + 1)) f (hf k.unop)
          (Submodule.Quotient.mk x))
    simp only [transition_mk, Submodule.mapQ_apply]

/-- The components of the tower comparison are the induced maps on quotients. -/
@[simp]
theorem quotientTowerMap_app (k : ℕᵒᵖ) :
    (F.quotientTowerMap G f ρ hρ hf).app k =
      ModuleCat.ofHom ((F.submodule (ρ k.unop + 1)).mapQ
        (G.submodule (k.unop + 1)) f (hf k.unop)) := (rfl)

/-- Taking the categorical limit of the quotient comparison recovers the
concrete filtered completion map. -/
theorem completionMap_completionIsoLimit :
    ModuleCat.ofHom (F.completionMap G f ρ hρ hf) ≫ G.completionIsoLimit.hom =
      F.completionIsoLimit.hom ≫ (F.quotientTowerMap G f ρ hρ hf).reindexLimitMap := by
  apply limit.hom_ext
  intro k
  simp only [Category.assoc, completionIsoLimit_hom_π, NatTrans.reindexLimitMap_π,
    quotientTowerMap_app]
  -- The reindexed tower object is the source quotient at the chosen cutoff.
  erw [← Category.assoc, completionIsoLimit_hom_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact F.projection_completionMap G f ρ hρ hf k.unop x

end TowerMap

end Mei.ModuleFiltration
