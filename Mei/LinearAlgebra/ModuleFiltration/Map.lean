/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion

/-!
# Maps of filtered module completions

A linear map preserving submodule filtrations along a monotone cutoff modulus
extends to their compatible-family completions. Its order-`k` projection uses the
source quotient at the modulus of `k`, or any larger order. The extension is
independent of the chosen modulus and respects identities and composition.

The construction uses Mathlib's `Submodule.mapQ` and the universal lift
`Mei.ModuleFiltration.lift`. It applies to arbitrary decreasing submodule
filtrations, including those that are not powers of a single ideal. No
separatedness or cofinality of the modulus is required.
-/

public section

namespace Mei.ModuleFiltration

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N)
  (f : M →ₗ[R] N) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.submodule (l k + 1) ≤ (G.submodule (k + 1)).comap f)

/-- Extend a filtered linear map to completions along its cutoff modulus. -/
def map : F.completion →ₗ[R] G.completion :=
  G.lift (fun k => ((F.submodule (l k + 1)).mapQ (G.submodule (k + 1)) f
    (hf k)).comp (F.projection (l k))) (by
      intro k j h
      ext x
      simp only [LinearMap.comp_apply]
      rw [← F.transition_projection (hl h) x]
      generalize F.projection (l j) x = z
      induction z using Submodule.Quotient.induction_on with
      | _ x => simp)

/-- The order-`k` component is induced from the source quotient at `l k`. -/
@[simp]
theorem projection_map (k : ℕ) (x : F.completion) :
    G.projection k (F.map G f l hl hf x) =
      (F.submodule (l k + 1)).mapQ (G.submodule (k + 1)) f (hf k)
        (F.projection (l k) x) := by
  simp [map]

/-- Any source order above the modulus computes the same target component. -/
theorem projection_map_of_le (k j : ℕ) (h : l k ≤ j) (x : F.completion) :
    G.projection k (F.map G f l hl hf x) =
      (F.submodule (j + 1)).mapQ (G.submodule (k + 1)) f
        ((F.antitone (Nat.add_le_add_right h 1)).trans (hf k))
        (F.projection j x) := by
  rw [projection_map, ← F.transition_projection h x]
  generalize F.projection j x = z
  induction z using Submodule.Quotient.induction_on with
  | _ x => simp

/-- The extension commutes with the canonical maps from the original modules. -/
@[simp]
theorem map_of (x : M) : F.map G f l hl hf (F.of x) = G.of (f x) := by
  apply G.completion_ext
  intro k
  simp

/-- Any two valid monotone moduli give the same completion map. -/
theorem map_eq (m : ℕ → ℕ) (hm : Monotone m)
    (hf' : ∀ k, F.submodule (m k + 1) ≤ (G.submodule (k + 1)).comap f) :
    F.map G f l hl hf = F.map G f m hm hf' := by
  ext x k
  rw [F.projection_map_of_le G f l hl hf k (max (l k) (m k)) (le_max_left _ _),
    F.projection_map_of_le G f m hm hf' k (max (l k) (m k)) (le_max_right _ _)]

/-- The completion map preserves filtration at the orders specified by its modulus. -/
theorem completedFiltration_le_comap_map (k : ℕ) :
    F.completedFiltration.submodule (l k + 1) ≤
      (G.completedFiltration.submodule (k + 1)).comap (F.map G f l hl hf) := by
  intro x hx
  simp only [completedFiltration_succ, Submodule.mem_comap, LinearMap.mem_ker,
    projection_map]
  simp only [completedFiltration_succ, LinearMap.mem_ker] at hx
  rw [hx, map_zero]

/-- Extending the identity with its identity modulus gives the identity map. -/
@[simp]
theorem map_id :
    F.map F LinearMap.id id monotone_id (fun _ => le_rfl) = LinearMap.id := by
  ext x k
  simp

variable (H : ModuleFiltration R P) (g : N →ₗ[R] P)
  (m : ℕ → ℕ) (hm : Monotone m)
  (hg : ∀ k, G.submodule (m k + 1) ≤ (H.submodule (k + 1)).comap g)

/-- Successive completion maps compose with the composite cutoff modulus `l ∘ m`. -/
theorem map_comp :
    F.map H (g.comp f) (l ∘ m) (hl.comp hm)
      (fun k => (hf (m k)).trans (Submodule.comap_mono (hg k))) =
      (G.map H g m hm hg).comp (F.map G f l hl hf) := by
  ext x k
  simp only [LinearMap.comp_apply, projection_map, Function.comp_apply]
  generalize F.projection (l (m k)) x = z
  induction z using Submodule.Quotient.induction_on with
  | _ x => simp

end Mei.ModuleFiltration
