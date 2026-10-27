/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Bilinear maps on filtered module completions

A bilinear map that adds filtration orders induces bilinear maps on matching
quotients and on completions. Projections compute the completed pairing, and
the completed pairing still adds filtration orders. This permits products
between different shifted coefficient modules without identifying their carriers.

The quotient construction uses Mathlib's `LinearMap.liftQ₂`; compatible quotient
families are assembled with `ModuleFiltration.lift`.
-/

public section

namespace Mei.ModuleFiltration

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (F : ModuleFiltration R M) (G : ModuleFiltration R N) (H : ModuleFiltration R P)
  (f : M →ₗ[R] N →ₗ[R] P)
  (hf : ∀ (a b : ℕ) {x y}, x ∈ F.submodule a → y ∈ G.submodule b →
    f x y ∈ H.submodule (a + b))

/-- The bilinear map on quotients retaining the same filtration order. -/
def quotientBilinear (k : ℕ) : F.quotient k →ₗ[R] G.quotient k →ₗ[R] H.quotient k :=
  (f.compr₂ (H.submodule (k + 1)).mkQ).liftQ₂
    (F.submodule (k + 1)) (G.submodule (k + 1))
    (by
      intro x hx
      ext y
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (by simpa using hf (k + 1) 0 hx (by simp)))
    (by
      intro y hy
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (by simpa using hf 0 (k + 1) (by simp) hy))

/-- Quotient pairings act on representatives by the original bilinear map. -/
@[simp]
theorem quotientBilinear_mk (k : ℕ) (x : M) (y : N) :
    quotientBilinear F G H f hf k (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (f x y) :=
  LinearMap.liftQ₂_mk _ _ x y

/-- Quotient pairings commute with decreasing the cutoff. -/
@[simp]
theorem transition_quotientBilinear {k l : ℕ} (h : k ≤ l)
    (x : F.quotient l) (y : G.quotient l) :
    H.transition h (quotientBilinear F G H f hf l x y) =
      quotientBilinear F G H f hf k (F.transition h x) (G.transition h y) := by
  obtain ⟨x, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (G.submodule (l + 1)).mkQ_surjective y
  simp

/-- Extend a bilinear map adding filtration orders to completed modules. -/
def completionBilinear : F.completion →ₗ[R] G.completion →ₗ[R] H.completion :=
  LinearMap.mk₂ R
    (fun x => H.lift
      (fun k => (quotientBilinear F G H f hf k (F.projection k x)).comp (G.projection k))
      (by
        intro k l h
        ext y
        simp))
    (by intros; ext k; simp)
    (by intros; ext k; simp)
    (by intros; exact map_add _ _ _)
    (by intros; exact map_smul _ _ _)

/-- A completed pairing is computed at any common finite cutoff. -/
@[simp]
theorem projection_completionBilinear (k : ℕ) (x : F.completion) (y : G.completion) :
    H.projection k (completionBilinear F G H f hf x y) =
      quotientBilinear F G H f hf k (F.projection k x) (G.projection k y) := by
  simp [completionBilinear]

/-- The completed pairing extends the original pairing. -/
@[simp]
theorem completionBilinear_of (x : M) (y : N) :
    completionBilinear F G H f hf (F.of x) (G.of y) = H.of (f x y) := by
  apply H.completion_ext
  intro k
  simp

/-- The completed bilinear map adds filtration orders. -/
@[grind .]
theorem completionBilinear_mem_completedFiltration {a b : ℕ}
    {x : F.completion} {y : G.completion}
    (hx : x ∈ F.completedFiltration.submodule a)
    (hy : y ∈ G.completedFiltration.submodule b) :
    completionBilinear F G H f hf x y ∈ H.completedFiltration.submodule (a + b) := by
  cases hab : a + b with
  | zero => simp
  | succ k =>
    rw [completedFiltration_succ, LinearMap.mem_ker, projection_completionBilinear]
    obtain ⟨m, hm, he⟩ := F.exists_projection_eq_of_mem_completedFiltration
      (k := k) hx
    obtain ⟨n, hn, he'⟩ := G.exists_projection_eq_of_mem_completedFiltration
      (k := k) hy
    rw [← he, ← he', quotientBilinear_mk, Submodule.Quotient.mk_eq_zero]
    simpa only [hab] using hf a b hm hn

end Mei.ModuleFiltration
