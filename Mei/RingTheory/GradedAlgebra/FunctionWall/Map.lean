/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.FunctionWall.Completion
public import Mei.RingTheory.FilteredAlgebra.Map

/-!
# Coefficient maps of completed function walls

A continuous ring map intertwines completed function-wall actions when its
finite quotient maps preserve normal weights and carry the source wall functions
to the target wall functions. The source and target scalar rings may differ,
and the cutoff modulus need not preserve orders. Coefficient quotients may make
wall actions trivial; neither injectivity nor separated filtrations are required.

The comparison uses `AlgFiltration.projection_mapCompletion` and the finite
`GradedAlgebra.map_functionWallAction`. It also identifies the image of the
completed wall unit itself. Thus coefficient specializations preserve both the
wall functions and the automorphisms they represent. The function-wall formula
is that of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.AlgFiltration

open Mei.GradedAlgebra

variable {R S A B : Type*} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
  (F : AlgFiltration A) (G : AlgFiltration B)
  (𝒜 : ∀ k : ℕ, ℤ → Submodule R (A ⧸ F.ideal (k + 1)))
  (ℬ : ∀ k : ℕ, ℤ → Submodule S (B ⧸ G.ideal (k + 1)))
  [∀ k, GradedAlgebra (𝒜 k)] [∀ k, GradedAlgebra (ℬ k)]
  (f : ∀ k, (𝒜 k 0)ˣ) (g : ∀ k, (ℬ k 0)ˣ)
  (hf : ∀ {k l : ℕ} (h : k ≤ l),
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (algebraMap (𝒜 l 0) _ (f l : 𝒜 l 0)) =
        algebraMap (𝒜 k 0) _ (f k : 𝒜 k 0))
  (hg : ∀ {k l : ℕ} (h : k ≤ l),
    Ideal.Quotient.factor (G.antitone (Nat.add_le_add_right h 1))
      (algebraMap (ℬ l 0) _ (g l : ℬ l 0)) =
        algebraMap (ℬ k 0) _ (g k : ℬ k 0))
  (φ : A →+* B) (l : ℕ → ℕ) (hl : Monotone l)
  (hφ : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap φ)
  (hfg : ∀ k, Ideal.quotientMap (G.ideal (k + 1)) φ (hφ k)
      (algebraMap (𝒜 (l k) 0) _ (f (l k) : 𝒜 (l k) 0)) =
        algebraMap (ℬ k 0) _ (g k : ℬ k 0))

include hfg in
/-- A continuous coefficient map carries compatible wall functions to the
completed target wall function. Weight preservation is not required for this
identity of units. -/
theorem mapCompletion_completedWallFunction :
    Units.map (F.mapCompletion G φ l hl hφ).toMonoidHom
        (F.completedWallFunction 𝒜 f hf) =
      G.completedWallFunction ℬ g hg := by
  apply Units.ext
  apply G.completion_ext
  intro k
  simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    projection_mapCompletion, projection_completedWallFunction] using hfg k

variable
  (h𝒜 : ∀ {k l : ℕ} (h : k ≤ l) {i : ℤ} {a : A ⧸ F.ideal (l + 1)},
    a ∈ 𝒜 l i →
      Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a ∈ 𝒜 k i)
  (hℬ : ∀ {k l : ℕ} (h : k ≤ l) {i : ℤ} {b : B ⧸ G.ideal (l + 1)},
    b ∈ ℬ l i →
      Ideal.Quotient.factor (G.antitone (Nat.add_le_add_right h 1)) b ∈ ℬ k i)
  (hgraded : ∀ k (i : ℤ) (a : A ⧸ F.ideal (l k + 1)), a ∈ 𝒜 (l k) i →
    Ideal.quotientMap (G.ideal (k + 1)) φ (hφ k) a ∈ ℬ k i)

include hfg hgraded in
/-- Continuous coefficient maps intertwine completed function walls. At target
order `k` only source order `l k` is used; the map may have a kernel and the two
algebras need not share a scalar ring. -/
theorem mapCompletion_completedFunctionWallAction (x : F.completion) :
    F.mapCompletion G φ l hl hφ (F.completedFunctionWallAction 𝒜 h𝒜 f hf x) =
      G.completedFunctionWallAction ℬ hℬ g hg (F.mapCompletion G φ l hl hφ x) := by
  apply G.completion_ext
  intro k
  let ψ : 𝒜 (l k) →+*ᵍ ℬ k :=
    { Ideal.quotientMap (G.ideal (k + 1)) φ (hφ k) with
      map_mem := fun {i a} ha => hgraded k i a ha }
  have hunit : Units.map ψ.gradedZeroRingHom.toMonoidHom (f (l k)) = g k := by
    apply Units.ext
    apply Subtype.ext
    exact hfg k
  rw [F.projection_mapCompletion, F.projection_completedFunctionWallAction,
    G.projection_completedFunctionWallAction, F.projection_mapCompletion]
  exact (map_functionWallAction (𝒜 (l k)) (ℬ k) ψ (f (l k))
    (F.projection (l k) x)).trans (congrArg
      (fun u => functionWallAction (ℬ k) u
        (Ideal.quotientMap (G.ideal (k + 1)) φ (hφ k) (F.projection (l k) x))) hunit)

end Mei.AlgFiltration
