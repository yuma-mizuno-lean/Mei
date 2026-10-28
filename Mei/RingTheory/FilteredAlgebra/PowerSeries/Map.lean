/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Basic
public import Mei.RingTheory.FilteredAlgebra.Map
public import Mei.RingTheory.PowerSeries.Nilpotent.Map

/-!
# Scalar-change naturality of completed power-series evaluation

Compatible ring maps on scalars and coefficients commute with evaluating arbitrary
power series at elements of the first completed ideal. The cutoff modulus is
arbitrary; preservation of the first ideal is retained as a separate hypothesis.
No injectivity, separatedness, rational scalar structure, or commutativity of the
coefficient algebras is assumed.
-/

public section

namespace Mei.AlgFiltration

variable {R S A B : Type*} [CommRing R] [CommRing S] [Ring A] [Ring B]
  [Algebra R A] [Algebra S B]
  (F : AlgFiltration A) (G : AlgFiltration B)
  (φ : R →+* S) (ψ : A →+* B)
  (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r))
  (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap ψ)
  (h₁ : F.ideal 1 ≤ (G.ideal 1).comap ψ)

include hψ in
/-- Completed evaluation is natural under simultaneous scalar and coefficient maps. -/
theorem mapCompletion_completedAeval (x : F.completionIdeal 1) (f : PowerSeries R) :
    F.mapCompletion G ψ l hl hf (F.completedAeval x f) =
      G.completedAeval ⟨F.mapCompletion G ψ l hl hf x,
        F.mapCompletion_mem_first G ψ l hl hf h₁ x.property⟩
        (PowerSeries.map φ f) := by
  apply G.completion_ext
  intro k
  rw [projection_mapCompletion, projection_completedAeval, projection_completedAeval]
  have hq : ∀ r, Ideal.quotientMap (G.ideal (k + 1)) ψ (hf k)
      (algebraMap R (A ⧸ F.ideal (l k + 1)) r) =
        algebraMap S (B ⧸ G.ideal (k + 1)) (φ r) := by
    intro r
    rw [Ideal.quotientMap_algebraMap, hψ, Ideal.Quotient.mk_algebraMap]
  rw [f.map_nilpotentAeval_map φ _ hq]
  simp only [projection_mapCompletion]

end Mei.AlgFiltration
