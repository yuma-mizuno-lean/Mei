/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Completed
public import Mei.Algebra.QuantumMonoidAlgebra.Completion
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Map

/-!
# Scalar-change naturality of completed quantum rays

Simultaneous coefficient and exponent maps commute with completed evaluation on
positive quantum rays, and hence with quantum dilogarithms when their parameter
is preserved. The coefficient rings may differ, the exponent map may merge
exponents, and the coefficient monoids need only have nonnegative degrees.

We reuse `positiveMap`, the generic completion map, scalar-change naturality of
completed power series evaluation, and the scalar quantum dilogarithm map law.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (φ : R →+* S) (f : Γ →+ Γ')
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
  (P : AddSubmonoid Γ) (P' : AddSubmonoid Γ') (hP : ∀ n ∈ P, f n ∈ P')
  (δ : Γ →+ ℤ) (δ' : Γ' →+ ℤ)
  (hδ : ∀ n ∈ P, 0 ≤ δ n) (hδ' : ∀ n ∈ P', 0 ≤ δ' n)

local notation "F" => positiveFiltration q β P δ hδ
local notation "G" => positiveFiltration q' β' P' δ' hδ'
local notation "ψ" => positiveMap φ f h P P' hP

variable (l : ℕ → ℕ) (hl : Monotone l)
  (hcut : ∀ k n, n ∈ P → (l k : ℤ) < δ n → (k : ℤ) < δ' (f n))

local notation "Ψ" => mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut

private theorem mapPositiveCompletionOfDegree_eq_generic :
    Ψ = (F).mapCompletion G ψ l hl
      (fun k => positiveMap_ideal_le_of_degree φ f h P P' hP δ δ' hδ hδ' (l k + 1) (k + 1)
        (fun n hn hd => by have := hcut k n hn (by omega); omega)) := by
  apply RingHom.ext
  intro x
  apply (G).completion_ext
  intro k
  have h₁ := projection_mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut k x
  have h₂ := (F).projection_mapCompletion G ψ l hl
    (fun k => positiveMap_ideal_le_of_degree φ f h P P' hP δ δ' hδ hδ' (l k + 1) (k + 1)
      (fun n hn hd => by have := hcut k n hn (by omega); omega)) k x
  exact h₁.trans h₂.symm

/-- The completed quantum map sends a ray generator to its image ray generator. -/
theorem mapPositiveCompletionOfDegree_completedRayGenerator (n : P) (hn : 0 < δ n)
    (hn' : 0 < δ' (f n)) :
    Ψ (completedRayGenerator q β P δ hδ n hn : (F).completion) =
      (completedRayGenerator q' β' P' δ' hδ' ⟨f n, hP n n.property⟩ hn' : (G).completion) := by
  simp only [coe_completedRayGenerator, mapPositiveCompletionOfDegree_toCompletion,
    positiveMap_positiveMonomial]

variable (hpos : ∀ n ∈ P, 0 < δ n → 0 < δ' (f n))

/-- Arbitrary scalar series evaluated on completed quantum rays commute with scalar
and exponent transport. Positive degree preservation supplies first-ideal preservation. -/
theorem mapPositiveCompletionOfDegree_completedRayAeval (n : P) (hn : 0 < δ n)
    (H : PowerSeries R) :
    Ψ ((F).completedAeval (completedRayGenerator q β P δ hδ n hn) H) =
      (G).completedAeval
        (completedRayGenerator q' β' P' δ' hδ' ⟨f n, hP n n.property⟩
          (hpos n n.property hn)) (PowerSeries.map φ H) := by
  have h₁ : (F).ideal 1 ≤ ((G).ideal 1).comap ψ :=
    positiveMap_ideal_le_of_degree φ f h P P' hP δ δ' hδ hδ' 1 1
      (fun n hn hd => by have := hpos n hn (by omega); omega)
  exact (F).mapCompletion_completedAeval_of_eq G φ ψ (positiveMap_algebraMap φ f h P P' hP)
    l hl (fun k => positiveMap_ideal_le_of_degree φ f h P P' hP δ δ' hδ hδ' (l k + 1) (k + 1)
      (fun n hn hd => by have := hcut k n hn (by omega); omega)) h₁ Ψ
    (mapPositiveCompletionOfDegree_eq_generic φ f h P P' hP δ δ' hδ hδ' l hl hcut)
    (completedRayGenerator q β P δ hδ n hn)
    (completedRayGenerator q' β' P' δ' hδ' ⟨f n, hP n n.property⟩ (hpos n n.property hn))
    (mapPositiveCompletionOfDegree_completedRayGenerator φ f h P P' hP δ δ' hδ hδ' l hl hcut
      n hn (hpos n n.property hn)) H

/-- Completed quantum dilogarithms are natural under scalar specialization and
compatible exponent maps. The denominator hypotheses remain exactly those of the
scalar dilogarithms. -/
theorem mapPositiveCompletionOfDegree_completedRayQuantumDilogarithm
    (hq : ∀ j : ℕ, IsUnit ((q : R) ^ (j + 1) - (↑q⁻¹ : R) ^ (j + 1)))
    (hq' : ∀ j : ℕ, IsUnit ((q' : S) ^ (j + 1) - (↑q'⁻¹ : S) ^ (j + 1)))
    (hparam : Units.map φ.toMonoidHom q = q') (n : P) (hn : 0 < δ n) :
    Ψ ((F).completedAeval (completedRayGenerator q β P δ hδ n hn)
      (q.quantumDilogarithm hq)) =
      (G).completedAeval
        (completedRayGenerator q' β' P' δ' hδ' ⟨f n, hP n n.property⟩
          (hpos n n.property hn)) (q'.quantumDilogarithm hq') := by
  have hd : PowerSeries.map φ (q.quantumDilogarithm hq) = q'.quantumDilogarithm hq' := by
    subst q'
    exact q.map_quantumDilogarithm hq φ
  exact (mapPositiveCompletionOfDegree_completedRayAeval φ f h P P' hP δ δ' hδ hδ' l hl hcut
    hpos n hn (q.quantumDilogarithm hq)).trans (congrArg _ hd)

end Mei.QuantumMonoidAlgebra
