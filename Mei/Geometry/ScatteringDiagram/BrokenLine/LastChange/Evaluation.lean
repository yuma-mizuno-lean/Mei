/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.LinearAlgebra.GradedModule.History.LastChange

/-!
# Weighted ray sums indexed by the last degree change

Partition the actual decorated admissible rays of a fixed signed encounter
itinerary into constant-degree rays and rays with a specified last degree change.
The latter contribute the whole component of their actual incoming decoration at
that encounter. All later encounters preserve the decoration. The full geometric
admission conditions and every recorded encounter remain in the fiber; equal
spatial velocities do not erase a degree change.

This is the coefficient partition for a last-change recursion. It does not yet
identify the incoming pieces with rays ending at perturbed incoming germs.
The construction applies `homogeneousHistory_eq_add_sum_last_degree_change` to
`decoratedRayEvaluation`. The broken-line recursion follows Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {velocity : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V} {W : J → Set V}
  {S : K → Set V} {C : Set V} {Q : V}

open Classical in
/-- Sum the constant-degree contributions and the whole component at each ray's
unique last degree change. The inner sum is over actual admissible rays, so all
wall, singular and source conditions are retained. No genericity, finite grading
or nonzero spatial velocity hypothesis is needed. -/
theorem decoratedRayEvaluation_eq_add_sum_last_degree_change
    (hT : ∀ j s x, x ∈ ℳ s → (DirectSum.decompose ℳ (T j x) s : M) = x) :
    decoratedRayEvaluation ℳ T p₀ a velocity f c ε P W S C Q =
      let := Fintype.ofFinite
        (DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
      (∑ r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q,
        if ∀ j, r.1.val j = Fin.snoc (α := fun _ => Γ) r.1.val p₀ j.succ
        then (a : M) else 0) +
      ∑ j : Fin n, ∑ r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q,
        if r.1.val j ≠ Fin.snoc (α := fun _ => Γ) r.1.val p₀ j.succ ∧
            ∀ i, i < j → r.1.val i = Fin.snoc (α := fun _ => Γ) r.1.val p₀ i.succ
        then (DirectSum.decompose ℳ (T j (r.decoration j.succ)) (r.1.val j) : M)
        else 0 := by
  classical
  let := Fintype.ofFinite
    (DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
  rw [decoratedRayEvaluation_def]
  simp_rw [DecoratedAdmissibleRay.decoration_zero,
    homogeneousHistory_eq_add_sum_last_degree_change hT _ a]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [DecoratedAdmissibleRay.decoration_def]

end Mei
