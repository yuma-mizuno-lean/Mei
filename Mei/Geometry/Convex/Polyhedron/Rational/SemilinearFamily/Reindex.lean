/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Evaluation

/-!
# Reindexing finite semilinear families

An equivalence of chart labels reindexes a semilinear family without changing
its chart domains, parameter points or evaluation maps. The induced fiber
bijection retains chart multiplicities and weighted evaluation. This lets a
comparison of geometric families use a proved equivalence of complete labels
without reconstructing their polyhedral charts.
-/

public section

namespace Mei.FiniteSemilinearFamily

variable {N V N' W ι κ μ : Type*}
  [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [AddCommGroup W] [Module ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  [Finite ι] [Finite κ] [Finite μ] (F : FiniteSemilinearFamily h h' ι) (e : κ ≃ ι)

/-- Rename the chart labels by an equivalence, retaining each full chart. -/
def reindex : FiniteSemilinearFamily h h' κ where
  domain c := F.domain (e c)
  eval c := F.eval (e c)
  isRationalPiecewiseAffine c := F.isRationalPiecewiseAffine (e c)

@[simp]
theorem reindex_domain (c : κ) : (F.reindex e).domain c = F.domain (e c) := (rfl)

@[simp]
theorem reindex_eval (c : κ) (x : (F.reindex e).domain c) :
    (F.reindex e).eval c x =
      F.eval (e c) ⟨x.val, by simpa only [reindex_domain] using x.property⟩ := (rfl)

@[simp]
theorem reindex_refl : F.reindex (Equiv.refl ι) = F := by ext <;> rfl

/-- Successive changes of chart labels compose in the order of substitution. -/
@[simp]
theorem reindex_reindex (d : μ ≃ κ) : (F.reindex e).reindex d = F.reindex (d.trans e) :=
  by ext <;> rfl

/-- Reindexing retains the actual parameter point in each endpoint fiber. -/
def fiberReindexEquiv (Q : W) : (F.reindex e).fiber Q ≃ F.fiber Q := by
  unfold fiber reindex
  exact Equiv.sigmaCongrLeft (β := fun c => {x : F.domain c // F.eval c x = Q}) e

@[simp]
theorem fiberReindexEquiv_label (Q : W) (z : (F.reindex e).fiber Q) :
    (F.fiberReindexEquiv e Q z).1 = e z.1 := (rfl)

@[simp]
theorem fiberReindexEquiv_point (Q : W) (z : (F.reindex e).fiber Q) :
    (F.fiberReindexEquiv e Q z).2.1.val = z.2.1.val := (rfl)

instance (Q : W) [Finite (F.fiber Q)] : Finite ((F.reindex e).fiber Q) :=
  Finite.of_equiv _ (F.fiberReindexEquiv e Q).symm

/-- Being a finite branch is independent of chart names. -/
@[simp]
theorem isFiniteBranch_reindex_iff : (F.reindex e).IsFiniteBranch ↔ F.IsFiniteBranch := by
  simp only [isFiniteBranch_iff, reindex]
  exact e.forall_congr_right (q := fun c =>
    IsFiniteBranchOn h h' (F.domain c) (F.eval c))

/-- Renaming chart labels and their weights preserves the fiber sum. -/
@[simp]
theorem weightedEvaluation_reindex {M : Type*} [AddCommMonoid M]
    (weight : ι → M) (Q : W) [Finite (F.fiber Q)] :
    (F.reindex e).weightedEvaluation (weight ∘ e) Q = F.weightedEvaluation weight Q := by
  let := Fintype.ofFinite ((F.reindex e).fiber Q)
  let := Fintype.ofFinite (F.fiber Q)
  simp only [weightedEvaluation_def]
  exact Fintype.sum_equiv (F.fiberReindexEquiv e Q) _ _
    (fun _ => by simp only [Function.comp_apply, fiberReindexEquiv_label])

end Mei.FiniteSemilinearFamily
