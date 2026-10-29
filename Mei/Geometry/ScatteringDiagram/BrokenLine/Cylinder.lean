/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Product
public import Mei.Geometry.ScatteringDiagram.BrokenLine.AffineRay
public import Mei.Geometry.ScatteringDiagram.Incoming.Cylinder

/-!
# Incoming germs of lifted affine rays

For a nonzero projected incoming direction, the product of a projected ray and
a forgotten-coordinate history is admitted by the cylinder source precisely
when the original germ is admitted and the forgotten incoming direction is the
prescribed degree velocity. Together with coordinatewise evaluation, this gives
the incoming-source comparison for lifting affine paths through cylinders.
Coefficient histories and their propagation are additional data.

The cylinder comparison follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter

namespace Mei.FiniteAffineRay

variable {Γ V W R E : Type*} [AddCommMonoid Γ] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [Semiring R] [AddCommMonoid E] [Module R E]
  {M : Γ → Type*} [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  {v : Γ →+ V} (S : AffineIncomingSource R E M v) (w : Γ →+ W)

/-- Lifting a ray preserves incoming-tail admission exactly when the forgotten
incoming velocity agrees. The nonzero projected source direction ensures that
both admission notions refer to nonstationary incoming tails. -/
theorem exists_incomingTail_prod_iff (β : FiniteAffineRay V V) (γ : FiniteAffineRay W W)
    (a : E) (hv : v S.degree ≠ 0) :
    (∃ τ : AffineIncomingTail (S.cylinder w) a,
      (β.prod γ : ℝ → V × W) =ᶠ[atBot] τ) ↔
      (∃ τ : AffineIncomingTail S a, (β : ℝ → V) =ᶠ[atBot] τ) ∧
        γ.incomingDirection = w S.degree := by
  have hpair : (v.prod w) S.degree ≠ 0 := fun h => hv (congrArg Prod.fst h)
  simp only [exists_incomingTail_iff, ne_eq,
    AffineIncomingSource.cylinder_coefficient_eq_zero_iff,
    AffineIncomingSource.cylinder_degree, AffineIncomingSource.endpoints_cylinder,
    incomingDirection_prod, incomingReference_prod, AddMonoidHom.prod_apply,
    Prod.mk.injEq, mem_prod, mem_univ, and_true]
  tauto

end Mei.FiniteAffineRay
