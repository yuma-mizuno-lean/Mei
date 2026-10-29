/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Incoming.Affine

/-!
# Cylinder sources for incoming tails

Adding unrestricted coordinates to an incoming source preserves its admission
condition on reference positions. The additional velocity is specified by an
additive map on degrees; it need not vanish or be injective. Coefficients and
incoming data are retained. This is the source geometry for lifting affine paths
through cylinder walls, as in Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set

namespace Mei.AffineIncomingSource

variable {Γ V W R E : Type*} [AddCommMonoid Γ] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [Semiring R] [AddCommMonoid E] [Module R E]
  {M : Γ → Type*} [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  {v : Γ →+ V} (S : AffineIncomingSource R E M v) (w : Γ →+ W)

/-- Extend a source to a cylinder, prescribing the additional degree velocities. -/
def cylinder : AffineIncomingSource R E M (v.prod w) where
  carrier := S.carrier ×ˢ univ
  degree := S.degree
  coefficient := S.coefficient
  direction_mem_recession := by
    rw [mem_recessionCone]
    intro x hx t ht
    exact ⟨(mem_recessionCone.mp S.direction_mem_recession) x.1 hx.1 t ht, mem_univ _⟩

@[simp]
theorem cylinder_carrier : (S.cylinder w).carrier = S.carrier ×ˢ univ := (rfl)

@[simp]
theorem cylinder_degree : (S.cylinder w).degree = S.degree := (rfl)

/-- Coefficients are unchanged after transporting their degree index. -/
@[simp]
theorem cylinder_coefficient (a : E) :
    cast (congrArg M (S.cylinder_degree w)) ((S.cylinder w).coefficient a) =
      S.coefficient a := (rfl)

/-- A cylinder source deletes exactly the same zero input coefficients. -/
@[simp]
theorem cylinder_coefficient_eq_zero_iff (a : E) :
    (S.cylinder w).coefficient a = 0 ↔ S.coefficient a = 0 := (Iff.rfl)

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]

/-- Admission of an incoming affine line to a cylinder is determined precisely by
its projected line. The unrestricted coordinate imposes no reference constraint. -/
@[simp]
theorem endpoints_cylinder : (S.cylinder w).endpoints = S.endpoints ×ˢ univ := by
  ext x
  simp [mem_endpoints_iff]

end Mei.AffineIncomingSource
