/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Basic
public import Mei.Geometry.ScatteringDiagram.Incoming.Affine

/-!
# Admitted incoming germs of finite affine rays

A finitely bent affine ray has the germ of an existing `AffineIncomingTail`
exactly when its incoming direction and affine reference position agree with
that tail. For a source and incoming datum this gives an admission criterion:
the source coefficient and direction are nonzero, the directions agree, and
the incoming affine line meets the source carrier.

When admitted, the source tail is unique, and the bent half-line is proper.
This supplies the incoming geometric condition for affine broken lines;
wall encounters and homogeneous coefficient propagation remain separate data.
The source, recession and coefficient conventions are those of the existing
incoming-tail construction.
-/

public section

open Set Filter

namespace Mei.FiniteAffineRay

variable {Γ V R E : Type*} [AddCommMonoid Γ] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [Semiring R] [AddCommMonoid E] [Module R E]
  {M : Γ → Type*} [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  {v : Γ →+ V} {S : AffineIncomingSource R E M v} {a : E}

/-- A finite ray matches an admitted tail precisely when their incoming direction
and reference position agree. Finite bends do not alter this germ criterion. -/
theorem eventuallyEq_incomingTail_iff (β : FiniteAffineRay V V) (γ : AffineIncomingTail S a) :
    (β : ℝ → V) =ᶠ[atBot] γ ↔
      β.incomingDirection = v S.degree ∧ β.incomingReference = γ 0 := by
  constructor
  · intro h
    have hline : β.incomingLine.toAffineMap = γ.representative.toAffineMap :=
      AffineMap.eq_of_eventuallyEq_atBot (β.eventuallyEq_incomingLine.symm.trans h)
    have hc := ContinuousAffineMap.toAffineMap_injective hline
    constructor
    · have hv := congrArg (fun f : ℝ →ᴬ[ℝ] V => f.linear 1) hc
      rw [incomingLine_velocity, γ.velocity] at hv
      exact neg_injective hv
    · have hQ := congrArg (fun f : ℝ →ᴬ[ℝ] V => f 0) hc
      simpa only [incomingLine_apply, neg_zero, zero_smul, zero_vadd] using hQ
  · rintro ⟨hv, hQ⟩
    filter_upwards [β.eventuallyEq_incomingLine] with t ht
    rw [ht, incomingLine_apply, hv, hQ, γ.apply_eq t]
    simp only [vadd_eq_add, sub_eq_add_neg, neg_smul, add_comm]

/-- A finite ray admits the source's incoming datum precisely when its incoming
affine line is admitted, with a nonzero source coefficient and direction. -/
theorem exists_incomingTail_iff (β : FiniteAffineRay V V) (S : AffineIncomingSource R E M v)
    (a : E) :
    (∃ γ : AffineIncomingTail S a, (β : ℝ → V) =ᶠ[atBot] γ) ↔
      S.coefficient a ≠ 0 ∧ v S.degree ≠ 0 ∧
        β.incomingDirection = v S.degree ∧ β.incomingReference ∈ S.endpoints := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨hv, hQ⟩ := (β.eventuallyEq_incomingTail_iff γ).mp hγ
    refine ⟨γ.coefficient_ne_zero, γ.direction_ne_zero, hv, ?_⟩
    rw [hQ]
    exact S.mem_endpoints γ
  · rintro ⟨ha, hv, hd, hQ⟩
    let γ := S.tailAt ha hv ⟨β.incomingReference, hQ⟩
    refine ⟨γ, (β.eventuallyEq_incomingTail_iff γ).mpr ⟨hd, ?_⟩⟩
    exact (S.tailAt_apply_zero ha hv ⟨β.incomingReference, hQ⟩).symm

/-- An admitted finite ray has exactly one incoming tail at its source and datum. -/
theorem existsUnique_incomingTail (β : FiniteAffineRay V V)
    (S : AffineIncomingSource R E M v) (a : E)
    (ha : S.coefficient a ≠ 0) (hv : v S.degree ≠ 0)
    (hd : β.incomingDirection = v S.degree) (hQ : β.incomingReference ∈ S.endpoints) :
    ∃! γ : AffineIncomingTail S a, (β : ℝ → V) =ᶠ[atBot] γ := by
  obtain ⟨γ, hγ⟩ := (β.exists_incomingTail_iff S a).mpr ⟨ha, hv, hd, hQ⟩
  refine ⟨γ, hγ, ?_⟩
  intro γ' hγ'
  apply AffineIncomingTail.germ_eq_iff.mp
  rw [γ'.germ_eq_ofFun, γ.germ_eq_ofFun]
  exact (hγ'.symm.trans hγ).germ_eq

/-- Admission by a nonzero incoming tail makes every closed half-line of the bent
ray proper; no restriction on the intermediate velocities is needed. -/
theorem isProperMap_restrict_Iic_of_incomingTail [T2Space V] (β : FiniteAffineRay V V)
    (γ : AffineIncomingTail S a) (hγ : (β : ℝ → V) =ᶠ[atBot] γ) (b : ℝ) :
    IsProperMap (fun t : Iic b => β t) := by
  apply β.isProperMap_restrict_Iic _ b
  rw [((β.eventuallyEq_incomingTail_iff γ).mp hγ).1]
  exact γ.direction_ne_zero

end Mei.FiniteAffineRay
