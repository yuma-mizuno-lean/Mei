/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Stratification
public import Mei.Geometry.Convex.Polyhedron.Rational.Generic
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Generic stability of finite-branch fibers

A finite semilinear family of finite branches has a finite exceptional arrangement
outside which nearby fibers are in bijection, preserving chart labels. The domain
points may move with the endpoint; distinct domain points of one chart and points
of different charts with the same image remain distinct fiber points. Neither closed
domains nor proper evaluation maps are required.

The construction uses a branch stratification and the common membership arrangement
of its target strata. It upgrades the stratumwise cardinality formula to stability of
the actual fibers. Consequently fiber cardinalities and sums of chart-constant weights
are locally constant on the generic locus.

This combines `BranchStratification.exists_fiberEquiv_of_mem_target` with
`IsRationalSemilinear.exists_membershipArrangement`; no topology on the fibers or
continuity of the chosen bijections is asserted.
-/

public section

open Set Filter Topology

namespace Mei.FiniteSemilinearFamily

variable {N V N' W : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {ι : Type*} [Finite ι] {F : FiniteSemilinearFamily h h' ι}

namespace BranchStratification

/-- The frontiers of a finite target stratification lie in one exceptional arrangement.
At every generic endpoint, nearby fibers are in bijection with its fiber, preserving
chart labels. The source stratification need not have finitely many strata. -/
theorem exists_fiberEquivArrangement {κ μ : Type*} [Finite κ]
    (S : F.BranchStratification κ μ) :
    ∃ E : ExceptionalArrangement W,
      (∀ b, frontier (S.target b) ⊆ {w | ¬ E.IsGeneric w}) ∧
        ∀ w, E.IsGeneric w → ∀ᶠ w' in 𝓝 w,
          ∃ e : F.fiber w ≃ F.fiber w', ∀ x, (e x).1 = x.1 := by
  obtain ⟨E, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement
    (fun b => (S.isLocallyClosedPolyhedron_target b).isRationalSemilinear)
  refine ⟨E, hfrontier, fun w hw => ?_⟩
  obtain ⟨b, hb⟩ := mem_iUnion.mp (S.iUnion_target ▸ mem_univ w)
  exact (hstable w hw).mono fun w' hw' =>
    S.exists_fiberEquiv_of_mem_target hb ((hw' b).mpr hb)

end BranchStratification

namespace IsFiniteBranch

/-- Off a finite exceptional arrangement, the actual fibers of a finite-branch
family are locally in bijection, preserving the chart label of each fiber point. -/
theorem exists_fiberEquivArrangement (hF : F.IsFiniteBranch) :
    ∃ E : ExceptionalArrangement W,
      ∀ w, E.IsGeneric w → ∀ᶠ w' in 𝓝 w,
        ∃ e : F.fiber w ≃ F.fiber w', ∀ x, (e x).1 = x.1 := by
  obtain ⟨κ, μ, _, _, ⟨S⟩⟩ := hF.exists_branchStratification
  obtain ⟨E, -, hE⟩ := S.exists_fiberEquivArrangement
  exact ⟨E, hE⟩

/-- The fiber cardinality of a finite-branch family is locally constant away from
one finite exceptional arrangement, including for nonclosed branch domains. -/
theorem exists_isLocallyConstant_nat_card_fiber (hF : F.IsFiniteBranch) :
    ∃ E : ExceptionalArrangement W,
      IsLocallyConstant (fun w : {w // E.IsGeneric w} => Nat.card (F.fiber w.val)) := by
  obtain ⟨E, hE⟩ := hF.exists_fiberEquivArrangement
  refine ⟨E, Set.isLocallyConstant_domRestrict_of_eventually_eq
    {w | E.IsGeneric w} (f := fun w => Nat.card (F.fiber w)) fun w hw => ?_⟩
  exact (hE w hw).mono fun w' hw' => by
    obtain ⟨e, -⟩ := hw'
    exact (Nat.card_congr e).symm

/-- One exceptional arrangement works for all chart-constant weights in any additive
commutative monoid. Nearby fibers retain their labels, so their finite weighted sums
are locally constant. Zero weights and coincident branch images are permitted. -/
theorem exists_isLocallyConstant_finsum_fiber (hF : F.IsFiniteBranch) :
    ∃ E : ExceptionalArrangement W,
      ∀ {A : Type*} [AddCommMonoid A] (weight : ι → A),
        IsLocallyConstant (fun w : {w // E.IsGeneric w} =>
          ∑ᶠ x : F.fiber w.val, weight x.1) := by
  obtain ⟨E, hE⟩ := hF.exists_fiberEquivArrangement
  refine ⟨E, fun {A} _ weight =>
    Set.isLocallyConstant_domRestrict_of_eventually_eq {w | E.IsGeneric w}
      (f := fun w => ∑ᶠ x : F.fiber w, weight x.1) fun w hw => ?_⟩
  exact (hE w hw).mono fun w' hw' => by
    obtain ⟨e, he⟩ := hw'
    exact (finsum_eq_of_bijective e e.bijective fun x => congrArg weight (he x).symm).symm

end IsFiniteBranch

end Mei.FiniteSemilinearFamily
