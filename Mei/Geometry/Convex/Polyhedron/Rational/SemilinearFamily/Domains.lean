/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Basic

/-!
# Families of semilinear endpoint domains

A finite collection of rational semilinear subsets of one space defines a finite
semilinear family by inclusion. Its fiber records exactly the domains containing
the endpoint. Different indices remain distinct even when their domains coincide.
Every chart is a finite branch, by the decomposition of a semilinear set into
locally closed polyhedra.

These families turn endpoint domains with discrete labels into the same family
interface as general piecewise affine parameterizations.
-/

public noncomputable section

namespace Mei

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Inclusion of a rational semilinear set is a finite branch. -/
theorem IsRationalSemilinear.isFiniteBranchOn_subtypeVal {D : Set V}
    (hD : IsRationalSemilinear h D) :
    IsFiniteBranchOn h h D (Subtype.val : D → V) := by
  apply isFiniteBranchOn_iff.mpr
  obtain ⟨κ, hκ, S, hS, -, hcover⟩ :=
    isRationalSemilinear_iff_exists_pairwise_disjoint.mp hD
  exact ⟨κ, hκ, S, fun _ => AffineMap.id ℝ V, hcover,
    fun k => ⟨hS k, Toric.IsRationalLinearMap.id h,
      Function.injective_id.injOn, fun _ _ => rfl⟩⟩

namespace FiniteSemilinearFamily

variable [Finite ι] (D : ι → Set V) (hD : ∀ t, IsRationalSemilinear h (D t))

/-- The family whose charts are inclusions of the given endpoint domains. -/
def ofDomains : FiniteSemilinearFamily h h ι where
  domain := D
  eval _ := Subtype.val
  isRationalPiecewiseAffine t := (hD t).isFiniteBranchOn_subtypeVal.isRationalPiecewiseAffine

@[simp]
theorem ofDomains_domain (t : ι) : (ofDomains D hD).domain t = D t := (rfl)

@[simp]
theorem ofDomains_eval (t : ι) (x : (ofDomains D hD).domain t) :
    (ofDomains D hD).eval t x = x.val := (rfl)

/-- Each inclusion chart is a finite branch, even when its domain is not closed. -/
theorem isFiniteBranch_ofDomains : (ofDomains D hD).IsFiniteBranch :=
  (isFiniteBranch_iff _).mpr fun t => (hD t).isFiniteBranchOn_subtypeVal

/-- A fiber of the inclusion family records the indices of domains containing
the endpoint; there is no identification of coincident charts. -/
def fiberOfDomainsEquiv (Q : V) : (ofDomains D hD).fiber Q ≃ {t // Q ∈ D t} where
  toFun z := ⟨z.1, by
    have hxQ : z.2.1.val = Q := (ofDomains_eval D hD z.1 z.2.1).symm.trans z.2.2
    simpa only [ofDomains_domain, hxQ] using z.2.1.property⟩
  invFun z := ⟨z.val, ⟨Q, z.property⟩, ofDomains_eval D hD _ _⟩
  left_inv := by
    rintro ⟨t, x, hx⟩
    have hxQ : x.val = Q := (ofDomains_eval D hD t x).symm.trans hx
    cases x
    cases hxQ
    rfl
  right_inv _ := rfl

@[simp]
theorem fiberOfDomainsEquiv_apply_val (Q : V) (z : (ofDomains D hD).fiber Q) :
    (fiberOfDomainsEquiv D hD Q z).val = z.1 := (rfl)

@[simp]
theorem fiberOfDomainsEquiv_symm_apply_fst (Q : V) (z : {t // Q ∈ D t}) :
    ((fiberOfDomainsEquiv D hD Q).symm z).1 = z.val := (rfl)

instance (Q : V) : Finite ((ofDomains D hD).fiber Q) :=
  Finite.of_equiv _ (fiberOfDomainsEquiv D hD Q).symm

end FiniteSemilinearFamily

end Mei
