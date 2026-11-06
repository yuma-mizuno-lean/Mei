/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Domains
public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification
public import Mei.Data.Set.DisjointCover

/-!
# Closed polyhedral charts for families of endpoint domains

An inclusion family has a finite parameterization by relative interiors of
closed rational-normal polyhedra. The parameterization is an equivalence onto
the whole family, preserving its endpoint and chart label. Each closed chart
adds only limiting endpoints of its original domain. Coincident domains with
different labels retain their multiplicities.

This assembles `IsRationalSemilinear.exists_disjoint_intrinsicInteriors` using
Mathlib's `Set.unionEqSigmaOfDisjoint`. In applications a label can record a
complete path history, whose geometric extension is then evaluated on these
same closed charts.
-/

public noncomputable section

open Set

namespace Mei.FiniteSemilinearFamily

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite ι]
  (D : ι → Set V) (hD : ∀ t, IsRationalSemilinear h (D t))

/-- Subdividing inclusion domains gives finite closed charts whose relative
interiors parameterize the entire family exactly, with its original labels.
Boundary points are limits and need not belong to the original domain. -/
theorem exists_ofDomains_polyhedralCharts :
    ∃ (κ : ι → Type) (_ : ∀ t, Finite (κ t)) (B : ∀ t, κ t → Set V),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧ B t j ⊆ closure (D t)) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = D t) ∧
      ∃ e : (Σ t, Σ j : κ t, intrinsicInterior ℝ (B t j)) ≃
          (Σ Q, (ofDomains D hD).fiber Q),
        (∀ z, (e z).1 = z.2.2.val) ∧ ∀ z, (e z).2.1 = z.1 := by
  classical
  choose κ hκ B hB hdisj hcover using fun t => (hD t).exists_disjoint_intrinsicInteriors
  let e := (Set.sigmaDisjointCoverEquiv hdisj hcover).trans
    (Equiv.sigmaCongrRight fun Q => (fiberOfDomainsEquiv D hD Q).symm)
  have hendpoint (z) : (e z).1 = z.2.2.val := by
    simp only [e, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
      Set.sigmaDisjointCoverEquiv_apply_fst]
  have hlabel (z) : (e z).2.1 = z.1 := by
    calc
      (e z).2.1 = (Set.sigmaDisjointCoverEquiv hdisj hcover z).2.val :=
        fiberOfDomainsEquiv_symm_apply_fst D hD _ _
      _ = z.1 := Set.sigmaDisjointCoverEquiv_apply_val hdisj hcover z
  exact ⟨κ, hκ, B, hB, hdisj, hcover, e, hendpoint, hlabel⟩

end Mei.FiniteSemilinearFamily
