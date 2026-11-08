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

variable {D} {κ : ι → Type*} {B : ∀ t, κ t → Set V}
  (hdisj : ∀ t, Pairwise fun j l => Disjoint (B t j) (B t l))
  (hcover : ∀ t, ⋃ j, B t j = D t)

/-- A disjoint cover of every domain by chart pieces parameterizes the whole
inclusion family: a point of a piece is sent to its endpoint and chart label. -/
def ofDomainsChartEquiv : (Σ t, Σ j, B t j) ≃ Σ Q, (ofDomains D hD).fiber Q :=
  (Mei.sigmaDisjointCoverEquiv hdisj hcover).trans
    (Equiv.sigmaCongrRight fun Q => (fiberOfDomainsEquiv D hD Q).symm)

/-- The chart parameterization preserves the endpoint. -/
@[simp]
theorem ofDomainsChartEquiv_apply_fst (z : Σ t, Σ j, B t j) :
    (ofDomainsChartEquiv hD hdisj hcover z).1 = z.2.2.val := by
  simp only [ofDomainsChartEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Mei.sigmaDisjointCoverEquiv_apply_fst]

/-- The chart parameterization preserves the chart label. -/
@[simp]
theorem ofDomainsChartEquiv_apply_snd_fst (z : Σ t, Σ j, B t j) :
    (ofDomainsChartEquiv hD hdisj hcover z).2.1 = z.1 :=
  (fiberOfDomainsEquiv_symm_apply_fst D hD _ _).trans
    (Mei.sigmaDisjointCoverEquiv_apply_val hdisj hcover z)

variable (D)

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
  exact ⟨κ, hκ, B, hB, hdisj, hcover, ofDomainsChartEquiv hD hdisj hcover,
    ofDomainsChartEquiv_apply_fst hD hdisj hcover,
    ofDomainsChartEquiv_apply_snd_fst hD hdisj hcover⟩

end Mei.FiniteSemilinearFamily
