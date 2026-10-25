/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Topology
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Polyhedral transverse sweeps

A normalized height functional gives an explicit continuous affine projection onto
its base hyperplane. A transverse sweep is the intersection of one closed affine
halfspace with the preimage of its base under this projection. Consequently finite
continuous affine inequalities remain finite continuous affine inequalities.

The argument allows unbounded sets and lineality. It does not use a claim that
arbitrary linear images of closed sets are closed.
-/

public section

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous normalized height proves polyhedrality directly, even without
finite dimensionality of the ambient space. -/
theorem isConvexPolyhedron_sweep_of_height {P : Set V} {n : V}
    (hP : TauCeti.IsConvexPolyhedron P) (f : V →L[ℝ] ℝ) (c : ℝ)
    (hn : f n = 1) (hfP : ∀ x ∈ P, f x = c) :
    TauCeti.IsConvexPolyhedron (sweep P n) := by
  rw [sweep_eq_halfspace_inter_preimage f c hn hfP]
  have hhalf : TauCeti.IsConvexPolyhedron {y : V | f y ≤ c} := by
    simpa only [ContinuousAffineMap.sub_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousAffineMap.coe_const, Function.const_apply, sub_nonpos] using
      TauCeti.isConvexPolyhedron_setOf_le
        (f.toContinuousAffineMap - ContinuousAffineMap.const ℝ V c)
  exact hhalf.inter (hP.preimage (sweepProjection f c n))

variable [FiniteDimensional ℝ V]

/-- Sweeping a convex polyhedron along a vector transverse to its affine direction
again gives a convex polyhedron. In particular its support is closed and convex.
The height functional is derived from transversality, rather than added as data. -/
theorem isConvexPolyhedron_sweep {P : Set V} {n : V}
    (hP : TauCeti.IsConvexPolyhedron P) (hn : n ∉ vectorSpan ℝ P) :
    TauCeti.IsConvexPolyhedron (sweep P n) := by
  rcases P.eq_empty_or_nonempty with h | hne
  · subst P
    simpa only [sweep_empty] using hP
  · obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height hne hn
    exact isConvexPolyhedron_sweep_of_height hP
      ⟨f, f.continuous_of_finiteDimensional⟩ c hfn hfP

end Mei.Convex
