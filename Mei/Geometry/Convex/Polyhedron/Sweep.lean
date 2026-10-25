/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Polyhedral transverse sweeps

A normalized height functional gives an explicit continuous affine projection onto
its base hyperplane. A transverse sweep is the intersection of one closed affine
halfspace with the preimage of its base under this projection. Consequently finite
continuous affine inequalities remain finite continuous affine inequalities.

The argument allows unbounded sets and lineality. It does not use a claim that
arbitrary linear images of closed sets are closed.

This supplies the closed convex polyhedral support part of
[ScatteringDiagrams §1.4](https://github.com/yuma-mizuno/TauCetiRoadmap/blob/mei/TauCetiRoadmap/ScatteringDiagrams/README.md#14-polyhedral-cochains-and-sweeps).
Rational-normal presentations and oriented polyhedral cochains are separate constructions.
-/

public section

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The affine projection recovering the base point of a transverse sweep.
When `f n = 1`, its image lies in the hyperplane `f x = c`. -/
def sweepProjection (f : V →L[ℝ] ℝ) (c : ℝ) (n : V) : V →ᴬ[ℝ] V :=
  (ContinuousLinearMap.id ℝ V - f.smulRight n).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ V (c • n)

/-- The projection adds the unique correction along the sweeping vector. -/
@[simp]
theorem sweepProjection_apply (f : V →L[ℝ] ℝ) (c : ℝ) (n y : V) :
    sweepProjection f c n y = y + (c - f y) • n := by
  change y - f y • n + c • n = _
  module

/-- The recovered base point has the required height. -/
theorem sweepProjection_height (f : V →L[ℝ] ℝ) (c : ℝ) {n : V}
    (hn : f n = 1) (y : V) :
    f (sweepProjection f c n y) = c := by
  simp [hn]

/-- The sweep projection fixes the base hyperplane. -/
theorem sweepProjection_eq_self (f : V →L[ℝ] ℝ) (c : ℝ) {n y : V}
    (hy : f y = c) : sweepProjection f c n y = y := by
  simp [hy]

/-- The explicit projection presents the sweep as a halfspace intersected with
an affine preimage, with no boundedness hypothesis on the base. -/
theorem sweep_eq_halfspace_inter_preimage {P : Set V} {n : V}
    (f : V →L[ℝ] ℝ) (c : ℝ) (hn : f n = 1)
    (hP : ∀ x ∈ P, f x = c) :
    sweep P n = {y | f y ≤ c} ∩ sweepProjection f c n ⁻¹' P := by
  ext y
  simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
    sweepProjection_apply, ContinuousLinearMap.coe_coe] using
    (mem_sweep_iff f.toLinearMap c hn hP (y := y))

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

/-- Sweeping an entire transverse affine hyperplane produces its closed negative
halfspace. In particular no boundedness or absence of lineality is required. -/
theorem sweep_hyperplane (f : V →L[ℝ] ℝ) (c : ℝ) {n : V} (hn : f n = 1) :
    sweep {x : V | f x = c} n = {x : V | f x ≤ c} := by
  rw [sweep_eq_halfspace_inter_preimage f c hn (fun _ hx => hx)]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  exact and_iff_left (sweepProjection_height f c hn y)

variable [FiniteDimensional ℝ V]

/-- Sweeping a convex polyhedron along a vector transverse to its affine direction
again gives a convex polyhedron. In particular its support is closed and convex.
The height functional is derived from transversality, rather than added as data. -/
theorem isConvexPolyhedron_sweep {P : Set V} {n : V}
    (hP : TauCeti.IsConvexPolyhedron P) (hn : n ∉ vectorSpan ℝ P) :
    TauCeti.IsConvexPolyhedron (sweep P n) := by
  rcases P.eq_empty_or_nonempty with h | hne
  · subst P
    have hEmpty : TauCeti.IsConvexPolyhedron (∅ : Set V) := by
      have he : {x : V | (ContinuousAffineMap.const ℝ V (1 : ℝ)) x ≤ 0} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hx
      rw [← he]
      exact TauCeti.isConvexPolyhedron_setOf_le (ContinuousAffineMap.const ℝ V (1 : ℝ))
    simpa [sweep] using hEmpty
  · obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height hne hn
    exact isConvexPolyhedron_sweep_of_height hP
      ⟨f, f.continuous_of_finiteDimensional⟩ c hfn hfP

/-- An unbounded base with lineality: the horizontal axis sweeps to the closed
lower half-plane under the positive vertical sweeping vector. -/
theorem sweep_horizontal_axis :
    sweep {p : ℝ × ℝ | p.2 = 0} (0, 1) = {p : ℝ × ℝ | p.2 ≤ 0} :=
  sweep_hyperplane (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 rfl

end Mei.Convex
