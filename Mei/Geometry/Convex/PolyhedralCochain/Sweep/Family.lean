/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Boundary

/-!
# Sweeping finite families of closed components

A finite presentation may have different sweeping directions on its different
components. If each component is closed, the signed boundary of the sum of
its sweeps is the negative of the entire source cochain. Components are indexed
independently of their directions: distinct components may have the same direction.
This permits homogeneous obstruction components to be swept simultaneously.

The result assembles `coboundaryOfFinsupp_sum_sweep_of_coboundary_eq_zero` using
Mathlib's `Finset.sum_fiberwise_of_maps_to`. Original indices are retained, so
coincident cells and repeated directions keep their multiplicities.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V ι κ : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

/-- Sweep each closed component in its own transverse lattice direction.
The boundary of the combined filling is the negative source cochain. The
component assignment need not be injective or determined by the geometry. -/
theorem coboundaryOfFinsupp_sum_sweep_of_fiberwise_closed [Fintype ι] [DecidableEq κ]
    (component : ι → κ) (n : κ → N) (σ : ι → OrientedCell h (k + 1))
    (hn : ∀ a, i (n (component a)) ∉ (affineSpan ℝ (σ a).carrier).direction)
    (c : ι → E)
    (hclosed : ∀ b, coboundaryOfFinsupp (R := R)
      (∑ a ∈ Finset.univ.filter (fun a => component a = b), Finsupp.single (σ a) (c a)) = 0) :
    coboundaryOfFinsupp (R := R)
      (∑ a, Finsupp.single ((σ a).sweep (n (component a)) (hn a)) (c a)) =
        -∑ a, mk (σ a) (c a) := by
  classical
  have hfiber (b : κ) :
      coboundaryOfFinsupp (R := R)
        (∑ a ∈ Finset.univ.filter (fun a => component a = b),
          Finsupp.single ((σ a).sweep (n (component a)) (hn a)) (c a)) =
        -∑ a ∈ Finset.univ.filter (fun a => component a = b), mk (σ a) (c a) := by
    let S := Finset.univ.filter (fun a => component a = b)
    have heq (a : S) : component a.val = b := (Finset.mem_filter.mp a.property).2
    have htrans (a : S) : i (n b) ∉ (affineSpan ℝ (σ a.val).carrier).direction := by
      rw [← heq a]
      exact hn a.val
    have hc : coboundaryOfFinsupp (R := R)
        (∑ a : S, Finsupp.single (σ a.val) (c a.val)) = 0 := by
      rw [Finset.sum_coe_sort S (fun a => Finsupp.single (σ a) (c a))]
      exact hclosed b
    have he := coboundaryOfFinsupp_sum_sweep_of_coboundary_eq_zero (n b)
      (fun a : S => σ a.val) htrans (fun a => c a.val) hc
    have hs : (∑ a : S, Finsupp.single ((σ a.val).sweep (n b) (htrans a)) (c a.val)) =
        ∑ a ∈ S, Finsupp.single ((σ a).sweep (n (component a)) (hn a)) (c a) := by
      rw [← Finset.sum_coe_sort S (fun a =>
        Finsupp.single ((σ a).sweep (n (component a)) (hn a)) (c a))]
      apply Finset.sum_congr rfl
      intro a _
      simp only [heq a]
    rw [hs, Finset.sum_coe_sort S (fun a => mk (σ a) (c a))] at he
    exact he
  have hmaps : ∀ a ∈ (Finset.univ : Finset ι),
      component a ∈ Finset.univ.image component := fun a ha => Finset.mem_image_of_mem _ ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => Finsupp.single ((σ a).sweep (n (component a)) (hn a)) (c a)), map_sum]
  simp_rw [hfiber]
  simpa only [Finset.sum_neg_distrib] using
    congrArg Neg.neg (Finset.sum_fiberwise_of_maps_to hmaps (fun a => mk (σ a) (c a)))

end Mei.PolyhedralCochain
