/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Endpoint
public import Mei.Geometry.Convex.PolyhedralCochain.ParameterSubdivision
public import Mei.Geometry.Convex.PolyhedralCochain.Crossing
import Mei.Topology.UnitInterval

/-!
# Endpoint Stokes along polygonal paths

Pairing the signed boundary of a finite full-dimensional polyhedral potential
along an admissible polygonal path gives the value at its target minus the
value at its source. The wall family must include the boundary facets of the
chosen potential presentation. Extra walls, repeated supports, unbounded cells
and lineality are allowed, and the coefficient ring may be noncommutative.

The segment formula extends
`PolyhedralCochain.exists_ball_intersectionPairing_coboundaryPresentation_eq_sub`,
using `OrientedCell.intersectionPairing_subdivide`. The transport formula applies
to any wall cochain equal to this boundary in the cochain quotient. It uses
`PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq` and
`Quiver.Path.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum`, so
subdivision and orientation relations are retained.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Mei.PolyhedralCochain

variable {N V R E ι : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  [Ring R] [AddCommGroup E] [Module R E] [Finite ι]
  {W : ι → Set V} (f : OrientedCell h 0 →₀ E)
  (hfacets : ∀ σ ∈ f.support, ∀ τ ∈ σ.boundaryFacets, ∃ j, W j = τ.carrier)

include hfacets

private theorem exists_endpoint_stokes_partition
    {x y : WallComplement W} (e : AdmissibleSegment x y) :
    ∃ t : ℕ → unitInterval, t 0 = 0 ∧ Monotone t ∧
      (∃ m, ∀ n ≥ m, t n = 1) ∧
      (∀ n, ∀ σ ∈ f.support, ∀ τ ∈ σ.boundaryFacets,
        AffineMap.lineMap x.val y.val (t n : ℝ) ∉ τ.carrier) ∧
      ∀ n, OrientedCell.intersectionPairing (R := R)
        ![AffineMap.lineMap x.val y.val (t n : ℝ),
          AffineMap.lineMap x.val y.val (t (n + 1) : ℝ)]
        (coboundaryPresentation (R := R) f) =
          OrientedCell.intersectionPairing (R := R)
            ![AffineMap.lineMap x.val y.val (t (n + 1) : ℝ)] f -
          OrientedCell.intersectionPairing (R := R)
            ![AffineMap.lineMap x.val y.val (t n : ℝ)] f := by
  classical
  let a : unitInterval → V := fun u => AffineMap.lineMap x.val y.val (u : ℝ)
  -- Pull the local Stokes neighborhoods back to the parameter interval.
  have ha : Continuous a := AffineMap.lineMap_continuous.comp continuous_subtype_val
  have hregular (u : unitInterval) (σ) (hσ : σ ∈ f.support) (τ)
      (hτ : τ ∈ σ.boundaryFacets) : a u ∉ intrinsicFrontier ℝ τ.carrier := by
    obtain ⟨j, hj⟩ := hfacets σ hσ τ hτ
    intro hp
    exact e.regular u u.property
      (mem_singularSupport.mpr (Or.inl ⟨j, by rwa [hj]⟩))
  choose ε hε hlocal using fun u : unitInterval =>
    exists_ball_intersectionPairing_coboundaryPresentation_eq_sub (R := R)
      f (a u) (hregular u)
  let c : unitInterval → Set unitInterval := fun u => a ⁻¹' Metric.ball (a u) (ε u)
  have hc : ∀ u, IsOpen (c u) := fun u => ha.isOpen_preimage _ Metric.isOpen_ball
  have hcover : univ ⊆ ⋃ u, c u := by
    intro u _
    exact mem_iUnion.mpr ⟨u, Metric.mem_ball_self (hε u)⟩
  -- Choose a mesh avoiding all crossing parameters, including coincident crossings.
  let S := Prod.snd '' crossings x y
  have hzero : 0 ∉ S := by
    rintro ⟨⟨j, r⟩, hr, he⟩
    have hr0 : r = 0 := he
    exact x.notMem j (by
      simpa only [hr0, AffineMap.lineMap_apply_zero] using ((mem_crossings x y j r).mp hr).2)
  have hone : 1 ∉ S := by
    rintro ⟨⟨j, r⟩, hr, he⟩
    have hr1 : r = 1 := he
    exact y.notMem j (by
      simpa only [hr1, AffineMap.lineMap_apply_one] using ((mem_crossings x y j r).mp hr).2)
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htS, htc⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_notMem hc hcover
      (e.finite_crossings.image Prod.snd).countable hzero hone
  have htmiss (n : ℕ) (j : ι) : a (t n) ∉ W j := by
    intro hj
    exact htS n ⟨(j, (t n : ℝ)), (mem_crossings x y j _).mpr ⟨(t n).property, hj⟩, rfl⟩
  have hmiss (n : ℕ) (σ) (hσ : σ ∈ f.support) (τ) (hτ : τ ∈ σ.boundaryFacets) :
      a (t n) ∉ τ.carrier := by
    obtain ⟨j, hj⟩ := hfacets σ hσ τ hτ
    rw [← hj]
    exact htmiss n j
  refine ⟨t, ht0, htmono, ⟨m, hm⟩, hmiss, fun n => ?_⟩
  obtain ⟨u, hu⟩ := htc n
  exact hlocal u _ (hu ⟨le_rfl, htmono (Nat.le_succ n)⟩)
    _ (hu ⟨htmono (Nat.le_succ n), le_rfl⟩) (hmiss n) (hmiss (n + 1))

/-- The pairing of a potential's complete signed boundary with an admissible
segment is the difference of its endpoint evaluations. Every boundary facet
of a nonzero source cell must occur in the finite wall family. No bound on
segment length or transverse angle is imposed. -/
theorem intersectionPairing_coboundaryPresentation_eq_sub
    {x y : WallComplement W} (e : AdmissibleSegment x y) :
    OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
        (coboundaryPresentation (R := R) f) =
      OrientedCell.intersectionPairing (R := R) ![y.val] f -
        OrientedCell.intersectionPairing (R := R) ![x.val] f := by
  classical
  let a : unitInterval → V := fun u => AffineMap.lineMap x.val y.val (u : ℝ)
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hmiss, hstep⟩ :=
    exists_endpoint_stokes_partition (R := R) f hfacets e
  let g := coboundaryPresentation (R := R) f
  have hgmiss (n : ℕ) (τ) (hτ : τ ∈ g.support) : a (t n) ∉ τ.carrier := by
    obtain ⟨σ, hσ, hτ⟩ := Finset.mem_biUnion.mp
      (support_coboundaryPresentation_subset f hτ)
    exact hmiss n σ hσ τ hτ
  have hself (n : ℕ) :
      OrientedCell.intersectionPairing (R := R) ![a (t n), a (t n)] g = 0 := by
    rw [OrientedCell.intersectionPairing_apply, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro τ hτ
    rw [OrientedCell.intersectionIndex_of_disjoint, zero_smul]
    rw [Matrix.range_cons_cons_empty, Set.insert_eq_of_mem (mem_singleton _),
      convexHull_singleton, Set.disjoint_singleton_left]
    exact hgmiss n τ hτ
  -- Additivity of intersections at allowed vertices telescopes the local identities.
  have hprefix (n : ℕ) :
      OrientedCell.intersectionPairing (R := R) ![x.val, a (t n)] g =
        OrientedCell.intersectionPairing (R := R) ![a (t n)] f -
          OrientedCell.intersectionPairing (R := R) ![x.val] f := by
    induction n with
    | zero => simpa only [ht0, a, Set.Icc.coe_zero,
        AffineMap.lineMap_apply_zero, sub_self] using hself 0
    | succ n ih =>
      have hle : (t n : ℝ) ≤ (t (n + 1) : ℝ) := htmono (Nat.le_succ n)
      by_cases hz : t n = 0
      · simpa only [hz, a, Set.Icc.coe_zero, AffineMap.lineMap_apply_zero]
          using hstep n
      by_cases he : t n = t (n + 1)
      · simpa only [← he] using ih
      have htpos : 0 < (t n : ℝ) := lt_of_le_of_ne (t n).property.1
        (fun he => hz (Subtype.ext he.symm))
      have hlt : (t n : ℝ) < (t (n + 1) : ℝ) :=
        lt_of_le_of_ne hle (fun he' => he (Subtype.ext he'))
      have hratio : (t n : ℝ) / (t (n + 1) : ℝ) ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos htpos (htpos.trans hlt), (div_lt_one (htpos.trans hlt)).mpr hlt⟩
      have hsplit := OrientedCell.intersectionPairing_subdivide (R := R) g hratio
        (z := a (t n)) (x := x.val) (y := a (t (n + 1)))
        (by simp [a, AffineMap.lineMap_lineMap_right, (htpos.trans hlt).ne'])
        (hgmiss n)
      rw [hsplit, ih, hstep]
      abel
  simpa only [hm m le_rfl, a, Set.Icc.coe_one, AffineMap.lineMap_apply_one]
    using hprefix m

/-- The signed boundary pairing along a polygonal path telescopes to the
potential difference at its endpoints. Repeated vertices and constant paths
are included. The finite wall family contains all participating facets. -/
theorem addWeightOfEPs_intersectionPairing_coboundaryPresentation_eq_sub
    {x y : WallComplement W} (p : AdmissiblePLPath x y) :
    p.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
      ![u.val, v.val] (coboundaryPresentation (R := R) f)) =
        OrientedCell.intersectionPairing (R := R) ![y.val] f -
          OrientedCell.intersectionPairing (R := R) ![x.val] f := by
  induction p with
  | nil => simp only [Quiver.Path.addWeightOfEPs_nil, sub_self]
  | cons p e ih =>
    rw [Quiver.Path.addWeightOfEPs_cons, ih,
      intersectionPairing_coboundaryPresentation_eq_sub f hfacets e.down]
    abel

end Mei.PolyhedralCochain

namespace Quiver.Path

open Mei

variable {N V R E ι : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  [Ring R] [AddCommGroup E] [Module R E] [Fintype ι]
  {σ : ι → OrientedCell h 1}
  {x y : WallComplement (fun j => (σ j).carrier)}

/-- A wall cochain equal to the boundary of a full-dimensional potential has
additive transport given by the source value minus the target value. Equality
is in the cochain quotient, including subdivision and orientation relations.
The path is admissible for the indexed walls, which also contain all facets
of the potential presentation. -/
theorem wallCrossingSum_eq_sub_of_eq_coboundary
    (p : AdmissiblePLPath x y) (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (f : OrientedCell h 0 →₀ E)
    (hfacets : ∀ υ ∈ f.support, ∀ τ ∈ υ.boundaryFacets,
      ∃ j, (σ j).carrier = τ.carrier)
    (hboundary : ∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j) =
      PolyhedralCochain.coboundaryOfFinsupp (R := R) f) :
    p.wallCrossingSum ν c =
      OrientedCell.intersectionPairing (R := R) ![x.val] f -
        OrientedCell.intersectionPairing (R := R) ![y.val] f := by
  classical
  let g := ∑ j, Finsupp.single (σ j) (c j)
  have hboundary' : PolyhedralCochain.ofFinsupp (R := R) g =
      PolyhedralCochain.ofFinsupp
        (PolyhedralCochain.coboundaryPresentation (R := R) f) := by
    simpa only [g, map_sum, PolyhedralCochain.ofFinsupp_single,
      PolyhedralCochain.ofFinsupp_coboundaryPresentation] using hboundary
  have hsegment {a b : WallComplement (fun j => (σ j).carrier)} (e : a ⟶ b) :
      OrientedCell.intersectionPairing (R := R) ![a.val, b.val] g =
        OrientedCell.intersectionPairing (R := R) ![b.val] f -
          OrientedCell.intersectionPairing (R := R) ![a.val] f := by
    rw [PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq hboundary']
    · exact PolyhedralCochain.intersectionPairing_coboundaryPresentation_eq_sub
        f hfacets e.down
    · intro τ hτ
      obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum τ hτ
      obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hj
      exact e.down.isTransverse_orientedCell j
    · intro τ hτ
      obtain ⟨υ, hυ, hτ⟩ := Finset.mem_biUnion.mp
        (PolyhedralCochain.support_coboundaryPresentation_subset f hτ)
      obtain ⟨j, hj⟩ := hfacets υ hυ τ hτ
      have ht := e.down.isTransverse_orientedCell j
      rcases ht with ⟨hf, hl⟩
      rw [hj] at hf hl
      exact ⟨hf, hl⟩
  have hpath : p.addWeightOfEPs (fun a b =>
      OrientedCell.intersectionPairing (R := R) ![a.val, b.val] g) =
        OrientedCell.intersectionPairing (R := R) ![y.val] f -
          OrientedCell.intersectionPairing (R := R) ![x.val] f := by
    induction p with
    | nil => simp only [addWeightOfEPs_nil, sub_self]
    | cons p e ih => rw [addWeightOfEPs_cons, ih, hsegment e]; abel
  rw [addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum p ν c hν] at hpath
  simpa only [neg_neg, neg_sub] using congrArg Neg.neg hpath

end Quiver.Path
