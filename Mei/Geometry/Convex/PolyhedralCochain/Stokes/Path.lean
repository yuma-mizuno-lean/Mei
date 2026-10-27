/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Endpoint
public import Mei.Geometry.Convex.PolyhedralCochain.ParameterSubdivision
import Mei.Topology.Order.LocalRelation
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Endpoint Stokes along admissible polygonal paths

The pairing of the complete signed boundary of a finite full-dimensional
potential along an admissible polygonal path is its target point evaluation
minus its source point evaluation. In particular, the boundary has zero pairing
around every admissible loop. The wall family must contain every participating
facet; it may also contain additional walls and repeated supports.

The result combines the local endpoint formula
`PolyhedralCochain.exists_ball_intersectionPairing_coboundaryPresentation_eq_sub`
with `OrientedCell.intersectionPairing_subdivide`. Finiteness of the crossing
parameters (`AdmissibleSegment.finite_crossings`) gives a dense set of allowed
cut parameters, to which `Dense.rel_of_locally` applies. Coefficients may have torsion and lie in a
module over any associative ring.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Mei.PolyhedralCochain

variable {N V R E ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  [Ring R] [AddCommGroup E] [Module R E] [Finite ι]
  {W : ι → Set V}

/-- Pairing the signed boundary of a full-dimensional potential with an
admissible segment gives its endpoint difference. Every participating facet
must occur in the wall family. No shortness condition is required. -/
theorem intersectionPairing_coboundaryPresentation_eq_sub_of_admissible
    (f : OrientedCell h 0 →₀ E)
    (hf : ∀ P ∈ f.support, ∀ τ ∈ P.boundaryFacets, ∃ j, τ.carrier = W j)
    {x y : WallComplement W} (e : x ⟶ y) :
    OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
        (coboundaryPresentation (R := R) f) =
      OrientedCell.intersectionPairing (R := R) ![y.val] f -
        OrientedCell.intersectionPairing (R := R) ![x.val] f := by
  classical
  let g := coboundaryPresentation (R := R) f
  let φ := AffineMap.lineMap (k := ℝ) x.val y.val
  -- Every cut outside the finite crossing set is an allowed subdivision vertex.
  let B := Prod.snd '' crossings x y
  have hB : B.Finite := e.down.finite_crossings.image Prod.snd
  have hallowed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (htB : t ∈ Bᶜ) (j : ι) :
      φ t ∉ W j := by
    intro hj
    exact htB ⟨(j, t), (mem_crossings x y j t).mpr ⟨ht, hj⟩, rfl⟩
  have hfacets (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (htB : t ∈ Bᶜ) :
      ∀ P ∈ f.support, ∀ τ ∈ P.boundaryFacets, φ t ∉ τ.carrier := by
    intro P hP τ hτ
    obtain ⟨j, hj⟩ := hf P hP τ hτ
    rw [hj]
    exact hallowed t ht htB j
  have hsupport : ∀ τ ∈ g.support, ∃ j, τ.carrier = W j := by
    dsimp only [g]
    rw [← Finsupp.sum_single f]
    simp only [Finsupp.sum, map_sum, coboundaryPresentation_single]
    intro τ hτ
    obtain ⟨P, hP, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
    obtain ⟨υ, hυ, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hτ
    exact hf P hP τ hυ
  have hends : (0 : ℝ) ∈ Bᶜ ∧ (1 : ℝ) ∈ Bᶜ := by
    constructor
    · rintro ⟨⟨j, t⟩, ht, he⟩
      have hm := (mem_crossings x y j t).mp ht
      have ht0 : t = 0 := he
      exact x.notMem j (by simpa only [ht0, AffineMap.lineMap_apply_zero] using hm.2)
    · rintro ⟨⟨j, t⟩, ht, he⟩
      have hm := (mem_crossings x y j t).mp ht
      have ht1 : t = 1 := he
      exact y.notMem j (by simpa only [ht1, AffineMap.lineMap_apply_one] using hm.2)
  -- Glue the local Stokes identities, composing only at allowed parameters.
  have hglobal := (hB.countable.dense_compl ℝ).rel_of_locally zero_le_one hends.1 hends.2
    (fun u v => OrientedCell.intersectionPairing (R := R) ![φ u, φ v] g =
      OrientedCell.intersectionPairing (R := R) ![φ v] f -
        OrientedCell.intersectionPairing (R := R) ![φ u] f) ?_ ?_
  · simpa only [φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hglobal
  · intro u hu v hv w hw hus hvs hws huv hvw huvrel hvwrel
    rcases huv.eq_or_lt with rfl | huv
    · exact hvwrel
    rcases hvw.eq_or_lt with rfl | hvw
    · exact huvrel
    have hwu : 0 < w - u := by linarith
    have ht : (v - u) / (w - u) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (sub_pos.mpr huv) hwu, (div_lt_one hwu).mpr (by linarith)⟩
    have hparam : AffineMap.lineMap u w ((v - u) / (w - u)) = v := by
      rw [AffineMap.lineMap_apply_module', smul_eq_mul, div_mul_cancel₀ _ hwu.ne']
      ring
    have hvertex : φ v = AffineMap.lineMap (φ u) (φ w) ((v - u) / (w - u)) := by
      rw [← AffineMap.apply_lineMap, hparam]
    rw [OrientedCell.intersectionPairing_subdivide g ht hvertex
      (fun τ hτ => by
        obtain ⟨j, hj⟩ := hsupport τ hτ
        rw [hj]
        exact hallowed v hv hvs j), huvrel, hvwrel]
    abel
  · intro t ht
    -- Regularity includes the excluded crossing parameters, so the local
    -- identity can be applied across, rather than just between, crossings.
    obtain ⟨ε, hε, he⟩ :=
      exists_ball_intersectionPairing_coboundaryPresentation_eq_sub (R := R) f (φ t)
        (by
          intro P hP τ hτ
          obtain ⟨j, hj⟩ := hf P hP τ hτ
          rw [hj]
          exact fun hfront => e.down.regular t ht
            (mem_singularSupport.mpr (Or.inl ⟨j, hfront⟩)))
    have hc : Continuous φ := by fun_prop
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (hc.continuousAt.eventually (Metric.ball_mem_nhds (φ t) hε))
    refine ⟨δ, hδ, fun u hu v hv hut hvt hus hvs _ => ?_⟩
    exact he (φ u) (hnear (Metric.mem_ball.mp hut)) (φ v)
      (hnear (Metric.mem_ball.mp hvt)) (hfacets u hu hus) (hfacets v hv hvs)

/-- The sum of boundary pairings along an admissible polygonal path is the
endpoint difference of the potential. Thus it depends only on the endpoints,
including for constant paths and loops. -/
theorem addWeightOfEPs_intersectionPairing_coboundaryPresentation_eq_sub
    (f : OrientedCell h 0 →₀ E)
    (hf : ∀ P ∈ f.support, ∀ τ ∈ P.boundaryFacets, ∃ j, τ.carrier = W j)
    {x y : WallComplement W} (p : AdmissiblePLPath x y) :
    p.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
        ![u.val, v.val] (coboundaryPresentation (R := R) f)) =
      OrientedCell.intersectionPairing (R := R) ![y.val] f -
        OrientedCell.intersectionPairing (R := R) ![x.val] f := by
  induction p with
  | nil => simp only [Quiver.Path.addWeightOfEPs_nil, sub_self]
  | cons p e ih =>
    rw [Quiver.Path.addWeightOfEPs_cons, ih,
      intersectionPairing_coboundaryPresentation_eq_sub_of_admissible f hf e]
    abel

end Mei.PolyhedralCochain
