/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Exact
public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Path
public import Mei.Geometry.Convex.PolyhedralCochain.Crossing
public import Mei.Geometry.Convex.Polyhedron.Path.Perturbation

/-!
# Path independence for closed wall cochains

A closed codimension-one polyhedral cochain has zero additive crossing sum
around every admissible polygonal loop of its presenting wall family. Hence
its crossing sums depend only on endpoints. The walls need not form a complex;
coincident indexed walls and arbitrary module coefficients are allowed.

Exactness supplies a finite full-dimensional potential, whose facets may cut
through the original path. Move the whole loop, including its basepoint, into
general position for these extra facets, retaining its original signed events.
The quotient-invariant pairing then identifies its crossing sum with a
boundary pairing, which vanishes by endpoint Stokes. No admissibility for the
potential's extra facets is required of the original loop.

The proof combines `PolyhedralCochain.exists_outgoing_primitive`,
`PolyhedralCochain.addWeightOfEPs_intersectionPairing_coboundaryPresentation_eq_sub`,
and `Quiver.Path.exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt`.
The moving-basepoint argument follows `DirectedDiagram.LevelEquivalent.consistent`.
-/

public section

noncomputable section

open Set Mei Mei.Convex Mei.Convex.WallComplement

namespace Quiver.Path

variable {N V ι R E : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Fintype ι]
  [Ring R] [AddCommGroup E] [Module R E]
  {σ : ι → OrientedCell h 1}
  {x y : WallComplement (fun j => (σ j).carrier)}

/-- A closed wall cochain has zero additive transport around every admissible
loop of its original wall family. In particular, the loop need not avoid any
extra facets introduced by a polyhedral primitive of the cochain. -/
theorem wallCrossingSum_eq_zero_of_coboundary_eq_zero (p : AdmissiblePLPath x x)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hker : ∀ j, (ν j).ker = (affineSpan ℝ (σ j).carrier).direction)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hc : PolyhedralCochain.coboundary
      (∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j)) = 0) :
    p.wallCrossingSum ν c = 0 := by
  classical
  let := h.finiteDimensional
  cases p with
  | nil => simp
  | @cons y _ p e =>
    let loop := p.cons e
    -- Exactness gives a potential; retain every one of its facets in the test family.
    let f := ∑ j, Finsupp.single (σ j) (c j)
    have hf : PolyhedralCochain.coboundary (PolyhedralCochain.ofFinsupp (R := R) f) = 0 := by
      simpa only [f, map_sum, PolyhedralCochain.ofFinsupp_single] using hc
    obtain ⟨_, g, hg, _⟩ := PolyhedralCochain.exists_outgoing_primitive _ hf
    let J := Σ P : g.support, P.val.boundaryFacets
    let τ : J → OrientedCell h 1 := fun a => a.2.val
    let W : ι ⊕ J → Set V := Sum.elim (fun j => (σ j).carrier) (fun a => (τ a).carrier)
    have hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j) := by
      intro j
      obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp (Sum.elim σ τ j).rational
      have hp : TauCeti.IsConvexPolyhedron (Sum.elim σ τ j).carrier :=
        hP ▸ P.isConvexPolyhedron
      cases j <;> exact hp
    have hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
        Module.finrank ℝ V := by
      rintro (j | a)
      · exact (σ j).finrank_direction_add
      · exact (τ a).finrank_direction_add
    obtain ⟨ε, hε, hstable⟩ := loop.exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt
      (fun j => (σ j).isClosed_carrier) (fun j => (σ j).finrank_direction_add) ν hker
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp p.vertices_head?
    have hv : loop.vertices.map WallComplement.val =
        x.val :: (l.map WallComplement.val ++ [x.val]) := by
      simp only [loop, vertices_cons, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, hl, List.cons_append]
    -- Perturb the basepoint once for both ends, so the new path remains a loop.
    obtain ⟨a, q, hq⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt hpoly hdim x.val
      (l := l.map WallComplement.val) hε
    let r : WallComplement W ⥤q WallComplement (fun j => (σ j).carrier) :=
      restrictPrefunctor W Sum.inl
    let q₀ := r.mapPath q
    have hevents : q₀.signedCrossingEvents ν = loop.signedCrossingEvents ν := by
      apply hstable q₀
      have hv₀ : q₀.vertices.map WallComplement.val = q.vertices.map WallComplement.val :=
        vertices_restrictPrefunctor W Sum.inl q
      rwa [hv, hv₀]
    have hfacets : ∀ P ∈ g.support, ∀ υ ∈ P.boundaryFacets, ∃ j, υ.carrier = W j := by
      intro P hP υ hυ
      exact ⟨Sum.inr ⟨⟨P, hP⟩, ⟨υ, hυ⟩⟩, rfl⟩
    -- On this enlarged family, both presentations have transverse segment tests.
    have hg' : PolyhedralCochain.ofFinsupp (R := R) f =
        PolyhedralCochain.ofFinsupp (PolyhedralCochain.coboundaryPresentation (R := R) g) := by
      rw [PolyhedralCochain.ofFinsupp_coboundaryPresentation,
        ← PolyhedralCochain.coboundary_ofFinsupp]
      exact hg.symm
    have hsupport : ∀ υ ∈ (PolyhedralCochain.coboundaryPresentation (R := R) g).support,
        ∃ j : J, υ = τ j := by
      rw [← Finsupp.sum_single g]
      simp only [Finsupp.sum, map_sum, PolyhedralCochain.coboundaryPresentation_single]
      intro υ hυ
      obtain ⟨P, hP, hυ⟩ := Finsupp.mem_support_finsetSum υ hυ
      obtain ⟨ψ, hψ, hυ⟩ := Finsupp.mem_support_finsetSum υ hυ
      exact ⟨⟨⟨P, hP⟩, ⟨ψ, hψ⟩⟩,
        ((Finsupp.mem_support_single _ _ _).mp hυ).1⟩
    have hpair {u v : WallComplement W} (e : u ⟶ v) :
        OrientedCell.intersectionPairing (R := R) ![u.val, v.val] f =
          OrientedCell.intersectionPairing (R := R) ![u.val, v.val]
            (PolyhedralCochain.coboundaryPresentation (R := R) g) := by
      apply PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq hg'
      · intro υ hυ
        obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum υ hυ
        obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hj
        exact ((r.map e).down.isTransverse_orientedCell j)
      · intro υ hυ
        obtain ⟨j, rfl⟩ := hsupport υ hυ
        exact (((restrictPrefunctor W Sum.inr).map e).down.isTransverse_orientedCell j)
    have hweight {u v : WallComplement W} (s : AdmissiblePLPath u v) :
        (r.mapPath s).addWeightOfEPs (fun u v =>
            OrientedCell.intersectionPairing (R := R) ![u.val, v.val] f) =
          s.addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
            ![u.val, v.val] (PolyhedralCochain.coboundaryPresentation (R := R) g)) := by
      induction s with
      | nil => simp only [Prefunctor.mapPath_nil, addWeightOfEPs_nil]
      | cons s e ih =>
        rw [Prefunctor.mapPath_cons, addWeightOfEPs_cons, addWeightOfEPs_cons, ih]
        simp only [r, restrictPrefunctor_obj_val]
        rw [hpair e]
    -- Endpoint Stokes telescopes around the perturbed loop. Its original events survive.
    have hz := PolyhedralCochain.addWeightOfEPs_intersectionPairing_coboundaryPresentation_eq_sub
      (R := R) g hfacets q
    rw [sub_self, ← hweight q,
      q₀.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum ν c hν] at hz
    rw [wallCrossingSum_def] at hz ⊢
    rw [← hevents]
    exact neg_eq_zero.mp hz

/-- Additive transport of a closed wall cochain depends only on endpoints,
without choosing a common refinement or a primitive for the test paths. -/
theorem wallCrossingSum_eq_of_coboundary_eq_zero (p q : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hker : ∀ j, (ν j).ker = (affineSpan ℝ (σ j).carrier).direction)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hc : PolyhedralCochain.coboundary
      (∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j)) = 0) :
    p.wallCrossingSum ν c = q.wallCrossingSum ν c := by
  have he := (p.comp q.reverse).wallCrossingSum_eq_zero_of_coboundary_eq_zero ν c hker hν hc
  rw [wallCrossingSum_comp, wallCrossingSum_reverse q ν c hker, ← sub_eq_add_neg,
    sub_eq_zero] at he
  exact he

end Quiver.Path
