/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Exact
public import Mei.Geometry.Convex.PolyhedralCochain.Crossing
public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Path
import Mei.Geometry.Convex.PolyhedralCochain.Coorientation
import Mei.Geometry.Convex.Polyhedron.Path.Perturbation

/-!
# Closed wall cochains have endpoint-independent additive transport

A closed codimension-one polyhedral cochain has zero signed crossing sum around
any admissible polygonal loop. Its polyhedral primitive can have additional
facets, including facets through vertices of the original loop. Perturbing the
whole loop, including its basepoint, makes it admissible for these facets while
preserving its original signed crossing events. Endpoint Stokes then telescopes.
Thus the conclusion imposes no extra general-position conditions on the loop.

The argument uses `PolyhedralCochain.coboundary_eq_zero_iff_exists_coboundary`, the endpoint
Stokes theorem `addWeightOfEPs_intersectionPairing_coboundaryPresentation_eq_sub`,
invariance of intersection pairings under cochain relations, and
`AdmissiblePLPath.exists_loop_forall₂_dist_lt`. Repeated indexed walls, torsion
coefficients, unbounded cells and lineality are allowed.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement

namespace Quiver.Path

variable {N V ι R E : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Fintype ι]
  [Ring R] [AddCommGroup E] [Module R E]
  {σ : ι → OrientedCell h 1}

/-- If an indexed wall cochain is the boundary of a polyhedral potential, its
crossing sum vanishes on every admissible loop for the original walls. Vertices
and edges need not be in general position for the potential's extra facets. -/
private theorem wallCrossingSum_loop_eq_zero_of_eq_coboundary
    {x : WallComplement (fun j => (σ j).carrier)} (p : AdmissiblePLPath x x)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (f : OrientedCell h 0 →₀ E)
    (hf : PolyhedralCochain.coboundary (PolyhedralCochain.ofFinsupp (R := R) f) =
      ∑ j, PolyhedralCochain.mk (σ j) (c j)) :
    p.wallCrossingSum ν c = 0 := by
  classical
  let := h.finiteDimensional
  have hpoly (τ : OrientedCell h 1) : TauCeti.IsConvexPolyhedron τ.carrier := by
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp τ.rational
    exact hP ▸ P.isConvexPolyhedron
  have hker (j : ι) : (ν j).ker = (affineSpan ℝ (σ j).carrier).direction := by
    obtain ⟨m, _, hm, hs⟩ := (σ j).exists_integral_coorientation
    ext v
    rw [← hm, LinearMap.mem_ker, LinearMap.mem_ker,
      ← sign_eq_zero_iff, hν j v, ← hs v, sign_eq_zero_iff]
  cases p with
  | nil => simp
  | @cons y _ p e =>
    let loop := p.cons e
    obtain ⟨ε, hε, hstable⟩ :=
      loop.exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt
        (fun j => (σ j).isClosed_carrier) (fun j => (σ j).finrank_direction_add) ν hker
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp p.vertices_head?
    have hv : loop.vertices.map WallComplement.val =
        x.val :: (l.map WallComplement.val ++ [x.val]) := by
      simp only [loop, Quiver.Path.vertices_cons, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, hl, List.cons_append]
    -- Add every facet occurrence, retaining multiplicities in the potential.
    let J := Σ P : f.support, P.val.boundaryFacets
    let τ : J → OrientedCell h 1 := fun a => a.2.val
    let W : ι ⊕ J → Set V := Sum.elim (fun j => (σ j).carrier) (fun a => (τ a).carrier)
    have hWpoly : ∀ a, TauCeti.IsConvexPolyhedron (W a) := by
      rintro (j | a)
      · exact hpoly (σ j)
      · exact hpoly (τ a)
    have hWdim : ∀ a, Module.finrank ℝ (affineSpan ℝ (W a)).direction + 1 =
        Module.finrank ℝ V := by
      rintro (j | a)
      · exact (σ j).finrank_direction_add
      · exact (τ a).finrank_direction_add
    obtain ⟨a, q, hq⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt hWpoly hWdim x.val
      (l := l.map WallComplement.val) hε
    let r := restrictPrefunctor W Sum.inl
    let s := restrictPrefunctor W Sum.inr
    -- Use the original carrier families explicitly when evaluating crossing events.
    let q₀ : AdmissiblePLPath
        (⟨a.val, fun j => a.notMem (.inl j)⟩ : WallComplement (fun j => (σ j).carrier))
        ⟨a.val, fun j => a.notMem (.inl j)⟩ := r.mapPath q
    let q₁ : AdmissiblePLPath
        (⟨a.val, fun j => a.notMem (.inr j)⟩ : WallComplement (fun j => (τ j).carrier))
        ⟨a.val, fun j => a.notMem (.inr j)⟩ := s.mapPath q
    have hv₀ : q₀.vertices.map WallComplement.val = q.vertices.map WallComplement.val :=
      vertices_restrictPrefunctor W Sum.inl q
    have hnear : List.Forall₂ (fun u v => dist u v < ε)
        (loop.vertices.map WallComplement.val) (q₀.vertices.map WallComplement.val) := by
      rwa [hv, hv₀]
    have hevents := hstable q₀ hnear
    have hfacets : ∀ P ∈ f.support, ∀ υ ∈ P.boundaryFacets,
        ∃ j : J, υ.carrier = (τ j).carrier := by
      intro P hP υ hυ
      exact ⟨⟨⟨P, hP⟩, ⟨υ, hυ⟩⟩, rfl⟩
    let g := PolyhedralCochain.coboundaryPresentation (R := R) f
    let g₀ := ∑ j, Finsupp.single (σ j) (c j)
    have hg : PolyhedralCochain.ofFinsupp (R := R) g₀ =
        PolyhedralCochain.ofFinsupp g := by
      simpa only [g₀, g, map_sum, PolyhedralCochain.ofFinsupp_single,
        PolyhedralCochain.ofFinsupp_coboundaryPresentation,
        ← PolyhedralCochain.coboundary_ofFinsupp] using hf.symm
    have hg₀ (υ) (hυ : υ ∈ g₀.support) : ∃ j, υ = σ j := by
      obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum υ hυ
      exact ⟨j, ((Finsupp.mem_support_single _ _ _).mp hj).1⟩
    have hg₁ : ∀ υ ∈ g.support, ∃ j : J, υ = τ j := by
      intro υ hυ
      obtain ⟨P, hP, hυ⟩ :=
        Finset.mem_biUnion.mp
          (PolyhedralCochain.support_coboundaryPresentation_subset f hυ)
      exact ⟨⟨⟨P, hP⟩, ⟨υ, hυ⟩⟩, rfl⟩
    -- Compare both representatives on the same edges of the enlarged-wall loop.
    have hpair {u v : WallComplement W} (q : AdmissiblePLPath u v) :
        (r.mapPath q).addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] g₀) =
        (s.mapPath q).addWeightOfEPs (fun u v => OrientedCell.intersectionPairing (R := R)
          ![u.val, v.val] g) := by
      induction q with
      | nil => simp only [Prefunctor.mapPath_nil, addWeightOfEPs_nil]
      | cons q e ih =>
        simp only [Prefunctor.mapPath_cons, addWeightOfEPs_cons, ih]
        congr 1
        exact PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq hg
          (fun υ hυ => by
            obtain ⟨j, rfl⟩ := hg₀ υ hυ
            exact (r.map e).down.isTransverse_orientedCell j)
          (fun υ hυ => by
            obtain ⟨j, rfl⟩ := hg₁ υ hυ
            exact (s.map e).down.isTransverse_orientedCell j)
    have hzero := PolyhedralCochain.addWeightOfEPs_intersectionPairing_coboundaryPresentation_eq_sub
      (R := R) f hfacets q₁
    rw [sub_self] at hzero
    have hsum := q₀.addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum (R := R) ν c
      (fun j _ => hν j)
    have hfinal : -q₀.wallCrossingSum ν c = 0 :=
      hsum.symm.trans ((hpair q).trans hzero)
    have heq := congrArg (fun events : List (Finset (ι × ℤ)) =>
      (events.map (fun S => ∑ a ∈ S, a.2 • c a.1)).sum) hevents
    have heq' : q₀.wallCrossingSum ν c = loop.wallCrossingSum ν c := by
      simpa only [wallCrossingSum_def] using heq
    exact heq'.symm.trans (neg_eq_zero.mp hfinal)

/-- A closed codimension-one wall cochain has zero additive transport around
all admissible loops. Closedness is equality in the cochain quotient, so
orientation relations, subdivisions and coincident contributions are retained.
Normals need agree with the orientations only on walls with nonzero coefficients. -/
theorem wallCrossingSum_loop_eq_zero_of_coboundary_eq_zero
    {x : WallComplement (fun j => (σ j).carrier)} (p : AdmissiblePLPath x x)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hc : PolyhedralCochain.coboundary (∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j)) = 0) :
    p.wallCrossingSum ν c = 0 := by
  classical
  -- Fill in unused normals to apply the geometric perturbation argument.
  choose m _ _ hm using fun j => (σ j).exists_integral_coorientation
  let μ : ι → V →ₗ[ℝ] ℝ := fun j => if c j = 0 then h.realCharacter (m j) else ν j
  have hμ : ∀ j v, SignType.sign (μ j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v) := by
    intro j v
    by_cases hj : c j = 0
    · simpa only [μ, ite_eq_left hj] using hm j v
    · simpa only [μ, ite_eq_right hj] using hν j hj v
  have he := p.wallCrossingSum_eq_of_cochain_eq (R := R) p ν μ c c
    hν (fun j _ => hμ j) rfl (fun _ => rfl) (fun _ => rfl) rfl
  obtain ⟨B, hB⟩ := (PolyhedralCochain.coboundary_eq_zero_iff_exists_coboundary _).mp hc
  obtain ⟨f, rfl⟩ := PolyhedralCochain.ofFinsupp_surjective B
  exact he.trans (p.wallCrossingSum_loop_eq_zero_of_eq_coboundary μ c hμ f hB)

/-- Additive transport of a closed wall cochain depends only on endpoints,
without choosing a common refinement or a primitive for the test paths. -/
theorem wallCrossingSum_eq_of_coboundary_eq_zero
    {x y : WallComplement (fun j => (σ j).carrier)} (p q : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hc : PolyhedralCochain.coboundary
      (∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j)) = 0) :
    p.wallCrossingSum ν c = q.wallCrossingSum ν c := by
  have hp := (p.comp q.reverse).wallCrossingSum_loop_eq_zero_of_coboundary_eq_zero ν c hν hc
  have hq := (q.comp q.reverse).wallCrossingSum_loop_eq_zero_of_coboundary_eq_zero ν c hν hc
  rw [wallCrossingSum_comp] at hp hq
  exact add_right_cancel (hp.trans hq.symm)

end Quiver.Path
