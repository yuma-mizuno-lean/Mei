/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Polyhedron.Rational.Direction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Isolating neighborhoods and transverse slices at joints

At a relative interior point of a joint, a sufficiently small ball meets only
cells containing the joint and misses its relative boundary. The skeleton of
codimension at least two agrees with the joint throughout that ball. A chosen
complement to the joint direction gives a two-dimensional transverse slice
whose intersection with that skeleton is exactly the center.

The joint direction is also the common kernel of two real extensions of
integral characters. Evaluating these equations on lattice vectors gives the
integral tangent kernel used in homogeneous wall-space calculations.

These are the isolation and transversality conditions needed before constructing
small polygonal meridians: any filled polygon in the ball and slice misses every
other joint and the boundary of the chosen joint. The result constructs the slice
and neighborhood, without assuming a transverse plane as input. Cells may be
unbounded or have lineality.

The construction uses the common-face incidence theorem
`FinitePolyhedralComplex.eventually_subset_of_mem_cell`, Mathlib's
`Submodule.exists_isCompl`, and
`AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl`.
-/

public section

open Set Filter Topology

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The tangent space of a joint is the common kernel of two integral
characters extended to the ambient real space. -/
theorem exists_joint_direction_eq_inf_ker (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) :
    ∃ f g : N →+ ℤ, (affineSpan ℝ J).direction =
      (h.realCharacter f).ker ⊓ (h.realCharacter g).ker := by
  obtain ⟨hJC, hdim⟩ := (C.mem_cellsOfCodimension 2 J).mp hJ
  obtain ⟨f, g, hfg⟩ := (C.rational J hJC).exists_direction_eq_inf_ker
    (C.nonempty J hJC) hdim
  exact ⟨f.toAddMonoidHom, g.toAddMonoidHom, hfg⟩

/-- Every relative interior point of a joint admits an isolating ball and a
two-dimensional complementary slice. Within that slice and ball, the whole
codimension-at-least-two skeleton consists of the center alone. The ball misses
the joint's relative boundary and every other joint, and meets only cells containing the joint. -/
theorem exists_isolating_ball_joint (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) {x : V} (hx : x ∈ intrinsicInterior ℝ J) :
    ∃ (r : ℝ) (W : Submodule ℝ V), 0 < r ∧
      IsCompl (affineSpan ℝ J).direction W ∧ Module.finrank ℝ W = 2 ∧
      (Metric.ball x r ∩ (AffineSubspace.mk' x W : Set V)) ∩
        (C.codimensionAtLeast 2).support = {x} ∧
      Disjoint (Metric.ball x r) (intrinsicFrontier ℝ J) ∧
      (∀ Q ∈ C.joints, Q ≠ J → Disjoint (Metric.ball x r) Q) ∧
      ∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → J ⊆ Q := by
  let := h.finiteDimensional
  obtain ⟨r, hr, hskeleton, hfrontier, hother, hcells⟩ := C.exists_isolating_ball hJ hx
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (affineSpan ℝ J).direction
  have hdimJ := ((C.mem_cellsOfCodimension 2 J).mp hJ).2
  have hdimW := Submodule.finrank_add_eq_of_isCompl hW
  have hxJ := intrinsicInterior_subset hx
  have hxA := subset_affineSpan ℝ J hxJ
  have hxW : x ∈ (AffineSubspace.mk' x W : Set V) := AffineSubspace.self_mem_mk' x W
  obtain ⟨p, hp⟩ := AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl
    (s₁ := affineSpan ℝ J) (s₂ := AffineSubspace.mk' x W) ⟨x, hxA⟩ ⟨x, hxW⟩
    (by simpa only [AffineSubspace.direction_mk'] using hW)
  have hpx : x = p := Set.mem_singleton_iff.mp (hp ▸ ⟨hxA, hxW⟩)
  subst p
  refine ⟨r, W, hr, hW, by omega, ?_, hfrontier, hother, hcells⟩
  ext y
  constructor
  · rintro ⟨⟨hyball, hyW⟩, hys⟩
    have hyJ : y ∈ Metric.ball x r ∩ J := hskeleton ▸ ⟨hyball, hys⟩
    exact hp ▸ ⟨subset_affineSpan ℝ J hyJ.2, hyW⟩
  · intro hxy
    have hxy : y = x := Set.mem_singleton_iff.mp hxy
    subst y
    have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    have hxs : x ∈ Metric.ball x r ∩ (C.codimensionAtLeast 2).support :=
      hskeleton.symm ▸ ⟨hxball, hxJ⟩
    exact ⟨⟨hxball, hxW⟩, hxs.2⟩

end Mei.FinitePolyhedralComplex
