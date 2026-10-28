/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Sweep.Exceptional

/-!
# Singular-sweep exceptions for a polyhedral complex

For finitely many velocity vectors, `FinitePolyhedralComplex.singularDiscriminant`
is the finite arrangement of affine spans of sweeps of all cells of codimension
at least two. Generic endpoints have their full lines in these directions
disjoint from the higher skeleton and, in particular, from the singular support
of the walls. Thus the arrangement detects singular encounters of backward rays.

No transversality or nonzero-velocity assumption is required. Unbounded cells
and lineality are allowed. The existing arrangement API gives an open dense
generic locus and dense common generic loci for countably many such choices.

We use the complex's codimension subcomplex and its singular-support inclusion,
together with `ExceptionalArrangement.ofSweeps`.
-/

public section

noncomputable section

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Affine spans of the sweeps of all higher-codimension cells along the
specified vectors. These are the singular-encounter exceptions for endpoints. -/
def singularDiscriminant (C : FinitePolyhedralComplex h) (vectors : Finset V) :
    ExceptionalArrangement V := by
  have := h.finiteDimensional
  refine ExceptionalArrangement.ofSweeps (C.codimensionAtLeast 2).cells vectors ?_
  intro P hP _
  have hd := ((C.mem_codimensionAtLeast_cells 2 P).mp hP).2
  rw [← direction_affineSpan]
  omega

open Classical in
/-- The exceptions are the swept affine spans of the higher-codimension cells. -/
@[simp]
theorem exceptions_singularDiscriminant (C : FinitePolyhedralComplex h)
    (vectors : Finset V) :
    (C.singularDiscriminant vectors).exceptions =
      ((C.codimensionAtLeast 2).cells ×ˢ vectors).image
        (fun z => affineSpan ℝ (Convex.sweep z.1 z.2)) := by
  have := h.finiteDimensional
  exact ExceptionalArrangement.exceptions_ofSweeps _ _ _

/-- A generic endpoint has every full line in a specified direction disjoint
from the affine span of each higher-codimension cell. -/
@[simp]
theorem isGeneric_singularDiscriminant_iff (C : FinitePolyhedralComplex h)
    (vectors : Finset V) (Q : V) :
    (C.singularDiscriminant vectors).IsGeneric Q ↔
      ∀ P ∈ (C.codimensionAtLeast 2).cells, ∀ n ∈ vectors, ∀ t : ℝ,
        Q + t • n ∉ affineSpan ℝ P := by
  have := h.finiteDimensional
  exact ExceptionalArrangement.isGeneric_ofSweeps_iff _ _ _ Q

/-- Every full line from a generic endpoint in a specified direction misses
the entire codimension-at-least-two skeleton. -/
theorem add_smul_notMem_support_codimensionAtLeast_two (C : FinitePolyhedralComplex h)
    {vectors : Finset V} {Q : V} (hQ : (C.singularDiscriminant vectors).IsGeneric Q)
    {n : V} (hn : n ∈ vectors) (t : ℝ) :
    Q + t • n ∉ (C.codimensionAtLeast 2).support := by
  intro ht
  obtain ⟨P, hP, htP⟩ := mem_support.mp ht
  exact (C.isGeneric_singularDiscriminant_iff vectors Q).mp hQ P hP n hn t
    (subset_affineSpan ℝ P htP)

/-- In particular, rays from generic endpoints cannot encounter a wall
boundary or a joint of the complex. -/
theorem add_smul_notMem_singularSupport_walls (C : FinitePolyhedralComplex h)
    {vectors : Finset V} {Q : V} (hQ : (C.singularDiscriminant vectors).IsGeneric Q)
    {n : V} (hn : n ∈ vectors) (t : ℝ) :
    Q + t • n ∉ Convex.singularSupport (fun W : C.walls => (W : Set V)) :=
  fun ht => C.add_smul_notMem_support_codimensionAtLeast_two hQ hn t
    (C.singularSupport_walls_subset_support_codimensionAtLeast ht)

end Mei.FinitePolyhedralComplex
