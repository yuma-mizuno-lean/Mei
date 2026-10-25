/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Cone.MinkowskiWeyl
public import Mei.Geometry.Convex.Cone.Slice
public import Mei.Geometry.Convex.Polyhedron.Homogenization.Inequalities
public import Mei.Geometry.Convex.Polyhedron.Recession

/-!
# Affine Minkowski–Weyl decomposition

Every convex polyhedron in a finite-dimensional real normed space has a finitely
generated carrier-defined homogenization and recession cone. A nonempty such
polyhedron is the sum of the convex hull of finitely many of its points and its
actual recession cone. Unbounded sets and lineality are allowed.

The proof derives finite generation from affine inequalities, then applies the
height-one and height-zero slice theorems to the actual homogenization.
-/

public section

open scoped Pointwise

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {P : Set V}

/-- The actual recession cone of every convex polyhedron is finitely generated.
For the empty polyhedron, the recession cone is the whole ambient space. -/
theorem fg_recessionCone (hP : TauCeti.IsConvexPolyhedron P) : (Set.recessionCone P).FG :=
  (Set.recessionCone P).fg_of_isConvexPolyhedron
    (Mei.Convex.isConvexPolyhedron_recessionCone hP)

/-- The carrier-defined closed homogenization of every convex polyhedron is
finitely generated. The empty carrier has the zero homogenization cone. -/
theorem fg_homogenization (hP : TauCeti.IsConvexPolyhedron P) :
    (Set.homogenization P).FG := by
  rcases P.eq_empty_or_nonempty with h | hne
  · subst P
    rw [Set.homogenization_empty]
    exact Submodule.fg_bot
  · exact (Set.homogenization P).fg_of_isConvexPolyhedron
      (Mei.Convex.isConvexPolyhedron_homogenization hP hne)

/-- **Affine Minkowski–Weyl:** a nonempty convex polyhedron is the sum of a
finite convex hull of its own points and its actual recession cone. -/
theorem exists_finset_convexHull_add_recessionCone (hP : TauCeti.IsConvexPolyhedron P)
    (hne : P.Nonempty) :
    ∃ Q : Finset V, (Q : Set V) ⊆ P ∧
      P = convexHull ℝ (Q : Set V) + (Set.recessionCone P : Set V) := by
  classical
  obtain ⟨s, hs⟩ := hP.fg_homogenization
  -- `FG` gives a submodule span over nonnegative scalars. `PointedCone.hull` abbreviates
  -- that span, so `change` presents it in the form required by the slice lemmas.
  change PointedCone.hull ℝ (s : Set (V × ℝ)) = Set.homogenization P at hs
  have hsheight : ∀ z ∈ s, 0 ≤ z.2 := by
    intro z hz
    apply Set.homogenization_height_nonneg
    rw [← hs]
    exact PointedCone.subset_hull hz
  have hone : {x : V | (x, (1 : ℝ)) ∈ PointedCone.hull ℝ (s : Set (V × ℝ))} = P := by
    ext x
    simp only [Set.mem_ofPred_eq, hs]
    exact hP.convex.mem_homogenization_one_iff hP.isClosed
  have hzero : (PointedCone.hull ℝ (Finset.zeroSliceGenerators s : Set V) : Set V) =
      (Set.recessionCone P : Set V) := by
    rw [← Finset.slice_zero_hull s hsheight]
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, hs]
    exact hP.convex.mem_homogenization_zero_iff hne hP.isClosed
  refine ⟨Finset.positiveSliceGenerators s, ?_, ?_⟩
  · intro x hx
    apply (hP.convex.mem_homogenization_one_iff hP.isClosed).mp
    rw [← hs]
    exact Finset.mem_hull_one_of_mem_positiveSliceGenerators hx
  · calc
      P = {x : V | (x, (1 : ℝ)) ∈ PointedCone.hull ℝ (s : Set (V × ℝ))} := hone.symm
      _ = convexHull ℝ (Finset.positiveSliceGenerators s : Set V) +
          (PointedCone.hull ℝ (Finset.zeroSliceGenerators s : Set V) : Set V) :=
        Finset.slice_one_hull s hsheight
      _ = convexHull ℝ (Finset.positiveSliceGenerators s : Set V) +
          (Set.recessionCone P : Set V) := by rw [hzero]

end TauCeti.IsConvexPolyhedron
