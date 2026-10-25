/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Cone.MinkowskiWeyl
public import Mei.Geometry.Convex.Cone.Slice
public import Mei.Geometry.Convex.Polyhedron.Homogenization.Inequalities

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

namespace PointedCone

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The recession cone of the carrier of a pointed cone is the cone itself. -/
@[simp]
theorem recessionCone_coe (C : PointedCone ℝ V) : Mei.Convex.recessionCone (C : Set V) = C := by
  ext v
  constructor
  · intro hv
    simpa using hv 0 C.zero_mem 1 zero_le_one
  · intro hv x hx t ht
    exact C.add_mem hx (PointedCone.smul_mem C ht hv)

end Algebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A pointed cone with a finite continuous affine inequality presentation has
a finite homogeneous inequality presentation, even in infinite dimension. -/
theorem dualFG_of_isConvexPolyhedron (C : PointedCone ℝ V)
    (hC : TauCeti.IsConvexPolyhedron (C : Set V)) :
    C.DualFG (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V) := by
  classical
  obtain ⟨n, g, hg⟩ := TauCeti.isConvexPolyhedron_iff.mp hC
  have hne : {x : V | ∀ i, g i x ≤ 0}.Nonempty := by
    rw [← hg]
    exact ⟨0, C.zero_mem⟩
  have hlin (x : V) : x ∈ C ↔ ∀ i, (g i).linear x ≤ 0 := by
    calc
      x ∈ C ↔ x ∈ Mei.Convex.recessionCone (C : Set V) := by rw [C.recessionCone_coe]
      _ ↔ x ∈ Mei.Convex.recessionCone {x : V | ∀ i, g i x ≤ 0} := by rw [hg]
      _ ↔ ∀ i, (g i).linear x ≤ 0 := by
        simpa only [ContinuousAffineMap.coe_toAffineMap] using
          (Mei.Convex.mem_recessionCone_setOf_forall_iff
            (g := fun i => (g i).toAffineMap) hne (v := x))
  refine ⟨Finset.univ.image (fun i => -(g i).linear), ?_⟩
  ext x
  constructor
  · intro hx
    apply (hlin x).mpr
    intro i
    have hi := hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    simpa using hi
  · intro hx f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    simpa using (hlin x).mp hx i

variable [FiniteDimensional ℝ V]

/-- A convex polyhedral pointed cone is finitely generated, allowing lineality. -/
theorem fg_of_isConvexPolyhedron (C : PointedCone ℝ V)
    (hC : TauCeti.IsConvexPolyhedron (C : Set V)) : C.FG :=
  (C.dualFG_of_isConvexPolyhedron hC).fg

/-- Real finite-dimensional pointed cones are finitely generated exactly when
their carriers are convex polyhedra. -/
theorem fg_iff_isConvexPolyhedron {C : PointedCone ℝ V} :
    C.FG ↔ TauCeti.IsConvexPolyhedron (C : Set V) :=
  ⟨Submodule.FG.cone_isConvexPolyhedron, C.fg_of_isConvexPolyhedron⟩

end PointedCone

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {P : Set V}

/-- The actual recession cone of every convex polyhedron is finitely generated.
For the empty polyhedron, the recession cone is the whole ambient space. -/
theorem fg_recessionCone (hP : TauCeti.IsConvexPolyhedron P) : (Mei.Convex.recessionCone P).FG :=
  (Mei.Convex.recessionCone P).fg_of_isConvexPolyhedron
    (Mei.Convex.isConvexPolyhedron_recessionCone hP)

/-- The carrier-defined closed homogenization of every convex polyhedron is
finitely generated. The empty carrier has the zero homogenization cone. -/
theorem fg_homogenization (hP : TauCeti.IsConvexPolyhedron P) :
    (Mei.Convex.homogenization P).FG := by
  rcases P.eq_empty_or_nonempty with h | hne
  · subst P
    rw [Mei.Convex.homogenization_empty]
    exact Submodule.fg_bot
  · exact (Mei.Convex.homogenization P).fg_of_isConvexPolyhedron
      (Mei.Convex.isConvexPolyhedron_homogenization hP hne)

/-- **Affine Minkowski–Weyl:** a nonempty convex polyhedron is the sum of a
finite convex hull of its own points and its actual recession cone. -/
theorem exists_finset_convexHull_add_recessionCone (hP : TauCeti.IsConvexPolyhedron P)
    (hne : P.Nonempty) :
    ∃ Q : Finset V, (Q : Set V) ⊆ P ∧
      P = convexHull ℝ (Q : Set V) + (Mei.Convex.recessionCone P : Set V) := by
  classical
  obtain ⟨s, hs⟩ := hP.fg_homogenization
  change PointedCone.hull ℝ (s : Set (V × ℝ)) = Mei.Convex.homogenization P at hs
  have hsheight : ∀ z ∈ s, 0 ≤ z.2 := by
    intro z hz
    apply Mei.Convex.homogenization_height_nonneg
    rw [← hs]
    exact PointedCone.subset_hull hz
  have hone : {x : V | (x, (1 : ℝ)) ∈ PointedCone.hull ℝ (s : Set (V × ℝ))} = P := by
    ext x
    change (x, (1 : ℝ)) ∈ PointedCone.hull ℝ (s : Set (V × ℝ)) ↔ x ∈ P
    rw [hs]
    exact hP.convex.mem_homogenization_one_iff hP.isClosed
  have hzero : (PointedCone.hull ℝ (Finset.zeroSliceGenerators s : Set V) : Set V) =
      (Mei.Convex.recessionCone P : Set V) := by
    rw [← Finset.slice_zero_hull s hsheight]
    ext x
    change (x, (0 : ℝ)) ∈ PointedCone.hull ℝ (s : Set (V × ℝ)) ↔
      x ∈ Mei.Convex.recessionCone P
    rw [hs]
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
          (Mei.Convex.recessionCone P : Set V) := by rw [hzero]

end TauCeti.IsConvexPolyhedron
