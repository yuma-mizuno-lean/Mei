/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Cone.FiniteGeneration
public import Mei.Geometry.Convex.Cone.FiniteDuality
public import Mei.Geometry.Convex.Recession
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Minkowski–Weyl duality for pointed cones

In finite-dimensional spaces over a linearly ordered field, finite generation
is equivalent to having finitely many defining linear inequalities. The two
directions combine finite generation under halfspace cuts with the algebraic
separation theorem for finitely generated cones. No topological closedness is
assumed in this argument, and cones with lineality are allowed.

For real finite-dimensional normed spaces, finite generation is also equivalent
to the carrier being a convex polyhedron in the existing supplier's sense. Thus
finitely generated cones are closed in every real normed space, by restricting to
their finite-dimensional linear span.
-/

public section

namespace Submodule.FG

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] {C : PointedCone K V}

/-- A finitely generated cone in a finite-dimensional space is cut out by
finitely many algebraic linear inequalities under evaluation. -/
theorem cone_dualFG (hC : C.FG) :
    C.DualFG (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) := by
  let p : Module.Dual K V →ₗ[K] Module.Dual K V := LinearMap.id
  have hdual : (PointedCone.dual p.flip C).FG :=
    (PointedCone.DualFG.dual_of_fg p.flip hC).fg
  have hresult := PointedCone.DualFG.dual_of_fg p hdual
  rwa [hC.cone_dual_dual_flip_id] at hresult

end Submodule.FG

namespace PointedCone

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] {C : PointedCone K V}

/-- **Minkowski–Weyl:** a pointed cone is finitely generated exactly when it is
cut out by finitely many linear halfspaces, including when it has lineality. -/
theorem fg_iff_dualFG :
    C.FG ↔ C.DualFG (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) :=
  ⟨Submodule.FG.cone_dualFG, DualFG.fg⟩

end PointedCone

namespace Submodule.FG

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V}

/-- A finitely generated real cone is a convex polyhedron, via its finite
linear inequality presentation. -/
theorem cone_isConvexPolyhedron (hC : C.FG) : TauCeti.IsConvexPolyhedron (C : Set V) := by
  obtain ⟨s, hs⟩ := hC.cone_dualFG
  let row (f : s) : V →ᴬ[ℝ] ℝ :=
    -(ContinuousLinearMap.toContinuousAffineMap
      ⟨(f : Module.Dual ℝ V), (f : Module.Dual ℝ V).continuous_of_finiteDimensional⟩)
  have he : (PointedCone.dual
      (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V) s : Set V) =
      {x : V | ∀ f : s, row f x ≤ 0} := by
    ext x
    simp only [SetLike.mem_coe, PointedCone.mem_dual, LinearMap.id_apply,
      Set.mem_ofPred_eq, row, ContinuousAffineMap.neg_apply,
      ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.coe_mk', neg_nonpos]
    constructor
    · intro h f
      exact h f.property
    · intro h f hf
      exact h ⟨f, hf⟩
  rw [← hs, he]
  exact TauCeti.isConvexPolyhedron_setOf_forall row

omit [FiniteDimensional ℝ V] in
/-- Finitely generated real cones are closed, even in infinite-dimensional spaces.
This follows from the finite inequality theorem on their linear span, rather than
being assumed for algebraic separation. -/
theorem cone_isClosed (hC : C.FG) : IsClosed (C : Set V) := by
  -- Restrict to the finite-dimensional real span before using the inequality theorem.
  let P := Submodule.span ℝ (C : Set V)
  have hP : P.FG := hC.span
  have : FiniteDimensional ℝ P := Module.Finite.of_fg hP
  let i := P.subtype.restrictScalars (Nonneg ℝ)
  let D : PointedCone ℝ P := Submodule.comap i C
  have hmap : Submodule.map i D = C := by
    apply Submodule.map_comap_eq_of_le
    intro x hx
    exact ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
  have hD : D.FG := Submodule.fg_of_fg_map_injective i Subtype.val_injective (hmap.symm ▸ hC)
  have hclosed := hD.cone_isConvexPolyhedron.isClosed
  have himage : Subtype.val '' (D : Set P) = (C : Set V) := by
    exact congrArg (fun S : PointedCone ℝ V => (S : Set V)) hmap
  rw [← himage]
  exact P.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isClosedMap _ hclosed

end Submodule.FG

namespace PointedCone

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
      x ∈ C ↔ x ∈ Set.recessionCone (C : Set V) := by rw [C.recessionCone_coe]
      _ ↔ x ∈ Set.recessionCone {x : V | ∀ i, g i x ≤ 0} := by rw [hg]
      _ ↔ ∀ i, (g i).linear x ≤ 0 := by
        simpa only [ContinuousAffineMap.coe_toAffineMap] using
          (Set.mem_recessionCone_setOf_forall_iff
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
