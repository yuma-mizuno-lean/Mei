/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Cone.FiniteGeneration
public import Mei.Geometry.Convex.Cone.FiniteDuality
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Minkowski–Weyl duality for pointed cones

In finite-dimensional spaces over a linearly ordered field, finite generation
is equivalent to having finitely many defining linear inequalities. The two
directions combine finite generation under halfspace cuts with the algebraic
separation theorem for finitely generated cones. No topological closedness is
assumed in this argument, and cones with lineality are allowed.

For real finite-dimensional normed spaces, a finite inequality presentation is
also a convex polyhedron in the existing supplier's sense. Thus finitely
generated cones are closed as a consequence of the algebraic theorem.
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

/-- Finitely generated real cones are closed. This follows from the finite
inequality theorem rather than being assumed for algebraic separation. -/
theorem cone_isClosed (hC : C.FG) : IsClosed (C : Set V) :=
  hC.cone_isConvexPolyhedron.isClosed

end Submodule.FG
