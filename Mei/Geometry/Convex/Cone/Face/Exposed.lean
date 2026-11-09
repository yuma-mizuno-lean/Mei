/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Faces of finitely generated cones are exposed

Every face of a finitely generated cone is the zero set within the cone of a
nonnegative linear functional. This gives supporting hyperplane descriptions,
allowing the zero functional for the full face.
`PointedCone.IsFaceOf.exists_nonneg_linear_inf_ker` expresses this as
an intersection with the functional's kernel, while
`PointedCone.IsFaceOf.exists_nonneg_linear_zero_iff` gives the pointwise criterion.
These algebraic results hold over any linearly ordered field, without finite
dimensionality, topological closedness, or salience assumptions.

In a finite-dimensional real normed space,
`PointedCone.IsFaceOf.isExposed_of_fg` supplies Mathlib's continuous-functional
predicate `IsExposed`, using the negative functional for its maximization convention.
The algebraic construction uses Tucker's theorem and the face property.
Conversely, `IsExposed.exists_isFaceOf_coe_eq` identifies every nonempty exposed
subset of a real cone with a cone face, without a finite-generation assumption.
-/
