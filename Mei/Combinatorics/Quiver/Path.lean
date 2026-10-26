/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Vertices and reversal of paths under prefunctors

A prefunctor preserving reversal of edges also preserves reversal of paths.
This extends Mathlib's `Prefunctor.MapReverse` API to `Prefunctor.mapPath`,
so that geometric projections of polygonal paths can use the same reversal law.
A prefunctor also applies its object map to the vertex list, allowing geometric
paths to be compared after forgetting some of their admissibility conditions.
-/

public section

namespace Prefunctor

variable {U V : Type*} [Quiver U] [Quiver V]

/-- A prefunctor applies its object map to every vertex of a path. -/
@[simp]
theorem vertices_mapPath (F : U ⥤q V) {x y : U} (p : Quiver.Path x y) :
    (F.mapPath p).vertices = p.vertices.map F.obj := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

variable {U V : Type*} [Quiver U] [Quiver V]
  [Quiver.HasReverse U] [Quiver.HasReverse V]

/-- A prefunctor preserving edge reversal preserves reversal of entire paths. -/
@[simp]
theorem mapPath_reverse (F : U ⥤q V) [F.MapReverse] {x y : U} (p : Quiver.Path x y) :
    F.mapPath p.reverse = (F.mapPath p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Quiver.Path.reverse, mapPath_comp, mapPath_toPath, mapPath_cons, ih,
      map_reverse]

end Prefunctor
