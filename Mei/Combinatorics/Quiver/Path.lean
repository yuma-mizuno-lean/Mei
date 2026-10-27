/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.List.Chain

/-!
# Vertices and reversal of paths under prefunctors

A prefunctor preserving reversal of edges also preserves reversal of paths.
This extends Mathlib's `Prefunctor.MapReverse` API to `Prefunctor.mapPath`,
so that geometric projections of polygonal paths can use the same reversal law.
A prefunctor also applies its object map to the vertex list, allowing geometric
paths to be compared after forgetting some of their admissibility conditions.
Relations between consecutive vertices can be checked separately on each part
of a concatenation, using Mathlib's `List.isChain_split` at the common endpoint.
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

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- A relation holds between consecutive vertices of a concatenated path exactly when
it holds along both paths. The common endpoint is counted only once. -/
theorem isChain_vertices_comp {x y z : V} (p : Path x y) (q : Path y z)
    (r : V → V → Prop) :
    (p.comp q).vertices.IsChain r ↔ p.vertices.IsChain r ∧ q.vertices.IsChain r := by
  have hq : y :: q.vertices.tail = q.vertices :=
    List.cons_head?_tail (by simp)
  rw [vertices_comp, ← hq, List.isChain_split, dropLast_append_end_eq, hq]

variable {V : Type*} [Quiver V] [Quiver.HasReverse V]

/-- Reversing a path reverses its entire vertex list. -/
@[simp]
theorem vertices_reverse {x y : V} (p : Path x y) :
    p.reverse.vertices = p.vertices.reverse := by
  induction p with
  | nil => simp
  | cons p e ih => simp [Path.reverse, ih]

end Quiver.Path
