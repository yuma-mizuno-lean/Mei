/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Basic

/-!
# Comparing endpoints of admissible paths

The vertex list determines the endpoints even when the paths use different wall families.
-/

public section

open TauCeti (WallComplement AdmissiblePLPath)

namespace Quiver.Path

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y : WallComplement W}

/-- Polygonal paths with the same vertex list have the same endpoints, even for different
wall families. -/
theorem endpoints_val_eq_of_vertices_eq {κ : Type*} {W' : κ → Set V}
    {x' y' : WallComplement W'} (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    x.val = x'.val ∧ y.val = y'.val :=
  ⟨by simpa using congrArg List.head? hpq,
    by simpa [List.getLast?_eq_getLast_of_ne_nil p.vertices_ne_nil,
      List.getLast?_eq_getLast_of_ne_nil q.vertices_ne_nil] using congrArg List.getLast? hpq⟩

end Quiver.Path
