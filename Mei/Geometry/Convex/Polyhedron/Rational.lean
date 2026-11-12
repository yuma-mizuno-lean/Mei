/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic
public import Mei.Geometry.Toric.Algebraic.RationalFunctional

/-!
# Rational offsets under finite reindexing

Finite reindexing of affine constraints preserves rational offsets.
-/

public section

namespace TauCeti.RationalAffinePolyhedron

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- Finite reindexing preserves rational affine offsets. -/
theorem hasRationalOffsets_ofFinite {ι : Type*} [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, TauCeti.Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (ho : ∀ j, ∃ q : ℚ, g j 0 = (q : ℝ)) : (ofFinite g hg).HasRationalOffsets := by
  exact (hasRationalOffsets_ofFinite_iff hg).2 ho

end TauCeti.RationalAffinePolyhedron
