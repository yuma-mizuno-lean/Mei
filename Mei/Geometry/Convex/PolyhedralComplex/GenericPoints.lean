/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus

/-!
# Coefficient points avoiding countably many exceptional arrangements

On the regular locus of a finite polyhedral complex, off-wall coefficient points
remain dense after imposing any countable family of exceptional-arrangement
conditions. The existing simultaneous-arrangement density theorem is pulled
back to the open regular locus and intersected with the dense coefficient points.
This supplies a dense domain for extending geometrically defined coefficients
to an ambient transport sheaf.
-/

public noncomputable section

open Set Mei.Convex TopologicalSpace

namespace TauCeti.FinitePolyhedralComplex

variable {N V J : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

/-- Off-wall coefficient points satisfying every arrangement condition. -/
abbrev arrangementCoefficientPoints (A : J → ExceptionalArrangement ℝ V) :=
  {x : C.coefficientPoints // ∀ j, (A j).IsGeneric x.val.val}

/-- Simultaneous genericity for a countable family of arrangements preserves density
in the full regular locus, including its regular wall points. -/
theorem denseRange_arrangementCoefficientPoints [Countable J]
    (A : J → ExceptionalArrangement ℝ V) :
    DenseRange (fun x : C.arrangementCoefficientPoints A => x.val.val) := by
  let := h.finiteDimensional
  have hdAll : Dense {x : C.regularSpace | ∀ j, (A j).IsGeneric x.val} :=
    (ExceptionalArrangement.dense_iInter_isGeneric A).preimage
      C.isOpen_regularLocus.isOpenMap_subtype_val
  have hdPoints := C.dense_coefficientPoints.inter_of_isOpen_left hdAll C.isOpen_coefficientPoints
  unfold DenseRange
  apply hdPoints.mono
  rintro x ⟨hx, hA⟩
  exact ⟨⟨⟨x, hx⟩, hA⟩, rfl⟩
end TauCeti.FinitePolyhedralComplex
