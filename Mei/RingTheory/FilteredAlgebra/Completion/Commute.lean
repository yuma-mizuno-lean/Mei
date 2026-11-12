/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.RingTheory.FilteredAlgebra.Completion

/-!
# Commutativity of filtered completions

If all elements of a filtered ring commute, then so do all elements of its completion: each
finite-order projection lands in a quotient of the original ring, and elements of the
completion are determined by their projections. This applies to rings whose multiplication
is commutative but which carry only a `Ring` structure, such as subalgebras of twisted
monoid algebras at a trivial factor set.
-/

public section

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] (F : AlgFiltration A)

/-- If all elements of a filtered ring commute, then all elements of its completion commute. -/
theorem commute_completion (h : ∀ x y : A, Commute x y) (a b : F.completion) :
    Commute a b := by
  refine F.completion_ext fun k => ?_
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (F.projection k a)
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (F.projection k b)
  rw [map_mul, map_mul, ← hu, ← hv, ← map_mul, ← map_mul, (h u v).eq]

end TauCeti.AlgFiltration
