/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Coefficient maps preserve monoid-algebra gradings

Changing coefficients preserves the pieces of any grading given by a degree
function on monomials. Coefficients may vanish under the map. This supplies
homogeneous coefficient maps for correspondences between monoid algebras.
-/

public section

namespace AddMonoidAlgebra

variable {K R S M ι : Type*} [CommSemiring K] [CommSemiring R] [CommSemiring S]
  [Algebra K R] [Algebra K S] [AddMonoid M]

/-- Coefficient change preserves homogeneous support for an arbitrary degree function. -/
theorem mapAlgHom_mem_gradeBy (φ : R →ₐ[K] S) {f : M → ι} {i : ι} {u : R[M]}
    (hu : u ∈ gradeBy R f i) : mapAlgHom M φ u ∈ gradeBy S f i := by
  exact fun m hm => hu m (Finsupp.support_mapRange (hf := φ.map_zero) hm)

end AddMonoidAlgebra
