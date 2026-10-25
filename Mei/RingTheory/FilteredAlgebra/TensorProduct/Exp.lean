/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Completion
public import Mei.RingTheory.FilteredAlgebra.Exp

/-!
# Exponentials in completed tensor products

The completed tensor inclusions commute with exponential coordinates. In
particular, the tensor square of an exponential is the exponential of the sum
of its left and right inclusions. These identities take place in the completion
for total tensor degree, allowing coproduct identities to be exponentiated.

We use Mathlib's `IsNilpotent.map_exp` at each finite order, Mei's
`AlgFiltration.completedExp_add`, and commutation of the two completed tensor
inclusions.
-/

public section

open scoped TensorProduct

namespace Mei.AlgFiltration

variable {R A B : Type*} [CommRing R]
  [Ring A] [Ring B] [Algebra R A] [Algebra R B] [Algebra ℚ A]
  (F : AlgFiltration A) (G : AlgFiltration B)

/-- The completed left tensor inclusion commutes with exponentiation. -/
theorem includeLeftCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeLeftCompletion (R := R) G (F.completedExp x) =
      (F.tensorProduct R G).completedExp
        ⟨F.includeLeftCompletion (R := R) G x,
          F.includeLeftCompletion_mem_completionIdeal G x.property⟩ := by
  apply (F.tensorProduct R G).completion_ext
  intro k
  simp only [projection_includeLeftCompletion, projection_completedExp]
  exact (F.isNilpotent_projection x.property k).map_exp _

variable [Algebra ℚ B]

/-- The completed right tensor inclusion commutes with exponentiation. -/
theorem includeRightCompletion_completedExp (y : G.completionIdeal 1) :
    F.includeRightCompletion (R := R) G (G.completedExp y) =
      (F.tensorProduct R G).completedExp
        ⟨F.includeRightCompletion (R := R) G y,
          F.includeRightCompletion_mem_completionIdeal G y.property⟩ := by
  apply (F.tensorProduct R G).completion_ext
  intro k
  simp only [projection_includeRightCompletion, projection_completedExp]
  exact (G.isNilpotent_projection y.property k).map_exp _

/-- A tensor of exponentials is the exponential of the sum of the two inclusions. -/
theorem completedTensor_completedExp (x : F.completionIdeal 1) (y : G.completionIdeal 1) :
    F.completedTensor (R := R) G (F.completedExp x) (G.completedExp y) =
      (F.tensorProduct R G).completedExp
        (⟨F.includeLeftCompletion (R := R) G x,
            F.includeLeftCompletion_mem_completionIdeal G x.property⟩ +
          ⟨F.includeRightCompletion (R := R) G y,
            F.includeRightCompletion_mem_completionIdeal G y.property⟩) := by
  rw [completedTensor_apply, includeLeftCompletion_completedExp,
    includeRightCompletion_completedExp]
  exact ((F.tensorProduct R G).completedExp_add _ _
    (F.commute_includeLeftCompletion_includeRightCompletion (R := R) G x y)).symm

end Mei.AlgFiltration
