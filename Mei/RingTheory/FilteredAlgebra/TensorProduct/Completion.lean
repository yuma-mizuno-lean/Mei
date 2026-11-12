/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Map
public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Basic
public import Mei.RingTheory.FilteredAlgebra.Module
public import Mei.LinearAlgebra.ModuleFiltration.Bilinear

/-!
# Comparing completed algebra tensors and module pairings

The completed tensor over the coefficient ring agrees with the completed
bilinear pairing under the module and algebra completion equivalences.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

open Mei

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] (F : TauCeti.AlgFiltration A) (G : TauCeti.AlgFiltration B)

/-- The completed tensor is the generic completed bilinear pairing under the
canonical module/algebra completion comparisons. -/
theorem completedTensor_apply_eq_completionBilinear (x : F.completion) (y : G.completion) :
    F.completedTensor (R := R) G x y =
      (F.tensorProduct R G).moduleCompletionEquiv
        (ModuleFiltration.completionBilinear
          (F.toModuleFiltration R) (G.toModuleFiltration R)
          ((F.tensorProduct R G).toModuleFiltration R)
          (TensorProduct.mk R A B) (F.tmul_mem_tensorProduct R G)
          ((F.moduleCompletionEquiv (R := R)).symm x)
          ((G.moduleCompletionEquiv (R := R)).symm y)) := by
  apply (F.tensorProduct R G).completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (G.projection k y)
  rw [F.projection_completedTensor_of_representatives R G k x y a b ha hb,
    projection_moduleCompletionEquiv,
    ModuleFiltration.projection_completionBilinear _ _ _ _ (F.tmul_mem_tensorProduct R G),
    F.projection_moduleCompletionEquiv_symm_of_mk k x a ha,
    G.projection_moduleCompletionEquiv_symm_of_mk k y b hb,
    ModuleFiltration.quotientBilinear_mk _ _ _ _ (F.tmul_mem_tensorProduct R G)]
  simp only [Submodule.Quotient.restrictScalarsEquiv_mk, Ideal.Quotient.mk_eq_mk,
    TensorProduct.mk_apply]

/-- Projection of a completed pure tensor is computed using only the order-`k` classes. -/
@[simp]
theorem projection_completedTensor (k : ℕ) (x : F.completion) (y : G.completion) :
    (F.tensorProduct R G).projection k (F.completedTensor (R := R) G x y) =
      Ideal.quotientMapₐ ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
        (F.ideal_le_comap_includeLeft R G (k + 1)) (F.projection k x) *
      Ideal.quotientMapₐ ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
        (F.ideal_le_comap_includeRight R G (k + 1)) (G.projection k y) := by
  rw [completedTensor_apply, map_mul, projection_includeLeftCompletion,
    projection_includeRightCompletion]

end TauCeti.AlgFiltration
