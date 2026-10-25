/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Basic
public import Mei.RingTheory.FilteredAlgebra.Map
public import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# Pure tensors in completed tensor products

The inclusions of two filtered algebras in their tensor product extend to their
completions. Their images commute, so their product defines an `R`-bilinear,
multiplicative pure-tensor map into the completion for the total-degree filtration.
At each order this map depends only on the two finite-order classes. In particular,
it can be used to state group-like and primitive identities for completed coproducts.

The construction uses `Mei.AlgFiltration.mapCompletion` and Mathlib's algebra tensor
inclusions, rather than choosing representatives of elements of either completion.
The two algebras may be noncommutative; no flatness or separatedness is required.
-/

public section

open scoped TensorProduct

namespace Mei.AlgFiltration

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] (F : Mei.AlgFiltration A) (G : Mei.AlgFiltration B)

/-- The left inclusion into the completed total-degree tensor product. -/
noncomputable def includeLeftCompletion :
    F.completion →ₐ[R] (F.tensorProduct R G).completion where
  __ := F.mapCompletion (F.tensorProduct R G)
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
    id monotone_id (fun _ _ hx => F.includeLeft_mem_tensorProduct R G hx)
  commutes' r := by
    apply (F.tensorProduct R G).completion_ext
    intro k
    refine (F.projection_mapCompletion _ _ id monotone_id _ k _).trans ?_
    simp [Ideal.quotientMap_algebraMap, -Algebra.TensorProduct.algebraMap_apply]

/-- The right inclusion into the completed total-degree tensor product. -/
noncomputable def includeRightCompletion :
    G.completion →ₐ[R] (F.tensorProduct R G).completion where
  __ := G.mapCompletion (F.tensorProduct R G)
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    id monotone_id (fun _ _ hx => F.includeRight_mem_tensorProduct R G hx)
  commutes' r := by
    apply (F.tensorProduct R G).completion_ext
    intro k
    refine (G.projection_mapCompletion _ _ id monotone_id _ k _).trans ?_
    simp [Ideal.quotientMap_algebraMap, -Algebra.TensorProduct.algebraMap_apply]

/-- Finite-order projection of the completed left inclusion. -/
@[simp]
theorem projection_includeLeftCompletion (k : ℕ) (x : F.completion) :
    (F.tensorProduct R G).projection k (F.includeLeftCompletion (R := R) G x) =
      Ideal.quotientMap ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
        (fun _ hx => F.includeLeft_mem_tensorProduct R G hx) (F.projection k x) := by
  exact F.projection_mapCompletion _ _ id monotone_id _ k x

/-- Finite-order projection of the completed right inclusion. -/
@[simp]
theorem projection_includeRightCompletion (k : ℕ) (y : G.completion) :
    (F.tensorProduct R G).projection k (F.includeRightCompletion (R := R) G y) =
      Ideal.quotientMap ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
        (fun _ hy => F.includeRight_mem_tensorProduct R G hy) (G.projection k y) := by
  exact G.projection_mapCompletion _ _ id monotone_id _ k y

/-- The completed left inclusion extends the ordinary tensor inclusion. -/
@[simp]
theorem includeLeftCompletion_toCompletion (a : A) :
    F.includeLeftCompletion (R := R) G (F.toCompletion a) =
      (F.tensorProduct R G).toCompletion (a ⊗ₜ[R] (1 : B)) := by
  exact F.mapCompletion_toCompletion _ _ id monotone_id _ a

/-- The completed right inclusion extends the ordinary tensor inclusion. -/
@[simp]
theorem includeRightCompletion_toCompletion (b : B) :
    F.includeRightCompletion (R := R) G (G.toCompletion b) =
      (F.tensorProduct R G).toCompletion ((1 : A) ⊗ₜ[R] b) := by
  exact G.mapCompletion_toCompletion _ _ id monotone_id _ b

/-- The two completed tensor inclusions have commuting images. -/
theorem commute_includeLeftCompletion_includeRightCompletion
    (x : F.completion) (y : G.completion) :
    Commute (F.includeLeftCompletion (R := R) G x) (F.includeRightCompletion (R := R) G y) := by
  apply (F.tensorProduct R G).completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (G.projection k y)
  simp only [map_mul, projection_includeLeftCompletion, projection_includeRightCompletion]
  simp [← ha, ← hb, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The bilinear pure-tensor map from the completions into the completed tensor product. -/
noncomputable def completedTensor :
    F.completion →ₗ[R] G.completion →ₗ[R] (F.tensorProduct R G).completion :=
  (LinearMap.mul R (F.tensorProduct R G).completion).compl₁₂
    (F.includeLeftCompletion (R := R) G).toLinearMap
    (F.includeRightCompletion (R := R) G).toLinearMap

/-- A completed pure tensor is the product of its completed tensor inclusions. -/
theorem completedTensor_apply (x : F.completion) (y : G.completion) :
    F.completedTensor (R := R) G x y =
      F.includeLeftCompletion (R := R) G x * F.includeRightCompletion (R := R) G y :=
  (rfl)

/-- Projection of a completed pure tensor is computed using only the order-`k` classes. -/
@[simp]
theorem projection_completedTensor (k : ℕ) (x : F.completion) (y : G.completion) :
    (F.tensorProduct R G).projection k (F.completedTensor (R := R) G x y) =
      Ideal.quotientMap ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
        (fun _ hx => F.includeLeft_mem_tensorProduct R G hx) (F.projection k x) *
      Ideal.quotientMap ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
        (fun _ hy => F.includeRight_mem_tensorProduct R G hy) (G.projection k y) := by
  simp [completedTensor_apply]

/-- Any representatives of the two finite-order classes compute the projected tensor. -/
theorem projection_completedTensor_of_representatives (k : ℕ)
    (x : F.completion) (y : G.completion) (a : A) (b : B)
    (ha : Ideal.Quotient.mk (F.ideal (k + 1)) a = F.projection k x)
    (hb : Ideal.Quotient.mk (G.ideal (k + 1)) b = G.projection k y) :
    (F.tensorProduct R G).projection k (F.completedTensor (R := R) G x y) =
      Ideal.Quotient.mk ((F.tensorProduct R G).ideal (k + 1)) (a ⊗ₜ[R] b) := by
  simp [projection_completedTensor, ← ha, ← hb, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Completing an ordinary pure tensor agrees with tensoring the canonical images. -/
@[simp]
theorem completedTensor_toCompletion (a : A) (b : B) :
    F.completedTensor (R := R) G (F.toCompletion a) (G.toCompletion b) =
      (F.tensorProduct R G).toCompletion (a ⊗ₜ[R] b) := by
  simp [completedTensor_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The completed tensor map is multiplicative in pairs of factors. -/
theorem completedTensor_mul (x x' : F.completion) (y y' : G.completion) :
    F.completedTensor (R := R) G (x * x') (y * y') =
      F.completedTensor (R := R) G x y * F.completedTensor (R := R) G x' y' := by
  simp only [completedTensor_apply, map_mul]
  exact (F.commute_includeLeftCompletion_includeRightCompletion (R := R) G x' y).symm
    |>.mul_mul_mul_comm _ _ |>.symm

/-- Tensoring with the right unit is the completed left inclusion. -/
@[simp]
theorem completedTensor_one_right (x : F.completion) :
    F.completedTensor (R := R) G x 1 = F.includeLeftCompletion (R := R) G x := by
  simp [completedTensor_apply]

/-- Tensoring with the left unit is the completed right inclusion. -/
@[simp]
theorem completedTensor_one_left (y : G.completion) :
    F.completedTensor (R := R) G 1 y = F.includeRightCompletion (R := R) G y := by
  simp [completedTensor_apply]

end Mei.AlgFiltration
