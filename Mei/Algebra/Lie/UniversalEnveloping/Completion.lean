/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Coproduct
public import Mei.RingTheory.FilteredAlgebra.AlgHom
public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Completion

/-!
# The completed enveloping coproduct

The coproduct of a nonnegatively graded Lie algebra extends to its degree-completed
enveloping algebra, with values in the completion of the tensor product for total
degree. Its finite-order components are the existing quotient coproducts. The counit
extends through the order-zero projection, since it kills positive-degree words.

These maps define primitive and group-like elements in the completed algebra without
putting a coalgebra structure on the ordinary finite-order quotients. Primitives form
a submodule containing the images of Lie generators; group-like elements form a
submonoid. Both equations can be checked at every finite order.

The construction uses `Mei.AlgFiltration.mapCompletionₐ`, the completed pure-tensor
pairing, and Mathlib's `Ideal.Quotient.liftₐ`. The generator calculation uses
`TauCeti.UniversalEnvelopingAlgebra.comul_ι`. No rational scalars, basis, finite
generation, or separatedness hypothesis is needed.
-/

public section

open scoped TensorProduct

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d hneg
local notation "T" => Mei.AlgFiltration.tensorProduct
  R (degreeFiltration ℒ d hneg) (degreeFiltration ℒ d hneg)
local notation "tensor" => Mei.AlgFiltration.completedTensor (R := R)
  (degreeFiltration ℒ d hneg) (degreeFiltration ℒ d hneg)

/-- The coproduct on the degree completion, valued in the total-degree tensor completion. -/
noncomputable def completedCoproduct : (F).completion →ₐ[R] (T).completion :=
  (F).mapCompletionₐ (T) (Bialgebra.comulAlgHom R U) id monotone_id
    (fun k => by
      rw [Mei.AlgFiltration.tensorProduct_ideal]
      exact degreeFiltration_le_comap_comul ℒ d hneg (k + 1))

/-- The completed coproduct at order `k` is the coproduct modulo total degree `k + 1`. -/
@[simp]
theorem projection_completedCoproduct (k : ℕ) (x : (F).completion) :
    (T).projection k (completedCoproduct ℒ d hneg x) =
      Ideal.quotientEquivAlgOfEq R ((F).tensorProduct_ideal R (F) (k + 1)).symm
        (quotientCoproduct ℒ d hneg (k + 1) ((F).projection k x)) := by
  rw [completedCoproduct, Mei.AlgFiltration.projection_mapCompletionₐ]
  simp only [id_eq]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((F).projection k x)
  rw [← ha, quotientCoproduct_mk, Ideal.quotientEquivAlgOfEq_mk]
  simpa only [Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply] using
    Ideal.quotient_map_mkₐ (I := (F).ideal (k + 1))
      ((T).ideal (k + 1)) (Bialgebra.comulAlgHom R U) _ (x := a)

/-- The completed coproduct extends the enveloping coproduct on canonical elements. -/
@[simp]
theorem completedCoproduct_toCompletion (a : U) :
    completedCoproduct ℒ d hneg ((F).toCompletion a) =
      (T).toCompletion (Coalgebra.comul (R := R) a) := by
  rw [completedCoproduct, Mei.AlgFiltration.mapCompletionₐ_toCompletion,
    Bialgebra.comulAlgHom_apply]

/-- The coproduct preserves every order of the induced completion filtrations. -/
theorem completedCoproduct_mem_completionIdeal (k : ℕ) {x : (F).completion}
    (hx : x ∈ (F).completionIdeal k) :
    completedCoproduct ℒ d hneg x ∈ (T).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    exact (F).mapCompletionₐ_mem_completionIdeal (T) _ id monotone_id _ k hx

/-- The counit on the completion, obtained from the quotient by positive degree. -/
noncomputable def completedCounit : (F).completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ ((F).ideal 1) (Bialgebra.counitAlgHom R U)
    (fun _ ha => RingHom.mem_ker.mp (degreeFiltration_one_le_ker_counit ℒ d hneg ha))).comp
      ((F).projectionₐ 0)

/-- The completed counit is computed from the order-zero quotient. -/
theorem completedCounit_apply (x : (F).completion) :
    completedCounit ℒ d hneg x =
      Ideal.Quotient.liftₐ ((F).ideal 1) (Bialgebra.counitAlgHom R U)
        (fun _ ha => RingHom.mem_ker.mp (degreeFiltration_one_le_ker_counit ℒ d hneg ha))
        ((F).projection 0 x) := by
  rw [completedCounit, AlgHom.comp_apply, Mei.AlgFiltration.projectionₐ_apply]

/-- On canonical elements the completed counit is the original counit. -/
@[simp]
theorem completedCounit_toCompletion (a : U) :
    completedCounit ℒ d hneg ((F).toCompletion a) = Coalgebra.counit (R := R) a := by
  rw [completedCounit_apply, Mei.AlgFiltration.projection_toCompletion]
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Bialgebra.counitAlgHom_apply] using
    AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp ((F).ideal 1)
      (Bialgebra.counitAlgHom R U)
      (fun _ ha => RingHom.mem_ker.mp (degreeFiltration_one_le_ker_counit ℒ d hneg ha))) a

/-- A primitive element satisfies the primitive equation in the completed tensor product. -/
def IsCompletedPrimitive (x : (F).completion) : Prop :=
  completedCoproduct ℒ d hneg x = tensor x 1 + tensor 1 x

/-- The defining equation for a completed primitive element. -/
theorem isCompletedPrimitive_iff (x : (F).completion) :
    IsCompletedPrimitive ℒ d hneg x ↔
      completedCoproduct ℒ d hneg x = tensor x 1 + tensor 1 x := Iff.rfl

/-- Completed primitive elements form an `R`-submodule. -/
noncomputable def completedPrimitiveSubmodule : Submodule R (F).completion :=
  LinearMap.ker ((completedCoproduct ℒ d hneg).toLinearMap -
    ((F).includeLeftCompletion (R := R) (F)).toLinearMap -
    ((F).includeRightCompletion (R := R) (F)).toLinearMap)

/-- Membership in the primitive submodule is the completed primitive equation. -/
@[simp]
theorem mem_completedPrimitiveSubmodule (x : (F).completion) :
    x ∈ completedPrimitiveSubmodule ℒ d hneg ↔ IsCompletedPrimitive ℒ d hneg x := by
  simp [completedPrimitiveSubmodule, isCompletedPrimitive_iff, sub_sub, sub_eq_zero]

/-- Zero is primitive in the completed enveloping algebra. -/
@[simp]
theorem isCompletedPrimitive_zero : IsCompletedPrimitive ℒ d hneg 0 :=
  (mem_completedPrimitiveSubmodule ℒ d hneg 0).mp (Submodule.zero_mem _)

/-- Every Lie generator maps to a primitive element of the degree completion. -/
@[simp]
theorem isCompletedPrimitive_toCompletion_ι (x : L) :
    IsCompletedPrimitive ℒ d hneg
      ((F).toCompletion (mkAlgHom R L (TensorAlgebra.ι R x))) := by
  rw [← ι_apply, isCompletedPrimitive_iff, completedCoproduct_toCompletion,
    TauCeti.UniversalEnvelopingAlgebra.comul_ι, map_add]
  simpa only [map_one] using congrArg₂ (· + ·)
    ((F).completedTensor_toCompletion (R := R) (F) (ι R x) 1).symm
    ((F).completedTensor_toCompletion (R := R) (F) 1 (ι R x)).symm

/-- A group-like element has counit one and tensor-square coproduct in the completion. -/
def IsCompletedGroupLike (x : (F).completion) : Prop :=
  completedCounit ℒ d hneg x = 1 ∧ completedCoproduct ℒ d hneg x = tensor x x

/-- The two equations characterizing a completed group-like element. -/
theorem isCompletedGroupLike_iff (x : (F).completion) :
    IsCompletedGroupLike ℒ d hneg x ↔
      completedCounit ℒ d hneg x = 1 ∧ completedCoproduct ℒ d hneg x = tensor x x := Iff.rfl

/-- The unit of the completed enveloping algebra is group-like. -/
@[simp]
theorem isCompletedGroupLike_one : IsCompletedGroupLike ℒ d hneg 1 := by
  simp [isCompletedGroupLike_iff]

/-- Products of completed group-like elements are group-like. -/
theorem IsCompletedGroupLike.mul {x y : (F).completion}
    (hx : IsCompletedGroupLike ℒ d hneg x) (hy : IsCompletedGroupLike ℒ d hneg y) :
    IsCompletedGroupLike ℒ d hneg (x * y) := by
  obtain ⟨hxc, hxd⟩ := hx
  obtain ⟨hyc, hyd⟩ := hy
  exact ⟨by rw [map_mul, hxc, hyc, one_mul], by
    rw [map_mul, hxd, hyd, Mei.AlgFiltration.completedTensor_mul]⟩

/-- The submonoid of group-like elements of the degree-completed enveloping algebra. -/
noncomputable def completedGroupLikeSubmonoid : Submonoid (F).completion where
  carrier := {x | IsCompletedGroupLike ℒ d hneg x}
  one_mem' := isCompletedGroupLike_one ℒ d hneg
  mul_mem' := fun hx hy => hx.mul ℒ d hneg hy

/-- Membership in the group-like submonoid is the pair of completed group-like equations. -/
@[simp]
theorem mem_completedGroupLikeSubmonoid (x : (F).completion) :
    x ∈ completedGroupLikeSubmonoid ℒ d hneg ↔ IsCompletedGroupLike ℒ d hneg x := Iff.rfl

end Mei.UniversalEnvelopingAlgebra
