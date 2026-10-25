/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Coproduct
public import Mei.RingTheory.FilteredAlgebra.AlgHom
public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Completion
public import Mathlib.Algebra.Group.Submonoid.Units

/-!
# Coproduct and primitive elements in completed enveloping algebras

The enveloping coproduct extends to the degree completion with values in the
completed tensor product for the total-degree filtration. Its finite projections
are the quotient coproducts. The counit factors through every finite quotient and
thus extends to the completion as an algebra homomorphism to the scalar ring.

Completed primitive elements form a Lie subalgebra, and the canonical Lie map
lands in it. Completed group-like elements, whose counit is one and whose coproduct
is their completed tensor square, form a submonoid, and group-like units form a
subgroup. For a strictly positive grading every group-like element is congruent to
one, hence a unit, so this subgroup accounts for the whole submonoid. These
constructions require
only a nonnegative integral degree on the Lie grading, over any commutative ring,
without a basis or finiteness assumption.
The tensor target is completed by total degree; no coalgebra structure on the
ordinary degree quotients is used.

The construction uses `Mei.AlgFiltration.mapCompletionₐ`, the completed tensor
inclusions, Mathlib's `Ideal.Quotient.liftₐ` and Tau Ceti's primitive-generator
formula `TauCeti.UniversalEnvelopingAlgebra.comul_ι`. The group-like subgroup uses
Mathlib's `MonoidHom.eqLocus` and `MonoidHom.ker` on units.
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
local notation "T" => Mei.AlgFiltration.tensorProduct R
  (degreeFiltration ℒ d hneg) (degreeFiltration ℒ d hneg)

/-- The coproduct on the degree completion, valued in the completed total-degree
tensor product. -/
noncomputable def completedCoproduct : (F).completion →ₐ[R] (T).completion :=
  (F).mapCompletionₐ (T) (Bialgebra.comulAlgHom R U) id monotone_id
    (fun k => by
      rw [Mei.AlgFiltration.tensorProduct_ideal]
      exact degreeFiltration_le_comap_comul ℒ d hneg (k + 1))

/-- Projection of the completed coproduct is the existing finite quotient coproduct. -/
@[simp]
theorem projection_completedCoproduct (k : ℕ) (x : (F).completion) :
    (T).projection k (completedCoproduct ℒ d hneg x) =
      Ideal.Quotient.factor (by rw [Mei.AlgFiltration.tensorProduct_ideal])
        (quotientCoproduct ℒ d hneg (k + 1) ((F).projection k x)) := by
  rw [completedCoproduct, Mei.AlgFiltration.projection_mapCompletionₐ]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((F).projection k x)
  simp only [id_eq, ← ha, quotientCoproduct_mk, Ideal.Quotient.factor_mk,
    Ideal.quotient_map_mkₐ, Bialgebra.comulAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- Completing an ordinary coproduct agrees with the completed coproduct. -/
@[simp]
theorem completedCoproduct_toCompletion (a : U) :
    completedCoproduct ℒ d hneg ((F).toCompletion a) =
      (T).toCompletion (Coalgebra.comul (R := R) a) := by
  exact (F).mapCompletionₐ_toCompletion _ _ id monotone_id _ a

/-- The completed coproduct preserves the induced degree filtrations. -/
theorem completedCoproduct_mem_completionIdeal (k : ℕ) {x : (F).completion}
    (hx : x ∈ (F).completionIdeal k) :
    completedCoproduct ℒ d hneg x ∈ (T).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    exact (F).mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

/-- The scalar-valued counit induced on an order-`k` quotient. -/
noncomputable def quotientCounit (k : ℕ) : U ⧸ (F).ideal (k + 1) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom R U) (by
    intro a ha
    simpa only [Bialgebra.counitAlgHom_apply] using
      (TauCeti.HopfIdeal.mem_augmentation R U).mp
        (degreeFiltration_le_augmentation ℒ d hneg (Nat.zero_lt_succ k) ha))

/-- The quotient counit evaluates representatives by the ordinary counit. -/
@[simp]
theorem quotientCounit_mk (k : ℕ) (a : U) :
    quotientCounit ℒ d hneg k (Ideal.Quotient.mk ((F).ideal (k + 1)) a) =
      Coalgebra.counit (R := R) a := by
  rw [quotientCounit]
  refine AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp ((F).ideal (k + 1)) (Bialgebra.counitAlgHom R U) ?_) a
  intro b hb
  exact (TauCeti.HopfIdeal.mem_augmentation R U).mp
    (degreeFiltration_le_augmentation ℒ d hneg (Nat.zero_lt_succ k) hb)

/-- Quotient counits commute with lowering the cutoff. -/
theorem quotientCounit_factor {k l : ℕ} (h : k ≤ l) (x : U ⧸ (F).ideal (l + 1)) :
    quotientCounit ℒ d hneg k
        (Ideal.Quotient.factor ((F).antitone (Nat.add_le_add_right h 1)) x) =
      quotientCounit ℒ d hneg l x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- The counit on the degree completion, evaluated already at order zero. -/
noncomputable def completedCounit : (F).completion →ₐ[R] R :=
  (quotientCounit ℒ d hneg 0).comp ((F).projectionₐ 0)

/-- Every finite-order component computes the same completed counit. -/
theorem completedCounit_eq_quotientCounit (k : ℕ) (x : (F).completion) :
    completedCounit ℒ d hneg x = quotientCounit ℒ d hneg k ((F).projection k x) := by
  rw [completedCounit, AlgHom.comp_apply, Mei.AlgFiltration.projectionₐ_apply,
    ← (F).factor_projection (Nat.zero_le k)]
  exact quotientCounit_factor ℒ d hneg (Nat.zero_le k) _

/-- The completed counit extends the ordinary enveloping counit. -/
@[simp]
theorem completedCounit_toCompletion (a : U) :
    completedCounit ℒ d hneg ((F).toCompletion a) = Coalgebra.counit (R := R) a := by
  rw [completedCounit_eq_quotientCounit ℒ d hneg 0,
    Mei.AlgFiltration.projection_toCompletion, quotientCounit_mk]

/-- Elements of the first completion ideal have zero counit. -/
theorem completedCounit_eq_zero_of_mem {x : (F).completion}
    (hx : x ∈ (F).completionIdeal 1) : completedCounit ℒ d hneg x = 0 := by
  rw [Mei.AlgFiltration.completionIdeal_succ, RingHom.mem_ker] at hx
  rw [completedCounit_eq_quotientCounit ℒ d hneg 0, hx, map_zero]

/-- For a strictly positive Lie grading, the first completion ideal is precisely
the kernel of the completed counit. -/
theorem mem_completionIdeal_one_iff_counit_eq_zero
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x : (F).completion) :
    x ∈ (F).completionIdeal 1 ↔ completedCounit ℒ d hneg x = 0 := by
  refine ⟨completedCounit_eq_zero_of_mem ℒ d hneg, fun hx => ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((F).projection 0 x)
  have hc : Coalgebra.counit (R := R) a = 0 := by
    rw [completedCounit_eq_quotientCounit ℒ d hneg 0, ← ha, quotientCounit_mk] at hx
    exact hx
  have hm : a ∈ (F).ideal 1 := augmentation_le_degreeFiltration_one ℒ d hpos
    ((TauCeti.HopfIdeal.mem_augmentation R _).mpr hc)
  simpa only [Mei.AlgFiltration.completionIdeal_succ, RingHom.mem_ker,
    ← ha, Ideal.Quotient.eq_zero_iff_mem] using hm

/-- A completed primitive has coproduct `x ⊗ 1 + 1 ⊗ x` in the completed tensor product. -/
def IsCompletedPrimitive (x : (F).completion) : Prop :=
  completedCoproduct ℒ d hneg x =
    (F).includeLeftCompletion (R := R) (F) x + (F).includeRightCompletion (R := R) (F) x

/-- The primitive equation expressed using the completed pure-tensor pairing. -/
theorem isCompletedPrimitive_iff (x : (F).completion) :
    IsCompletedPrimitive ℒ d hneg x ↔
      completedCoproduct ℒ d hneg x =
        (F).completedTensor (R := R) (F) x 1 + (F).completedTensor (R := R) (F) 1 x := by
  simp only [IsCompletedPrimitive, Mei.AlgFiltration.completedTensor_one_right,
    Mei.AlgFiltration.completedTensor_one_left]

/-- Zero is primitive in the completed enveloping algebra. -/
@[simp]
theorem isCompletedPrimitive_zero : IsCompletedPrimitive ℒ d hneg 0 := by
  simp [IsCompletedPrimitive]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Completed primitive elements are closed under scalars, addition and Lie brackets. -/
noncomputable def completedPrimitives : LieSubalgebra R (F).completion where
  carrier := {x | IsCompletedPrimitive ℒ d hneg x}
  zero_mem' := isCompletedPrimitive_zero ℒ d hneg
  add_mem' hx hy := by
    simp only [Set.mem_ofPred_eq, IsCompletedPrimitive] at hx hy ⊢
    simp only [map_add, hx, hy]
    abel
  smul_mem' r x hx := by
    simp only [Set.mem_ofPred_eq, IsCompletedPrimitive] at hx ⊢
    simp only [map_smul, hx, smul_add]
  lie_mem' {x y} hx hy := by
    have hxy := (F).commute_includeLeftCompletion_includeRightCompletion (R := R) (F) x y
    have hyx := (F).commute_includeLeftCompletion_includeRightCompletion (R := R) (F) y x
    simp only [Set.mem_ofPred_eq, IsCompletedPrimitive] at hx hy ⊢
    simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul, hx, hy]
    noncomm_ring [hxy.eq, hyx.eq]

/-- Membership in the primitive Lie subalgebra is the completed primitive equation. -/
@[simp]
theorem mem_completedPrimitives (x : (F).completion) :
    x ∈ completedPrimitives ℒ d hneg ↔ IsCompletedPrimitive ℒ d hneg x := Iff.rfl

/-- The negative of a completed primitive element is primitive. -/
theorem IsCompletedPrimitive.neg {x : (F).completion}
    (hx : IsCompletedPrimitive ℒ d hneg x) : IsCompletedPrimitive ℒ d hneg (-x) :=
  (completedPrimitives ℒ d hneg).neg_mem hx

/-- Every canonical Lie generator is primitive in the completion. -/
theorem isCompletedPrimitive_toCompletion_ι (x : L) :
    IsCompletedPrimitive ℒ d hneg ((F).toCompletion (ι R x)) := by
  rw [IsCompletedPrimitive, completedCoproduct_toCompletion,
    TauCeti.UniversalEnvelopingAlgebra.comul_ι, map_add,
    Mei.AlgFiltration.includeLeftCompletion_toCompletion,
    Mei.AlgFiltration.includeRightCompletion_toCompletion]

/-- The canonical Lie map into the primitive elements of the completed enveloping algebra. -/
noncomputable def toCompletedPrimitives : L →ₗ⁅R⁆ completedPrimitives ℒ d hneg :=
  { toLinearMap := (((F).toCompletionₐ (R := R)).toLinearMap.comp (ι R).toLinearMap).codRestrict
      (completedPrimitives ℒ d hneg).toSubmodule (by
        intro x
        simpa only [LieSubalgebra.mem_toSubmodule, mem_completedPrimitives,
          LinearMap.comp_apply, AlgHom.toLinearMap_apply, LieHom.coe_toLinearMap,
          Mei.AlgFiltration.toCompletionₐ_apply] using
          isCompletedPrimitive_toCompletion_ι ℒ d hneg x)
    map_lie' := fun {x y} => Subtype.ext
      ((((F).toCompletionₐ (R := R)).toLieHom.comp (ι R)).map_lie x y) }

/-- The canonical primitive-valued map completes the usual enveloping generator. -/
@[simp]
theorem coe_toCompletedPrimitives (x : L) :
    (toCompletedPrimitives ℒ d hneg x : (F).completion) = (F).toCompletion (ι R x) := by
  exact (F).toCompletionₐ_apply (ι R x)

/-- A group-like element has counit one and tensor-square coproduct in the completion. -/
def IsCompletedGroupLike (x : (F).completion) : Prop :=
  completedCounit ℒ d hneg x = 1 ∧
    completedCoproduct ℒ d hneg x = (F).completedTensor (R := R) (F) x x

/-- The two equations characterizing a completed group-like element. -/
theorem isCompletedGroupLike_iff (x : (F).completion) :
    IsCompletedGroupLike ℒ d hneg x ↔
      completedCounit ℒ d hneg x = 1 ∧
        completedCoproduct ℒ d hneg x = (F).completedTensor (R := R) (F) x x := Iff.rfl

/-- Every completed group-like element is congruent to one for a strictly positive grading. -/
theorem IsCompletedGroupLike.sub_one_mem
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) {u : (F).completion}
    (hu : IsCompletedGroupLike ℒ d hneg u) :
    u - 1 ∈ (F).completionIdeal 1 := by
  have hc := ((isCompletedGroupLike_iff ℒ d hneg u).mp hu).1
  rw [mem_completionIdeal_one_iff_counit_eq_zero ℒ d hneg hpos, map_sub, map_one,
    hc, sub_self]

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

/-- The subgroup of units whose counit is one and whose completed coproduct
is their tensor square. -/
noncomputable def completedGroupLikeSubgroup : Subgroup (F).completionˣ :=
  let diagonal : (F).completionˣ →* (T).completion :=
    { toFun := fun u => (F).completedTensor (R := R) (F) u u
      map_one' := by simp
      map_mul' := fun u v => (F).completedTensor_mul (F) u v u v }
  ((completedCoproduct ℒ d hneg).toMonoidHom.comp (Units.coeHom _)).eqLocus diagonal ⊓
    ((completedCounit ℒ d hneg).toMonoidHom.comp (Units.coeHom _)).ker

/-- Membership in the subgroup is precisely the group-like condition on the value. -/
@[simp]
theorem mem_completedGroupLikeSubgroup (u : (F).completionˣ) :
    u ∈ completedGroupLikeSubgroup ℒ d hneg ↔
      IsCompletedGroupLike ℒ d hneg (u : (F).completion) := by
  simp [completedGroupLikeSubgroup, MonoidHom.eqLocus, MonoidHom.mem_eqLocusM,
    isCompletedGroupLike_iff, and_comm]

/-- The inverse of a group-like unit is group-like. -/
theorem IsCompletedGroupLike.inv {u : (F).completionˣ}
    (hu : IsCompletedGroupLike ℒ d hneg (u : (F).completion)) :
    IsCompletedGroupLike ℒ d hneg (u⁻¹ : (F).completionˣ) := by
  exact (mem_completedGroupLikeSubgroup ℒ d hneg u⁻¹).mp
    ((completedGroupLikeSubgroup ℒ d hneg).inv_mem
      ((mem_completedGroupLikeSubgroup ℒ d hneg u).mpr hu))

/-- Every completed group-like element is invertible for a strictly positive grading. -/
theorem IsCompletedGroupLike.isUnit
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) {u : (F).completion}
    (hu : IsCompletedGroupLike ℒ d hneg u) : IsUnit u :=
  (F).isUnit_of_sub_one_mem (hu.sub_one_mem ℒ d hneg hpos)

/-- Forgetting that group-like units are units recovers all group-like elements. -/
theorem ofUnits_completedGroupLikeSubgroup
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    (completedGroupLikeSubgroup ℒ d hneg).ofUnits =
      completedGroupLikeSubmonoid ℒ d hneg := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_completedGroupLikeSubmonoid ℒ d hneg _).mpr
      ((mem_completedGroupLikeSubgroup ℒ d hneg v).mp hv)
  · intro hu
    have hg := (mem_completedGroupLikeSubmonoid ℒ d hneg u).mp hu
    have hunit := hg.isUnit ℒ d hneg hpos
    exact ⟨hunit.unit, (mem_completedGroupLikeSubgroup ℒ d hneg _).mpr
      (by simpa only [hunit.unit_spec] using hg), hunit.unit_spec⟩

/-- The group-like submonoid is multiplicatively equivalent to the subgroup of
group-like units. -/
noncomputable def completedGroupLikeEquivUnits
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    completedGroupLikeSubmonoid ℒ d hneg ≃*
      completedGroupLikeSubgroup ℒ d hneg :=
  (MulEquiv.submonoidCongr (ofUnits_completedGroupLikeSubgroup ℒ d hneg hpos).symm).trans
    (completedGroupLikeSubgroup ℒ d hneg).ofUnitsEquivType

/-- The group-like equivalence preserves the value in the completed algebra. -/
@[simp]
theorem coe_completedGroupLikeEquivUnits
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (u : completedGroupLikeSubmonoid ℒ d hneg) :
    ((completedGroupLikeEquivUnits ℒ d hneg hpos u).val : (F).completion) = u :=
  (Subgroup.unit_of_mem_ofUnits_spec_val_eq_of_mem _ _)

/-- The inverse equivalence forgets the unit structure. -/
@[simp]
theorem coe_completedGroupLikeEquivUnits_symm
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (u : completedGroupLikeSubgroup ℒ d hneg) :
    ((completedGroupLikeEquivUnits ℒ d hneg hpos).symm u : (F).completion) = u.val :=
  (rfl)

end Mei.UniversalEnvelopingAlgebra
