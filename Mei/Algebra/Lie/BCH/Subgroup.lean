/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Group
public import Mei.Algebra.Lie.Nilpotent
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# BCH subgroups and quotients

A Lie subalgebra of a nilpotent Lie algebra over a commutative rational algebra
exponentiates to a subgroup. This subgroup is characterized by membership of the
logarithm, and is naturally isomorphic to the subalgebra's own BCH group. Images
and inverse images agree with those of Lie subalgebras.

For a Lie ideal the subgroup is normal: it is the kernel of the group map induced
by the Lie quotient. The corresponding group quotient is the BCH group of the
Lie quotient. This uses Mathlib's first isomorphism theorem
`QuotientGroup.liftEquiv`, and the functoriality of `LieHom.bchGroupMap`.
-/

public section

noncomputable section

open Mei BCHGroup

variable {R L L' : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing.IsNilpotent L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing.IsNilpotent L']

namespace LieSubalgebra

/-- Lie subalgebras are closed under the BCH operation. -/
theorem bch_mem (K : LieSubalgebra R L) {x y : L} (hx : x ∈ K) (hy : y ∈ K) :
    bch x y ∈ K := by
  have h : ((bch (⟨x, hx⟩ : K) ⟨y, hy⟩ : K) : L) = bch x y := by
    simpa only [LieHom.restrictScalars_apply, LieSubalgebra.coe_incl] using
      (K.incl.restrictScalars ℚ).map_bch (⟨x, hx⟩ : K) ⟨y, hy⟩
  rw [← h]
  exact (bch (⟨x, hx⟩ : K) ⟨y, hy⟩).property

/-- The subgroup consisting of exponentials of elements of a Lie subalgebra. -/
def bchSubgroup (K : LieSubalgebra R L) : Subgroup (BCHGroup L) where
  carrier := {g | log g ∈ K}
  one_mem' := by simp
  mul_mem' hx hy := by simpa only [Set.mem_ofPred_eq, log_mul] using K.bch_mem hx hy
  inv_mem' hx := by
    simp only [Set.mem_ofPred_eq, log_inv]
    exact K.neg_mem hx

/-- Membership in the exponential subgroup is tested by logarithm. -/
@[simp]
theorem mem_bchSubgroup (K : LieSubalgebra R L) (g : BCHGroup L) :
    g ∈ K.bchSubgroup ↔ log g ∈ K := by simp [bchSubgroup]

/-- Inclusion of exponential subgroups is exactly inclusion of Lie subalgebras. -/
@[simp]
theorem bchSubgroup_le_bchSubgroup {K H : LieSubalgebra R L} :
    K.bchSubgroup ≤ H.bchSubgroup ↔ K ≤ H := by
  constructor
  · intro h x hx
    have hx' : exp x ∈ K.bchSubgroup := by simpa using hx
    have := h hx'
    simpa using this
  · intro h g hg
    exact h hg

/-- Exponential coordinates identify the intrinsic BCH group with its ambient subgroup. -/
def bchSubgroupEquiv (K : LieSubalgebra R L) : BCHGroup K ≃* K.bchSubgroup where
  toFun g := ⟨K.incl.bchGroupMap g, by simp⟩
  invFun g := exp ⟨log g.val, g.property⟩
  left_inv g := by apply log_injective; apply Subtype.ext; simp
  right_inv g := by apply Subtype.ext; apply log_injective; simp
  map_mul' g h := Subtype.ext (map_mul K.incl.bchGroupMap g h)

/-- The subgroup equivalence exponentiates the ambient logarithm. -/
@[simp]
theorem coe_bchSubgroupEquiv (K : LieSubalgebra R L) (g : BCHGroup K) :
    (K.bchSubgroupEquiv g : BCHGroup L) = exp ((log g : K) : L) := by
  apply log_injective
  simp [bchSubgroupEquiv]

/-- The inverse equivalence has the same logarithm, regarded as an element of the subalgebra. -/
@[simp]
theorem coe_log_bchSubgroupEquiv_symm (K : LieSubalgebra R L) (g : K.bchSubgroup) :
    ((log (K.bchSubgroupEquiv.symm g) : K) : L) = log (g : BCHGroup L) := by
  simp [bchSubgroupEquiv]

/-- Exponentiation commutes with inverse images of Lie subalgebras. -/
@[simp]
theorem bchSubgroup_comap (K : LieSubalgebra R L') (f : L →ₗ⁅R⁆ L') :
    (K.comap f).bchSubgroup = K.bchSubgroup.comap f.bchGroupMap := by
  ext g
  simp

/-- Exponentiation commutes with images of Lie subalgebras. -/
@[simp]
theorem bchSubgroup_map (K : LieSubalgebra R L) (f : L →ₗ⁅R⁆ L') :
    (K.map f).bchSubgroup = K.bchSubgroup.map f.bchGroupMap := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, he⟩ := (K.mem_map f (log g)).mp hg
    refine ⟨exp x, by simpa using hx, ?_⟩
    rw [f.bchGroupMap_exp, he, exp_log]
  · rintro ⟨h, hh, rfl⟩
    exact (K.mem_map f _).mpr ⟨log h, hh, by simp⟩

end LieSubalgebra

namespace LieHom

/-- The BCH group map has the exponential of the Lie kernel as its kernel. -/
@[simp]
theorem ker_bchGroupMap (f : L →ₗ⁅R⁆ L') :
    f.bchGroupMap.ker = f.ker.toLieSubalgebra.bchSubgroup := by
  ext g
  rw [MonoidHom.mem_ker, ← log_injective.eq_iff]
  simp

end LieHom

namespace LieIdeal

/-- Lie ideals exponentiate to normal subgroups. -/
instance bchSubgroup_normal (I : LieIdeal R L) : I.toLieSubalgebra.bchSubgroup.Normal := by
  have h : I.toLieSubalgebra.bchSubgroup = I.mkQ.bchGroupMap.ker := by simp
  rw [h]
  infer_instance

/-- Taking the quotient commutes with forming the BCH group. -/
def bchQuotientEquiv (I : LieIdeal R L) :
    BCHGroup L ⧸ I.toLieSubalgebra.bchSubgroup ≃* BCHGroup (L ⧸ I) :=
  QuotientGroup.liftEquiv _ (fun g => by
    obtain ⟨x, hx⟩ := I.surjective_mkQ (log g)
    exact ⟨exp x, by rw [I.mkQ.bchGroupMap_exp, hx, exp_log]⟩) (by simp)

/-- The quotient comparison is induced by the BCH map of the Lie quotient. -/
@[simp]
theorem bchQuotientEquiv_mk (I : LieIdeal R L) (g : BCHGroup L) :
    I.bchQuotientEquiv (QuotientGroup.mk g) = I.mkQ.bchGroupMap g := (rfl)

/-- The inverse quotient comparison sends an exponential class to the group class. -/
@[simp]
theorem bchQuotientEquiv_symm_exp_mk (I : LieIdeal R L) (x : L) :
    I.bchQuotientEquiv.symm (exp (Submodule.Quotient.mk x : L ⧸ I)) =
      QuotientGroup.mk (exp x) := by
  apply I.bchQuotientEquiv.symm_apply_eq.mpr
  simp

end LieIdeal

end
