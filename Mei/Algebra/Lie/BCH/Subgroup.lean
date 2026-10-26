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

Modulo any submodule containing all brackets of the subalgebra, BCH is addition, so
the logarithm of a product in the subgroup is the sum of the logarithms of its
factors. This passes to the abelian quotient of the subalgebra, where BCH is
addition by `Mei.bch_eq_add`.

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

/-- Modulo any submodule containing all brackets of a Lie subalgebra, BCH on that subalgebra
is addition. -/
theorem bch_sub_add_mem (K : LieSubalgebra R L) (J : Submodule R L)
    (hJ : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ J) {x y : L} (hx : x ∈ K) (hy : y ∈ K) :
    bch x y - (x + y) ∈ J := by
  let I : LieIdeal ℚ K :=
    { carrier := {z | (z : L) ∈ J}
      add_mem' := J.add_mem
      zero_mem' := J.zero_mem
      smul_mem' := fun q _ hz => J.smul_of_tower_mem q hz
      lie_mem := fun {a z} _ => hJ a a.property z z.property }
  have : IsLieAbelian (K ⧸ I) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := I.surjective_mkQ a
    obtain ⟨b, rfl⟩ := I.surjective_mkQ b
    rw [← LieHom.map_lie, LieIdeal.mkQ_eq_zero]
    exact hJ a a.property b b.property
  let x' : K := ⟨x, hx⟩
  let y' : K := ⟨y, hy⟩
  have hbch : ((bch x' y' : K) : L) = bch x y := by
    simpa only [LieHom.restrictScalars_apply, LieSubalgebra.coe_incl] using
      (K.incl.restrictScalars ℚ).map_bch x' y'
  have hI : bch x' y' - (x' + y') ∈ I := by
    rw [← LieIdeal.mkQ_eq_zero, map_sub, LieHom.map_bch, bch_eq_add, map_add, sub_self]
  -- Membership in `I` is membership of the underlying element of `L` in `J`.
  have hJ' : ((bch x' y' - (x' + y') : K) : L) ∈ J := hI
  rwa [AddSubgroupClass.coe_sub, AddMemClass.coe_add, hbch] at hJ'

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

/-- Modulo any submodule containing all brackets of a Lie subalgebra, the logarithm of a
product in its exponential subgroup is the sum of the logarithms of the factors. -/
theorem log_list_prod_sub_sum_mem (K : LieSubalgebra R L) (J : Submodule R L)
    (hJ : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ J) {l : List (BCHGroup L)}
    (hl : ∀ g ∈ l, g ∈ K.bchSubgroup) : log l.prod - (l.map log).sum ∈ J := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have hg : log g ∈ K := hl g List.mem_cons_self
    have hl' : ∀ g ∈ l, g ∈ K.bchSubgroup := fun g hg => hl g (List.mem_cons_of_mem _ hg)
    have hprod : log l.prod ∈ K := K.bchSubgroup.list_prod_mem hl'
    have h := J.add_mem (K.bch_sub_add_mem J hJ hg hprod) (ih hl')
    rw [List.prod_cons, List.map_cons, List.sum_cons, log_mul]
    convert h using 1
    abel

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
