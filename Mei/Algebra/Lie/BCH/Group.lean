/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Associativity
public import Mei.Algebra.Lie.RestrictScalars
public import Mathlib.Data.Finset.NoncommProd

/-!
# The algebraic BCH group

`Mei.BCHGroup L` equips a nilpotent rational Lie algebra with the group law obtained
by evaluating the universal BCH polynomial. Exponential and logarithm are mutually
inverse changes of carrier. No faithful representation or freeness is required.
Lie homomorphisms over any compatible commutative rational algebra induce group
homomorphisms via `LieHom.bchGroupMap`, by restriction of scalars to `ℚ`.
Lie equivalences induce group equivalences, and scalar restriction leaves the
induced homomorphisms unchanged.

The group law uses the bound-independent operation `Mei.bch`; its associativity
comes from finite enveloping quotients in `Mei.Algebra.Lie.BCH.Associativity`.
The power formulas express multiplication along a single Lie algebra direction, and
finite pairwise commuting families exponentiate their sum to Mathlib's unordered
product `Finset.noncommProd`.
-/

public section

noncomputable section

namespace Mei

/-- The carrier of the BCH group, with multiplication in exponential coordinates. -/
def BCHGroup (L : Type*) := L

namespace BCHGroup

variable {L : Type*}

/-- Exponential coordinates identify the Lie algebra with the BCH group as sets. -/
def exp : L ≃ BCHGroup L := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-- The logarithm of an element of the BCH group. -/
def log (g : BCHGroup L) : L := exp.symm g

@[simp]
theorem log_exp (x : L) : log (exp x) = x := exp.symm_apply_apply x

@[simp]
theorem exp_log (g : BCHGroup L) : exp (log g) = g := exp.apply_symm_apply g

/-- Logarithm detects equality of BCH group elements. -/
theorem log_injective : Function.Injective (log : BCHGroup L → L) :=
  exp.symm.injective

/-- A trivial Lie algebra has a trivial BCH group. -/
instance [Subsingleton L] : Subsingleton (BCHGroup L) :=
  exp.symm.subsingleton

instance [Zero L] : One (BCHGroup L) := ⟨exp 0⟩

instance [Neg L] : Inv (BCHGroup L) := ⟨fun g => exp (-log g)⟩

@[simp]
theorem exp_zero [Zero L] : exp (0 : L) = 1 := (rfl)

@[simp]
theorem log_one [Zero L] : log (1 : BCHGroup L) = 0 := log_exp _

@[simp]
theorem log_inv [Neg L] (g : BCHGroup L) : log g⁻¹ = -log g := log_exp _

/-- The inverse of an exponential is the exponential of the negative. -/
@[simp]
theorem exp_neg [Neg L] (x : L) : exp (-x) = (exp x)⁻¹ := by
  apply log_injective
  simp only [log_exp, log_inv]

variable [LieRing L] [LieAlgebra ℚ L] [LieRing.IsNilpotent L]

instance : Mul (BCHGroup L) := ⟨fun g h => exp (bch (log g) (log h))⟩

/-- The logarithm computes multiplication by BCH. -/
@[simp]
theorem log_mul (g h : BCHGroup L) : log (g * h) = bch (log g) (log h) :=
  log_exp _

/-- The universal BCH polynomial makes every nilpotent rational Lie algebra a group. -/
instance : Group (BCHGroup L) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc g h k := by apply log_injective; simp only [log_mul, bch_assoc]
  one_mul g := by apply log_injective; simp only [log_mul, log_one, bch_zero_left]
  mul_one g := by apply log_injective; simp only [log_mul, log_one, bch_zero_right]
  inv_mul_cancel g := by apply log_injective; simp only [log_mul, log_inv, bch_neg_left, log_one]

/-- Exponentiating BCH gives the ordered group product. -/
@[simp]
theorem exp_bch (x y : L) : exp (bch x y) = exp x * exp y := by
  apply log_injective
  simp only [log_exp, log_mul]

/-- Commuting Lie algebra elements have additive exponential coordinates. -/
theorem exp_add_of_lie_eq_zero (x y : L) (h : ⁅x, y⁆ = 0) :
    exp (x + y) = exp x * exp y := by
  rw [← bch_eq_add_of_lie_eq_zero x y h, exp_bch]

/-- Elements with zero Lie bracket exponentiate to commuting group elements. -/
theorem commute_exp_of_lie_eq_zero (x y : L) (h : ⁅x, y⁆ = 0) :
    Commute (exp x) (exp y) := by
  have h' : ⁅y, x⁆ = 0 := by simpa only [h, neg_zero] using (lie_skew y x).symm
  exact (exp_add_of_lie_eq_zero x y h).symm.trans
    ((congrArg exp (add_comm x y)).trans (exp_add_of_lie_eq_zero y x h'))

/-- Group elements whose logarithms have zero Lie bracket commute. -/
theorem commute_of_lie_log_eq_zero (g h : BCHGroup L) (hgh : ⁅log g, log h⁆ = 0) :
    Commute g h := by
  simpa only [exp_log] using commute_exp_of_lie_eq_zero _ _ hgh

/-- A finite family of pairwise commuting Lie algebra elements has additive exponential
coordinates: the exponential of the sum is the unordered product of the exponentials. -/
theorem exp_sum_of_lie_eq_zero {ι : Type*} (s : Finset ι) (x : ι → L)
    (h : (s : Set ι).Pairwise fun i j => ⁅x i, x j⁆ = 0) :
    exp (∑ i ∈ s, x i) = s.noncommProd (fun i => exp (x i))
      (h.imp fun _ _ hij => commute_exp_of_lie_eq_zero _ _ hij) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.noncommProd_empty, exp_zero]
  | cons a s ha ih =>
    have hs : (s : Set ι).Pairwise fun i j => ⁅x i, x j⁆ = 0 :=
      h.mono (Finset.coe_subset.mpr (Finset.subset_cons ha))
    have ha' : ⁅x a, ∑ i ∈ s, x i⁆ = 0 := by
      rw [lie_sum]
      exact Finset.sum_eq_zero fun j hj => h (Finset.mem_cons_self a s)
        (Finset.mem_cons_of_mem hj) (ne_of_mem_of_not_mem hj ha).symm
    rw [Finset.sum_cons, Finset.noncommProd_cons, exp_add_of_lie_eq_zero _ _ ha', ih hs]

/-- Natural powers of an exponential multiply its Lie algebra coordinate. -/
theorem exp_nsmul (x : L) (n : ℕ) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, exp_add_of_lie_eq_zero _ _ (by simp), ih, pow_succ]

/-- Integer powers of an exponential multiply its Lie algebra coordinate. -/
theorem exp_zsmul (x : L) (n : ℤ) : exp (n • x) = exp x ^ n := by
  cases n with
  | ofNat n => simpa using exp_nsmul x n
  | negSucc n =>
    simp only [negSucc_zsmul, exp_neg, exp_nsmul, zpow_negSucc]

/-- The logarithm of an integer power is the corresponding integer multiple. -/
@[simp]
theorem log_zpow (g : BCHGroup L) (n : ℤ) : log (g ^ n) = n • log g := by
  rw [← exp_log g, ← exp_zsmul, log_exp, log_exp]

end BCHGroup

end Mei

namespace LieHom

open Mei BCHGroup

variable {R L L' L'' : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra R L] [IsScalarTower ℚ R L]
  [LieRing.IsNilpotent L]
  [LieRing L'] [LieAlgebra ℚ L'] [LieAlgebra R L'] [IsScalarTower ℚ R L']
  [LieRing.IsNilpotent L']
  [LieRing L''] [LieAlgebra ℚ L''] [LieAlgebra R L''] [IsScalarTower ℚ R L'']
  [LieRing.IsNilpotent L'']

/-- A Lie homomorphism induces a homomorphism of algebraic BCH groups. -/
noncomputable def bchGroupMap (f : L →ₗ⁅R⁆ L') : BCHGroup L →* BCHGroup L' where
  toFun g := exp (f (log g))
  map_one' := by simp
  map_mul' g h := by
    simpa only [log_mul, exp_bch, restrictScalars_apply] using
      congrArg exp ((f.restrictScalars ℚ).map_bch (log g) (log h))

/-- The induced group homomorphism agrees with the Lie homomorphism in exponential
coordinates. -/
@[simp]
theorem bchGroupMap_exp (f : L →ₗ⁅R⁆ L') (x : L) :
    f.bchGroupMap (exp x) = exp (f x) := by simp [bchGroupMap]

@[simp]
theorem log_bchGroupMap (f : L →ₗ⁅R⁆ L') (g : BCHGroup L) :
    log (f.bchGroupMap g) = f (log g) := by simp [bchGroupMap]

/-- An injective Lie homomorphism induces an injective homomorphism of BCH groups. -/
theorem bchGroupMap_injective {f : L →ₗ⁅R⁆ L'} (hf : Function.Injective f) :
    Function.Injective f.bchGroupMap := fun g g' hgg' =>
  log_injective (hf (by simpa only [log_bchGroupMap] using congrArg log hgg'))

/-- A surjective Lie homomorphism induces a surjective homomorphism of BCH groups. -/
theorem bchGroupMap_surjective {f : L →ₗ⁅R⁆ L'} (hf : Function.Surjective f) :
    Function.Surjective f.bchGroupMap := fun g => by
  obtain ⟨x, hx⟩ := hf (log g)
  exact ⟨exp x, by rw [bchGroupMap_exp, hx, exp_log]⟩

/-- The identity Lie homomorphism induces the identity group homomorphism. -/
@[simp]
theorem bchGroupMap_id :
    (LieHom.id : L →ₗ⁅R⁆ L).bchGroupMap = MonoidHom.id (BCHGroup L) := by
  ext g
  simp [bchGroupMap]

/-- Composition of Lie homomorphisms induces composition of group homomorphisms. -/
@[simp]
theorem bchGroupMap_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    (g.comp f).bchGroupMap = g.bchGroupMap.comp f.bchGroupMap := by
  ext h
  simp [bchGroupMap]

end LieHom

namespace LieHom

variable {R S L L' : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [SMul R S]
  [LieRing L] [LieAlgebra R L] [LieAlgebra S L] [LieAlgebra ℚ L]
  [IsScalarTower R S L] [IsScalarTower ℚ R L] [IsScalarTower ℚ S L]
  [LieRing.IsNilpotent L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra S L'] [LieAlgebra ℚ L']
  [IsScalarTower R S L'] [IsScalarTower ℚ R L'] [IsScalarTower ℚ S L']
  [LieRing.IsNilpotent L']

/-- Restricting scalars leaves the induced BCH homomorphism unchanged. -/
@[simp]
theorem bchGroupMap_restrictScalars (f : L →ₗ⁅S⁆ L') :
    (f.restrictScalars R).bchGroupMap = f.bchGroupMap := by
  ext g
  apply Mei.BCHGroup.log_injective
  simp

end LieHom

namespace LieEquiv

open Mei BCHGroup

variable {R L L' : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing.IsNilpotent L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing.IsNilpotent L']

/-- A Lie equivalence induces an equivalence of BCH groups. -/
def bchGroupEquiv (e : L ≃ₗ⁅R⁆ L') : BCHGroup L ≃* BCHGroup L' where
  __ := e.toLieHom.bchGroupMap
  invFun g := exp (e.symm (log g))
  left_inv g := by apply log_injective; simp
  right_inv g := by apply log_injective; simp

/-- The induced equivalence has the group homomorphism induced by the Lie map. -/
@[simp]
theorem coe_bchGroupEquiv (e : L ≃ₗ⁅R⁆ L') :
    (e.bchGroupEquiv : BCHGroup L →* BCHGroup L') = e.toLieHom.bchGroupMap := (rfl)

/-- The induced equivalence acts by the Lie equivalence in exponential coordinates. -/
@[simp]
theorem bchGroupEquiv_exp (e : L ≃ₗ⁅R⁆ L') (x : L) :
    e.bchGroupEquiv (exp x) = exp (e x) := by
  exact e.toLieHom.bchGroupMap_exp x

/-- Logarithm intertwines the induced equivalence with the original Lie equivalence. -/
@[simp]
theorem log_bchGroupEquiv (e : L ≃ₗ⁅R⁆ L') (g : BCHGroup L) :
    log (e.bchGroupEquiv g) = e (log g) := by
  exact e.toLieHom.log_bchGroupMap g

/-- The inverse induced equivalence acts by the inverse Lie equivalence. -/
@[simp]
theorem bchGroupEquiv_symm_exp (e : L ≃ₗ⁅R⁆ L') (x : L') :
    e.bchGroupEquiv.symm (exp x) = exp (e.symm x) := by
  apply e.bchGroupEquiv.injective
  simp

end LieEquiv

end
