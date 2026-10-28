/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Module.Primitive
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Saturated

/-!
# Ray indices of sublattices

Let `H` be a subgroup of a free integer module `N`, for instance a finite-index sublattice.
For a nonzero `n : N`, write `n = d • w` with `d > 0` and `w` primitive. The *ray index*
`H.rayIndex n = addOrderOf (w : N ⧸ H) / d` is the rational number `κ` such that the positive
rational multiples of `n` lying in `H` are exactly the multiples by `j * κ`, for positive
integers `j`. On a primitive vector it is the order of its class modulo `H`, an integer, and it
scales inversely with the vector: `κ(t n) = κ(n) / t` for every positive rational `t` with
`t n ∈ N`. It is positive on nonzero vectors when `H` has finite index.

Real or rational scalings of lattice vectors are expressed without leaving `N`: a vector
`m = (b / a) n` with positive integers `a, b` is recorded by the equation `a • m = b • n`.

This is the normalization `κ` of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, §1, defined by `ℝ_{>0} n ∩ N° = ℕ_{>0} κ(n) n` for the finite-index sublattice `N°`.

## Main declarations

* `AddSubgroup.rayIndex`: the ray index of a vector with respect to a subgroup.
* `AddSubgroup.rayIndex_eq_of_eq_zsmul`: its value on any primitive decomposition.
* `AddSubgroup.mem_iff_exists_div_eq_mul_rayIndex_of_zsmul_eq_zsmul`: the positive rational
  multiples of `n` in `H` are those by the positive integer multiples of `H.rayIndex n`.
* `AddSubgroup.rayIndex_eq_of_zsmul_eq_zsmul`: the scaling law of the ray index.
-/

public section

namespace AddSubgroup

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] (H : AddSubgroup N)

open Classical in
/-- The ray index of `n` with respect to `H`: for `n = d • w` with `d > 0` and `w` primitive,
the order of `w` modulo `H` divided by `d`. The positive rational multiples of a nonzero `n`
lying in `H` are its multiples by `j * H.rayIndex n` with `j` a positive integer
(`AddSubgroup.mem_iff_exists_div_eq_mul_rayIndex_of_zsmul_eq_zsmul`).
By convention the ray index of `0` is `0`. -/
noncomputable def rayIndex (n : N) : ℚ :=
  if hn : n = 0 then 0 else
    (addOrderOf ((TauCeti.exists_eq_zsmul_isPrimitive hn).choose_spec.choose : N ⧸ H) : ℚ) /
      (TauCeti.exists_eq_zsmul_isPrimitive hn).choose

/-- The ray index of the zero vector is zero. -/
@[simp]
theorem rayIndex_zero : H.rayIndex 0 = 0 := by
  simp [rayIndex]

/-- The ray index computed from any decomposition `n = d • w` with `d > 0` and `w` primitive. -/
theorem rayIndex_eq_of_eq_zsmul {n w : N} {d : ℤ} (hd : 0 < d) (hw : TauCeti.IsPrimitive w)
    (hn : n = d • w) : H.rayIndex n = addOrderOf (w : N ⧸ H) / d := by
  have : HasUniqueDiv N := .of_isTorsionFree ℤ N
  have hn0 : n ≠ 0 := hn ▸ smul_ne_zero hd.ne' hw.ne_zero
  have hspec := (TauCeti.exists_eq_zsmul_isPrimitive hn0).choose_spec.choose_spec
  simp only [rayIndex, hn0, ↓reduceDIte]
  generalize (TauCeti.exists_eq_zsmul_isPrimitive hn0).choose_spec.choose = w' at hspec ⊢
  generalize (TauCeti.exists_eq_zsmul_isPrimitive hn0).choose = d' at hspec ⊢
  obtain ⟨hd', hw', hn'⟩ := hspec
  obtain rfl : w' = w := hw'.eq_of_pos_zsmul_eq hw hd' hd (hn'.symm.trans hn)
  obtain rfl : d' = d := hw'.zsmul_left_injective (hn'.symm.trans hn)
  rfl

/-- On a primitive vector the ray index is the order of its class modulo `H`; in particular
it is an integer. -/
theorem rayIndex_of_isPrimitive {w : N} (hw : TauCeti.IsPrimitive w) :
    H.rayIndex w = addOrderOf (w : N ⧸ H) := by
  simpa using H.rayIndex_eq_of_eq_zsmul one_pos hw (one_smul ℤ w).symm

/-- The ray index is nonnegative. -/
theorem rayIndex_nonneg (n : N) : 0 ≤ H.rayIndex n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  obtain ⟨d, w, hd, hw, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hn
  rw [H.rayIndex_eq_of_eq_zsmul hd hw rfl]
  positivity

/-- For a subgroup of finite index, the ray index of a nonzero vector is positive. -/
theorem rayIndex_pos [H.FiniteIndex] {n : N} (hn : n ≠ 0) : 0 < H.rayIndex n := by
  obtain ⟨d, w, hd, hw, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hn
  rw [H.rayIndex_eq_of_eq_zsmul hd hw rfl]
  have := addOrderOf_pos (w : N ⧸ H)
  positivity

/-- The ray index scales inversely with positive integer multiples. -/
theorem rayIndex_zsmul {d : ℤ} (hd : 0 < d) (n : N) :
    H.rayIndex (d • n) = H.rayIndex n / d := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  obtain ⟨e, w, he, hw, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hn
  rw [H.rayIndex_eq_of_eq_zsmul he hw rfl, smul_smul,
    H.rayIndex_eq_of_eq_zsmul (mul_pos hd he) hw rfl, Int.cast_mul, mul_comm (d : ℚ),
    div_div]

/-- The ray index scales inversely with positive rational multiples: if `m = (b / a) n`, that
is `a • m = b • n` with `a, b > 0`, then `κ(m) = κ(n) * a / b`. -/
theorem rayIndex_eq_of_zsmul_eq_zsmul {m n : N} {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : a • m = b • n) : H.rayIndex m = H.rayIndex n * a / b := by
  have hm := H.rayIndex_zsmul ha m
  rw [h, H.rayIndex_zsmul hb n] at hm
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [div_eq_div_iff hb' ha'] at hm
  rw [eq_div_iff hb']
  linarith

/-- The ray index is invariant under negation of the vector. -/
@[simp]
theorem rayIndex_neg (n : N) : H.rayIndex (-n) = H.rayIndex n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  obtain ⟨d, w, hd, hw, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hn
  rw [H.rayIndex_eq_of_eq_zsmul hd hw rfl,
    H.rayIndex_eq_of_eq_zsmul hd hw.neg (smul_neg d w).symm, QuotientAddGroup.mk_neg,
    addOrderOf_neg]

/-- The positive rational multiples of a nonzero vector `n` lying in `H` are exactly its
multiples by `j * H.rayIndex n` for positive integers `j`. Here the multiple `m = (b / a) n` is
recorded by `a • m = b • n` with `a, b > 0`. -/
theorem mem_iff_exists_div_eq_mul_rayIndex_of_zsmul_eq_zsmul {m n : N} (hn : n ≠ 0)
    {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : a • m = b • n) :
    m ∈ H ↔ ∃ j : ℕ, 0 < j ∧ (b / a : ℚ) = j * H.rayIndex n := by
  have : HasUniqueDiv N := .of_isTorsionFree ℤ N
  obtain ⟨d, w, hd, hw, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hn
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hw
  -- `m` is the multiple `e • w` with `a * e = b * d`.
  set e := f m
  have hae : a * e = b * d := by
    have := congrArg f h
    simpa [smul_smul, hf, e] using this
  have hm : m = e • w := by
    apply smul_right_injective N ha.ne'
    simp only [smul_smul, hae, h]
  have he : 0 < e := pos_of_mul_pos_right (hae ▸ mul_pos hb hd) ha.le
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hba : (b / a : ℚ) = e / d := by
    rw [div_eq_div_iff ha' hd']
    exact_mod_cast (by linarith [hae] : b * d = e * a)
  rw [H.rayIndex_eq_of_eq_zsmul hd hw rfl, hba, hm, ← QuotientAddGroup.eq_zero_iff,
    QuotientAddGroup.mk_zsmul, ← addOrderOf_dvd_iff_zsmul_eq_zero]
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos (addOrderOf (w : N ⧸ H)) with h0 | h0
      · simp [h0] at hc
        omega
      · exact pos_of_mul_pos_right (hc ▸ he) (by positivity)
    refine ⟨c.toNat, by omega, ?_⟩
    have hcn : ((c.toNat : ℕ) : ℚ) = c := by exact_mod_cast Int.toNat_of_nonneg hc0.le
    rw [hcn, hc]
    push_cast
    ring
  · rintro ⟨j, hj, hje⟩
    refine ⟨j, ?_⟩
    rw [mul_div_assoc', div_left_inj' hd'] at hje
    exact_mod_cast (hje.trans (mul_comm _ _))

/-- The multiple `κ(n) n` lies in `H`: some `m ∈ H` satisfies `den(κ) • m = num(κ) • n`, where
`κ = H.rayIndex n`. -/
theorem exists_mem_den_rayIndex_zsmul_eq_num_rayIndex_zsmul (n : N) :
    ∃ m ∈ H, ((H.rayIndex n).den : ℤ) • m = (H.rayIndex n).num • n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨0, H.zero_mem, by simp⟩
  obtain ⟨d, w, hd, hw, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hn
  refine ⟨addOrderOf (w : N ⧸ H) • w, ?_, ?_⟩
  · rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, addOrderOf_nsmul_eq_zero]
  · have hκ := H.rayIndex_eq_of_eq_zsmul hd hw rfl
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hcross : ((H.rayIndex (d • w)).den : ℤ) * addOrderOf (w : N ⧸ H) =
        (H.rayIndex (d • w)).num * d := by
      generalize H.rayIndex (d • w) = κ at hκ ⊢
      have hq : (κ.num : ℚ) / κ.den = addOrderOf (w : N ⧸ H) / d := (Rat.num_div_den κ).trans hκ
      have hden : (κ.den : ℚ) ≠ 0 := by positivity
      rw [div_eq_div_iff hden hd'] at hq
      have : (((κ.den : ℤ) * addOrderOf (w : N ⧸ H) : ℤ) : ℚ) = ((κ.num * d : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast this
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, smul_smul, hcross]

/-- The normalized vector `κ(n) n`, as an element of `H`. It is characterized by
`den_rayIndex_zsmul_rayVector`, including when the ray index is zero. -/
noncomputable def rayVector (n : N) : H :=
  ⟨(H.exists_mem_den_rayIndex_zsmul_eq_num_rayIndex_zsmul n).choose,
    (H.exists_mem_den_rayIndex_zsmul_eq_num_rayIndex_zsmul n).choose_spec.1⟩

/-- Clearing the denominator of the ray index recovers its normalized lattice vector. -/
theorem den_rayIndex_zsmul_rayVector (n : N) :
    ((H.rayIndex n).den : ℤ) • (H.rayVector n : N) = (H.rayIndex n).num • n :=
  (H.exists_mem_den_rayIndex_zsmul_eq_num_rayIndex_zsmul n).choose_spec.2

/-- The normalized vector of zero is zero. -/
@[simp]
theorem rayVector_zero : H.rayVector 0 = 0 := by
  apply Subtype.ext
  simpa using H.den_rayIndex_zsmul_rayVector 0

/-- Normalization commutes with negation. -/
@[simp]
theorem rayVector_neg (n : N) : H.rayVector (-n) = -H.rayVector n := by
  apply Subtype.ext
  apply smul_right_injective N (r := ((H.rayIndex n).den : ℤ))
    (by exact_mod_cast (H.rayIndex n).den_nz)
  simpa [H.den_rayIndex_zsmul_rayVector] using H.den_rayIndex_zsmul_rayVector (-n)

/-- The normalized vector depends only on the positive ray of its input. -/
@[simp]
theorem rayVector_zsmul {d : ℤ} (hd : 0 < d) (n : N) :
    H.rayVector (d • n) = H.rayVector n := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hκ := H.rayIndex_zsmul hd n
  rw [← Rat.num_div_den (H.rayIndex (d • n)), ← Rat.num_div_den (H.rayIndex n),
    div_div, div_eq_div_iff (by positivity) (mul_ne_zero (by positivity) hd')] at hκ
  have hcross : ((H.rayIndex n).den : ℤ) * (H.rayIndex (d • n)).num * d =
      ((H.rayIndex (d • n)).den : ℤ) * (H.rayIndex n).num := by
    have hc : (H.rayIndex (d • n)).num * (((H.rayIndex n).den : ℤ) * d) =
        (H.rayIndex n).num * ((H.rayIndex (d • n)).den : ℤ) := by
      exact_mod_cast hκ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  apply Subtype.ext
  apply smul_right_injective N (r :=
    ((H.rayIndex (d • n)).den : ℤ) * (H.rayIndex n).den)
    (mul_ne_zero (by exact_mod_cast (H.rayIndex (d • n)).den_nz)
      (by exact_mod_cast (H.rayIndex n).den_nz))
  calc
    _ = ((H.rayIndex n).den : ℤ) •
        (((H.rayIndex (d • n)).den : ℤ) • (H.rayVector (d • n) : N)) := by
      rw [smul_smul, mul_comm]
    _ = (((H.rayIndex n).den : ℤ) * (H.rayIndex (d • n)).num * d) • n := by
      rw [H.den_rayIndex_zsmul_rayVector, smul_smul, smul_smul]
    _ = (((H.rayIndex (d • n)).den : ℤ) * (H.rayIndex n).num) • n := by rw [hcross]
    _ = _ := by simp only [mul_smul, H.den_rayIndex_zsmul_rayVector]

/-- Normalization preserves membership in any saturated subgroup. -/
theorem rayVector_mem_of_mem {K : AddSubgroup N} (hK : K.toAddSubmonoid.NSMulSaturated)
    {n : N} (hn : n ∈ K) : (H.rayVector n : N) ∈ K := by
  have hm : ((H.rayIndex n).den : ℤ) • (H.rayVector n : N) ∈ K := by
    rw [H.den_rayIndex_zsmul_rayVector]
    exact K.zsmul_mem hn _
  exact ((AddSubgroup.saturated_iff_zsmul.mp hK) _ _ hm).resolve_left (by
    exact_mod_cast (H.rayIndex n).den_nz)

end AddSubgroup
