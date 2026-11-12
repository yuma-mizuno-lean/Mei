/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Ray.Basic

/-!
# Commensurable degrees on supported rays

Two allowed degrees `n`, `n'` are commensurable when `p • n' = q • n` for some nonzero natural
numbers `p`, `q`. In a free integer module, commensurable nonzero allowed degrees lie on a common
supported ray: an allowed degree commensurable with an actual degree of a supported ray is an
actual degree of that ray. In particular, for `m ≠ 0` and nonzero `p`, `q` with `p • m` and
`q • m` allowed, both lie on one supported ray, and `m` is a positive multiple of its generator.

For instance, if `2 • m` and `3 • m` are allowed while `m` is not, then `2 • m` and `3 • m` lie on
a common supported ray of which `m` is not an actual degree.

As background, supported rays index the walls of the abelian-ray description of scattering
diagrams in Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2). This file concerns only degrees and rays.
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

namespace TauCeti


variable {N : Type*} [AddCommGroup N] {d : PositiveDegrees N}

namespace SupportedRay

/-- Nonzero natural multiples of an actual ray degree remain on that ray. -/
theorem nsmul_mem_rayDegrees {w : SupportedRay d} {n : N} (hn : n ∈ w.rayDegrees) {p : ℕ}
    (hp : p ≠ 0) : p • n ∈ w.rayDegrees := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  exact succ_nsmul_mem_rayDegrees hn j

/-- In a free integer module, an allowed degree commensurable with an actual degree of a supported
ray is an actual degree of that ray. -/
theorem mem_rayDegrees_of_nsmul_eq_nsmul [Module.Free ℤ N] {w : SupportedRay d} {n n' : N}
    (hn : n ∈ w.rayDegrees) (hn' : n' ∈ d.monoid) {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p • n' = q • n) : n' ∈ w.rayDegrees := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    exact ne_zero_of_mem_rayDegrees (nsmul_mem_rayDegrees hn hq) (by rw [← h, smul_zero])
  obtain ⟨v, hv⟩ := d.exists_supportedRay hn' hn'0
  obtain rfl : v = w :=
    eq_of_mem_rayDegrees (nsmul_mem_rayDegrees hv hp) (h ▸ nsmul_mem_rayDegrees hn hq)
  exact hv

/-- In a free integer module, if a nonzero natural multiple of `m` is an actual degree of a
supported ray, then `m` is a positive integer multiple of the generator of that ray. -/
theorem exists_pos_zsmul_generator_of_nsmul_mem_rayDegrees [Module.Free ℤ N]
    {w : SupportedRay d} {m : N} {p : ℕ} (hp : p ≠ 0) (h : p • m ∈ w.rayDegrees) :
    ∃ a : ℤ, 0 < a ∧ m = a • w.generator := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact ne_zero_of_mem_rayDegrees h (smul_zero p)
  obtain ⟨c, v, hc, hv, rfl⟩ := TauCeti.exists_eq_zsmul_isPrimitive hm0
  obtain ⟨-, b, hb, hpb⟩ := mem_rayDegrees.mp h
  have hpc : (0 : ℤ) < p * c := mul_pos (by omega) hc
  refine ⟨c, hc, ?_⟩
  rw [hv.eq_of_pos_zsmul_eq w.isPrimitive hpc hb (by rw [mul_smul, natCast_zsmul, hpb])]

/-- A vector that is not an allowed degree is not an actual degree of any supported ray. -/
theorem notMem_rayDegrees_of_notMem (w : SupportedRay d) {m : N} (hm : m ∉ d.monoid) :
    m ∉ w.rayDegrees :=
  fun h => hm (w.rayDegrees_subset h)

end SupportedRay

namespace PositiveDegrees

variable (d)

/-- In a free integer module, for `m ≠ 0` and nonzero `p`, `q`, if `p • m` and `q • m` are
allowed degrees then both are actual degrees of one supported ray. -/
theorem exists_supportedRay_nsmul_mem_rayDegrees [Module.Free ℤ N] {m : N} (hm0 : m ≠ 0)
    {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hpm : p • m ∈ d.monoid) (hqm : q • m ∈ d.monoid) :
    ∃ w : SupportedRay d, p • m ∈ w.rayDegrees ∧ q • m ∈ w.rayDegrees := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  obtain ⟨w, hw⟩ := d.exists_supportedRay hpm (smul_ne_zero hp hm0)
  exact ⟨w, hw, SupportedRay.mem_rayDegrees_of_nsmul_eq_nsmul hw hqm hp hq
    (by rw [smul_smul, smul_smul, mul_comm])⟩

/-- In a free integer module, if `2 • m` and `3 • m` are allowed degrees but `m` is not, then
`2 • m` and `3 • m` are actual degrees of one supported ray, `m` is a positive multiple of its
generator, and `m` is not an actual degree of this ray. -/
theorem exists_supportedRay_two_nsmul_three_nsmul [Module.Free ℤ N] {m : N}
    (h2 : 2 • m ∈ d.monoid) (h3 : 3 • m ∈ d.monoid) (hm : m ∉ d.monoid) :
    ∃ w : SupportedRay d, 2 • m ∈ w.rayDegrees ∧ 3 • m ∈ w.rayDegrees ∧
      m ∉ w.rayDegrees ∧ ∃ a : ℤ, 0 < a ∧ m = a • w.generator := by
  obtain ⟨w, hw2, hw3⟩ := d.exists_supportedRay_nsmul_mem_rayDegrees
    (by rintro rfl; exact hm d.monoid.zero_mem) two_ne_zero three_ne_zero h2 h3
  exact ⟨w, hw2, hw3, w.notMem_rayDegrees_of_notMem hm,
    SupportedRay.exists_pos_zsmul_generator_of_nsmul_mem_rayDegrees two_ne_zero hw2⟩

end PositiveDegrees

end TauCeti
