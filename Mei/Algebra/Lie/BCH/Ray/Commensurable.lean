/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Basic
public import Mei.Algebra.PositiveDegrees.Ray.Commensurable

/-!
# Labels supported on multiples of commensurable degrees

For a nonzero allowed degree `n`, consider completed labels, elements of the completed BCH group,
whose logarithmic coefficients vanish off the positive multiples `(j + 1) • n`. Such a label lies
in the completed subgroup of the supported ray through `n`. When rays are abelian
(`IsAbelianRays`) and the degree lattice is free, two such labels for commensurable allowed degrees
`n` and `n'` commute, as elements of the completed group of their common supported ray, although
neither set of positive multiples need contain the other.

In particular, for `m ≠ 0` and nonzero `p`, `q` with `p • m` and `q • m` allowed, labels supported
on the positive multiples of `p • m` commute with those supported on the positive multiples of
`q • m`. The case `p = 2`, `q = 3` with `m` not allowed is
`commute_of_logComponent_eq_zero_two_nsmul_three_nsmul`.

As motivation, labels of walls indexed by nonprimitive degrees are of this form in the abelian-ray
description of scattering diagrams of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, §1.1 (arXiv:1411.1394v2), and Bridgeland, *Scattering diagrams, Hall algebras and
stability conditions*, §§2–3 (arXiv:1603.00416v4). This file does not formalize walls or the
merging of labels on coincident supports; it concerns only completed labels.

Membership in the ray group uses `TauCeti.PositiveDegrees.mem_completedRaySubgroup_iff_logComponent`
and commutation is `TauCeti.PositiveDegrees.commute_of_mem_completedRaySubgroup`.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading SupportedRay)

namespace TauCeti.PositiveDegrees

open Mei

variable {N R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A completed label whose logarithmic coefficients vanish off the positive multiples of an
actual degree `n` of a supported ray lies in the completed subgroup of that ray. -/
theorem mem_completedRaySubgroup_of_logComponent_eq_zero {w : SupportedRay d} {n : N}
    (hn : n ∈ w.rayDegrees) {g : d.completedBCHGroup ℒ}
    (hg : ∀ m, (∀ j : ℕ, (j + 1) • n ≠ m) → d.logComponent ℒ g m = 0) :
    g ∈ d.completedRaySubgroup ℒ w :=
  (d.mem_completedRaySubgroup_iff_logComponent ℒ w g).mpr fun m hm =>
    hg m fun j hj => hm (hj ▸ SupportedRay.succ_nsmul_mem_rayDegrees hn j)

/-- With abelian rays over a free degree lattice, let `n` be a nonzero allowed degree and `n'` an
allowed degree with `p • n' = q • n` for nonzero `p`, `q`. Completed labels supported on the
positive multiples of `n` commute with completed labels supported on the positive multiples
of `n'`. -/
theorem commute_of_logComponent_eq_zero_of_nsmul_eq_nsmul [Module.Free ℤ N]
    [IsAbelianRays d ℒ] {n n' : N} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hn' : n' ∈ d.monoid)
    {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (h : p • n' = q • n) {g g' : d.completedBCHGroup ℒ}
    (hg : ∀ m, (∀ j : ℕ, (j + 1) • n ≠ m) → d.logComponent ℒ g m = 0)
    (hg' : ∀ m, (∀ j : ℕ, (j + 1) • n' ≠ m) → d.logComponent ℒ g' m = 0) :
    Commute g g' := by
  obtain ⟨w, hw⟩ := d.exists_supportedRay hn hn0
  exact d.commute_of_mem_completedRaySubgroup ℒ
    (d.mem_completedRaySubgroup_of_logComponent_eq_zero ℒ hw hg)
    (d.mem_completedRaySubgroup_of_logComponent_eq_zero ℒ
      (SupportedRay.mem_rayDegrees_of_nsmul_eq_nsmul hw hn' hp hq h) hg')

/-- With abelian rays over a free degree lattice, for `m ≠ 0` and nonzero `p`, `q` with `p • m`
and `q • m` allowed, completed labels supported on the positive multiples of `p • m` commute with
completed labels supported on the positive multiples of `q • m`. -/
theorem commute_of_logComponent_eq_zero_nsmul_nsmul [Module.Free ℤ N] [IsAbelianRays d ℒ]
    {m : N} (hm0 : m ≠ 0) {p q : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hpm : p • m ∈ d.monoid)
    (hqm : q • m ∈ d.monoid) {g g' : d.completedBCHGroup ℒ}
    (hg : ∀ n, (∀ j : ℕ, (j + 1) • (p • m) ≠ n) → d.logComponent ℒ g n = 0)
    (hg' : ∀ n, (∀ j : ℕ, (j + 1) • (q • m) ≠ n) → d.logComponent ℒ g' n = 0) :
    Commute g g' :=
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  d.commute_of_logComponent_eq_zero_of_nsmul_eq_nsmul ℒ hpm (smul_ne_zero hp hm0) hqm hp hq
    (by rw [smul_smul, smul_smul, mul_comm]) hg hg'

/-- With abelian rays over a free degree lattice, if `2 • m` and `3 • m` are allowed degrees
but `m` is not, completed labels supported on the positive multiples of `2 • m` commute with
completed labels supported on the positive multiples of `3 • m`. -/
theorem commute_of_logComponent_eq_zero_two_nsmul_three_nsmul [Module.Free ℤ N]
    [IsAbelianRays d ℒ] {m : N} (h2 : 2 • m ∈ d.monoid) (h3 : 3 • m ∈ d.monoid)
    (hm : m ∉ d.monoid) {g g' : d.completedBCHGroup ℒ}
    (hg : ∀ n, (∀ j : ℕ, (j + 1) • (2 • m) ≠ n) → d.logComponent ℒ g n = 0)
    (hg' : ∀ n, (∀ j : ℕ, (j + 1) • (3 • m) ≠ n) → d.logComponent ℒ g' n = 0) :
    Commute g g' :=
  d.commute_of_logComponent_eq_zero_nsmul_nsmul ℒ (by rintro rfl; exact hm d.monoid.zero_mem)
    two_ne_zero three_ne_zero h2 h3 hg hg'

end TauCeti.PositiveDegrees
