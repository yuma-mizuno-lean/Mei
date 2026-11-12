/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Ray.Basic
public import Mei.Algebra.PositiveDegrees.Basic

/-!
# Actual degrees on a supported ray

The allowed positive multiples on a supported primitive ray form a semigroup.
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

namespace TauCeti.SupportedRay

variable {N : Type*} [AddCommGroup N] {d : PositiveDegrees N}

/-- Positive natural multiples of an actual ray degree remain on that ray. -/
theorem succ_nsmul_mem_rayDegrees {w : SupportedRay d} {n : N} (hn : n ∈ w.rayDegrees)
    (j : ℕ) : (j + 1) • n ∈ w.rayDegrees := by
  obtain ⟨hn, a, ha, rfl⟩ := mem_rayDegrees.mp hn
  refine mem_rayDegrees.mpr ⟨d.monoid.nsmul_mem hn _, (j + 1) * a, ?_, ?_⟩
  · positivity
  · rw [mul_smul, ← Nat.cast_succ, natCast_zsmul]

/-- The additive semigroup of actual allowed positive degrees on a supported ray. -/
def degreeSemigroup (w : SupportedRay d) : AddSubsemigroup N where
  carrier := w.rayDegrees
  add_mem' := add_mem_rayDegrees

/-- Semigroup membership is membership in the set of actual ray degrees. -/
@[simp]
theorem mem_degreeSemigroup (w : SupportedRay d) (n : N) :
    n ∈ w.degreeSemigroup ↔ n ∈ w.rayDegrees := Iff.rfl

/-- All ray degrees are allowed degrees. -/
theorem rayDegrees_subset (w : SupportedRay d) : w.rayDegrees ⊆ d.monoid :=
  fun _ hn => (mem_rayDegrees.mp hn).1

end TauCeti.SupportedRay
