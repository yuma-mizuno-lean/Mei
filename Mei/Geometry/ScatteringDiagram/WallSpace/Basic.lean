/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Basic

/-!
# Homogeneous directed wall spaces

Wall spaces are homogeneous submodules indexed by a degree and an integral normal.
Their bracket has the normal obtained by contracting each input normal with the
other input's geometric direction. Nontangent spaces and spaces with zero normal
vanish. These conditions force commutation for proportional normals and vanishing
of brackets whose total direction is annihilated by both normals.

The degree and tangent monoids are independent. No lattice basis, coefficient
characteristic or positivity assumption is needed for these algebraic identities.
-/

public section

namespace Mei

variable {Γ Λ R L : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The integral normal attached to a bracket of homogeneous wall elements. -/
def wallBracketNormal (ρ : Γ →+ Λ) (n n' : Γ) (m m' : Λ →+ ℤ) : Λ →+ ℤ :=
  m (ρ n') • m' - m' (ρ n) • m

/-- Evaluate the bracket normal on a tangent vector. -/
@[simp]
theorem wallBracketNormal_apply (ρ : Γ →+ Λ) (n n' : Γ) (m m' : Λ →+ ℤ) (v : Λ) :
    wallBracketNormal ρ n n' m m' v = m (ρ n') * m' v - m' (ρ n) * m v := (rfl)

/-- Homogeneous submodules with the normal and bracket laws of directed walls.
For a positive grading, containment in the homogeneous pieces automatically makes
all spaces outside the nonzero positive degrees vanish. -/
structure DirectedWallSpaces (ρ : Γ →+ Λ) (ℒ : Γ → Submodule R L) where
  /-- The submodule of wall elements of a given degree and normal. -/
  wall : Γ → (Λ →+ ℤ) → Submodule R L
  /-- Wall elements are homogeneous. -/
  wall_le_piece : ∀ n m, wall n m ≤ ℒ n
  /-- A zero normal carries no wall elements. -/
  zero_normal : ∀ n, wall n 0 = ⊥
  /-- A normal not annihilating the geometric degree carries no wall elements. -/
  nontangent : ∀ n m, m (ρ n) ≠ 0 → wall n m = ⊥
  /-- Nonzero integral rescaling leaves the wall submodule unchanged. -/
  rescale : ∀ n m (c : ℤ), c ≠ 0 → wall n (c • m) = wall n m
  /-- The bracket belongs to the space with summed degree and contracted normal. -/
  bracket_mem : ∀ {n n' m m' x y}, x ∈ wall n m → y ∈ wall n' m' →
    ⁅x, y⁆ ∈ wall (n + n') (wallBracketNormal ρ n n' m m')

namespace DirectedWallSpaces

variable {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)

/-- Directed wall spaces are determined by their wall submodules. -/
@[ext]
theorem ext {H K : DirectedWallSpaces ρ ℒ}
    (h : ∀ n m, H.wall n m = K.wall n m) : H = K := by
  have hw : H.wall = K.wall := funext fun n => funext fun m => h n m
  cases H
  cases K
  congr

/-- The normal of a nonzero wall element annihilates its geometric degree. -/
theorem normal_apply_eq_zero {n : Γ} {m : Λ →+ ℤ} {x : L}
    (hx : x ∈ H.wall n m) (hx0 : x ≠ 0) : m (ρ n) = 0 := by
  by_contra h
  rw [H.nontangent n m h, Submodule.mem_bot] at hx
  exact hx0 hx

/-- A bracket vanishes if both input normals annihilate its total geometric degree. -/
theorem lie_eq_zero_of_normal_total_eq_zero {n n' : Γ} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.wall n m) (hy : y ∈ H.wall n' m')
    (hm : m (ρ (n + n')) = 0) (hm' : m' (ρ (n + n')) = 0) : ⁅x, y⁆ = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hn := H.normal_apply_eq_zero hx hx0
  have hn' := H.normal_apply_eq_zero hy hy0
  have hcross : m (ρ n') = 0 := by simpa [hn] using hm
  have hcross' : m' (ρ n) = 0 := by simpa [hn'] using hm'
  have hnormal : wallBracketNormal ρ n n' m m' = 0 := by
    ext v
    simp [hcross, hcross']
  have h := H.bracket_mem hx hy
  rwa [hnormal, H.zero_normal, Submodule.mem_bot] at h

/-- Wall elements with the same normal commute, including nontangent degrees. -/
theorem lie_eq_zero_of_same_normal {n n' : Γ} {m : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.wall n m) (hy : y ∈ H.wall n' m) : ⁅x, y⁆ = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have htotal : m (ρ (n + n')) = 0 := by
    simp [H.normal_apply_eq_zero hx hx0, H.normal_apply_eq_zero hy hy0]
  exact H.lie_eq_zero_of_normal_total_eq_zero hx hy htotal htotal

/-- Rationally proportional integral normals give commuting wall elements.
Proportionality is expressed by a common nonzero integral rescaling. -/
theorem lie_eq_zero_of_proportional {n n' : Γ} {m m' : Λ →+ ℤ} {x y : L}
    (hx : x ∈ H.wall n m) (hy : y ∈ H.wall n' m')
    {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) (h : c • m = d • m') : ⁅x, y⁆ = 0 := by
  apply H.lie_eq_zero_of_same_normal (n := n) (n' := n') (m := c • m)
  · simpa only [H.rescale n m c hc] using hx
  · simpa only [h, H.rescale n' m' d hd] using hy

end DirectedWallSpaces

end Mei
