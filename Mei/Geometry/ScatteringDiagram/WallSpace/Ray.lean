/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Basic
public import Mei.Algebra.PositiveDegrees.Ray.Basic
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Wall spaces on supported rays

The sum of the homogeneous wall spaces on the actual allowed degrees of a
supported ray is an abelian Lie subalgebra. Distinct rays with proportional
normals commute as well. The primitive generator need not be an allowed degree.

For an internal grading, membership in this sum is detected by homogeneous
components: they belong to the prescribed wall spaces, and vanish away from the
ray. The construction uses Mathlib's submodule suprema and
`Submodule.iSup_induction`, with the supported degrees from `Mei.SupportedRay`.
-/

public section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  (H : DirectedWallSpaces ρ ℒ)

/-- The sum of wall spaces on the actual allowed degrees of a supported ray. -/
def raySubmodule (w : SupportedRay d) (m : Λ →+ ℤ) : Submodule R L :=
  ⨆ n : w.rayDegrees, H.wall n m

/-- The ray submodule is the sum over its allowed degrees. -/
theorem raySubmodule_def (w : SupportedRay d) (m : Λ →+ ℤ) :
    H.raySubmodule w m = ⨆ n : w.rayDegrees, H.wall n m := (rfl)

/-- A homogeneous wall space embeds into its supported-ray sum. -/
theorem wall_le_raySubmodule (w : SupportedRay d) (m : Λ →+ ℤ)
    {n : Γ} (hn : n ∈ w.rayDegrees) : H.wall n m ≤ H.raySubmodule w m :=
  le_iSup (fun n : w.rayDegrees => H.wall n m) ⟨n, hn⟩

/-- Rescaling the normal by a nonzero integer preserves the ray submodule. -/
@[simp]
theorem raySubmodule_rescale (w : SupportedRay d) (m : Λ →+ ℤ)
    (c : ℤ) (hc : c ≠ 0) : H.raySubmodule w (c • m) = H.raySubmodule w m := by
  simp only [raySubmodule_def, H.rescale _ _ c hc]

/-- A zero normal has zero ray submodule. -/
@[simp]
theorem raySubmodule_zero (w : SupportedRay d) : H.raySubmodule w 0 = ⊥ := by
  simp only [raySubmodule_def, H.zero_normal, iSup_bot]

/-- Sums of wall elements with rationally proportional normals commute, even
when their supported rays differ. -/
theorem lie_eq_zero_of_mem_raySubmodule {w v : SupportedRay d} {m m' : Λ →+ ℤ}
    {x y : L} (hx : x ∈ H.raySubmodule w m) (hy : y ∈ H.raySubmodule v m')
    {c e : ℤ} (hc : c ≠ 0) (he : e ≠ 0) (hm : c • m = e • m') : ⁅x, y⁆ = 0 := by
  rw [raySubmodule_def] at hx hy
  refine Submodule.iSup_induction _ (motive := fun x => ⁅x, y⁆ = 0) hx
    (fun n x hx => ?_) (by simp) (fun x z hx hz => by simp [hx, hz])
  exact Submodule.iSup_induction _ (motive := fun y => ⁅x, y⁆ = 0) hy
    (fun n' y hy => H.lie_eq_zero_of_proportional hx hy hc he hm)
    (by simp) (fun y z hy hz => by simp [hy, hz])

/-- The ray sum is an abelian Lie subalgebra of the original Lie algebra. -/
def rayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ) : LieSubalgebra R L where
  toSubmodule := H.raySubmodule w m
  lie_mem' hx hy := by
    rw [H.lie_eq_zero_of_mem_raySubmodule hx hy one_ne_zero one_ne_zero rfl]
    exact Submodule.zero_mem _

/-- Membership in the ray Lie subalgebra is membership in the ray sum. -/
@[simp]
theorem mem_rayLieSubalgebra (w : SupportedRay d) (m : Λ →+ ℤ) (x : L) :
    x ∈ H.rayLieSubalgebra w m ↔ x ∈ H.raySubmodule w m := Iff.rfl

/-- Every supported-ray wall Lie algebra is abelian. -/
instance rayLieSubalgebra_isLieAbelian (w : SupportedRay d) (m : Λ →+ ℤ) :
    IsLieAbelian (H.rayLieSubalgebra w m) where
  trivial x y := Subtype.ext
    (H.lie_eq_zero_of_mem_raySubmodule x.property y.property one_ne_zero one_ne_zero rfl)

variable [DecidableEq Γ] [DirectSum.Decomposition ℒ]

/-- Homogeneous components of a ray sum lie in their prescribed wall space. -/
theorem decompose_mem_wall_of_mem_raySubmodule {w : SupportedRay d} {m : Λ →+ ℤ}
    {x : L} (hx : x ∈ H.raySubmodule w m) (n : Γ) :
    (DirectSum.decompose ℒ x n : L) ∈ H.wall n m := by
  rw [raySubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => (DirectSum.decompose ℒ x n : L) ∈ H.wall n m) hx
    (fun i x hx => ?_) (by simp)
    (fun x y hx hy => by simpa using (H.wall n m).add_mem hx hy)
  · by_cases h : (i : Γ) = n
    · subst n
      rwa [DirectSum.decompose_of_mem_same ℒ (H.wall_le_piece _ _ hx)]
    · rw [DirectSum.decompose_of_mem_ne ℒ (H.wall_le_piece _ _ hx) h]
      exact Submodule.zero_mem _

/-- Components outside the actual ray degrees vanish. -/
theorem decompose_eq_zero_of_notMem_rayDegrees {w : SupportedRay d} {m : Λ →+ ℤ}
    {x : L} (hx : x ∈ H.raySubmodule w m) {n : Γ} (hn : n ∉ w.rayDegrees) :
    (DirectSum.decompose ℒ x n : L) = 0 := by
  rw [raySubmodule_def] at hx
  exact Submodule.iSup_induction _
    (motive := fun x => (DirectSum.decompose ℒ x n : L) = 0) hx
    (fun i x hx => DirectSum.decompose_of_mem_ne ℒ (H.wall_le_piece _ _ hx)
      (fun h => hn (h ▸ i.property)))
    (by simp) (fun x y hx hy => by simp [hx, hy])

/-- Membership in a ray sum is equivalent to the wall-space condition on every
component and vanishing of all components off the actual allowed ray degrees. -/
theorem mem_raySubmodule_iff (w : SupportedRay d) (m : Λ →+ ℤ) (x : L) :
    x ∈ H.raySubmodule w m ↔
      (∀ n, (DirectSum.decompose ℒ x n : L) ∈ H.wall n m) ∧
      ∀ n, n ∉ w.rayDegrees → (DirectSum.decompose ℒ x n : L) = 0 := by
  classical
  refine ⟨fun hx => ⟨H.decompose_mem_wall_of_mem_raySubmodule hx,
    fun _ hn => H.decompose_eq_zero_of_notMem_rayDegrees hx hn⟩, ?_⟩
  rintro ⟨hwall, hzero⟩
  rw [← DirectSum.sum_support_decompose ℒ x]
  apply Submodule.sum_mem
  intro n _
  by_cases hn : n ∈ w.rayDegrees
  · exact H.wall_le_raySubmodule w m hn (hwall n)
  · rw [hzero n hn]
    exact Submodule.zero_mem _

end Mei.DirectedWallSpaces
