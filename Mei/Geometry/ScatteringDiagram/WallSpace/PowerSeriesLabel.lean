/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Algebra.Lie.BCH.Ray.Series

/-!
# Power-series labels in wall groups

Let `n` be an actual degree of a supported ray `w`, and let `x j` lie in the wall space of
degree `(j+1)n` and normal `m`, for every `j`. Then every power-series label
`PositiveDegrees.rayExp` built from the family `x` is a completed wall label for `w` and `m`
(`DirectedWallSpaces.rayExp_mem_wallGroup`): its finite logarithms are the partial sums of
the ray series, which lie in the wall sum of the ray.
-/

public section

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L] [DecidableEq Γ]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  (H : DirectedWallSpaces ρ ℒ)

/-- If `n` is a degree of the supported ray `w` and every `x j` lies in the wall space of
degree `(j+1)n` and normal `m`, then every power-series label of `x` is a wall label for `w`
and `m`. -/
theorem rayExp_mem_wallGroup {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) {x : ℕ → L}
    (hx : ∀ j, x j ∈ ℒ ((j + 1) • n)) {w : SupportedRay d} (hw : n ∈ w.rayDegrees)
    {m : Λ →+ ℤ} (hxm : ∀ j, x j ∈ H.wall ((j + 1) • n) m) (f : PowerSeries R) :
    d.rayExp ℒ x hn hn0 hx f ∈ H.wallGroup w m := by
  rw [mem_wallGroup]
  intro k
  rw [d.log_projection_rayExp ℒ x hn hn0 hx k f, mem_truncatedRayLieSubalgebra]
  refine ⟨_, ?_, rfl⟩
  rw [PositiveDegrees.rayPartialSum_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (H.wall_le_raySubmodule w m (SupportedRay.succ_nsmul_mem_rayDegrees hw j) (hxm j))

end Mei.DirectedWallSpaces
