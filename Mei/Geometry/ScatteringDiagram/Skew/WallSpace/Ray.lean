/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.WallSpace.Basic
public import Mei.Algebra.Lie.Skew.Ray
public import Mei.Geometry.ScatteringDiagram.WallSpace.Group

/-!
# Principal labels on a supported ray

At the normalized principal normal of a supported primitive generator, the
principal wall spaces exhaust the skew ray algebra. Consequently every scalar
ray exponential is a legal principal wall label, including at radical degrees.
This connects `principalWallSpaces_wall_eq_piece` with
`SkewLieAlgebra.rayExp_mem_completedRaySubgroup`.

The normalization follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2.
-/

public noncomputable section

namespace Mei.SkewLatticeDatum

variable {N R : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [CommRing R] [Algebra ℚ R] (D : SkewLatticeDatum N)
  (d : PositiveDegrees D.unfrozen) [DecidableEq D.unfrozen]

local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) d

/-- At its normalized principal normal, the whole supported skew ray group
is available as a wall group. No saturation of the positive monoid is required. -/
theorem principalWallSpaces_wallGroup_eq_completedRaySubgroup (w : SupportedRay d) :
    (D.principalWallSpaces (R := R) d).wallGroup w
        (D.principalNormal w.generator).toAddMonoidHom = d.completedRaySubgroup ℒ w := by
  apply DirectedWallSpaces.wallGroup_eq_completedRaySubgroup
  rw [DirectedWallSpaces.raySubmodule_def, Mei.rayLieSubalgebra_toSubmodule]
  congr 1
  funext n
  obtain ⟨a, ha, he⟩ := (SupportedRay.mem_rayDegrees.mp n.property).2
  apply D.principalWallSpaces_wall_eq_piece
  rw [he, D.principalNormal_zsmul ha]

/-- Any scalar series on an allowed degree defines a principal wall label on
its supported ray. The series may have infinitely many nonzero coefficients. -/
theorem rayExp_mem_principalWallGroup {w : SupportedRay d} {n : D.unfrozen}
    (hn : n ∈ w.rayDegrees) (f : PowerSeries R) :
    SkewLieAlgebra.rayExp (D.coefficientForm R) (D.isAlt_coefficientForm R)
        (w.rayDegrees_subset hn) (SupportedRay.ne_zero_of_mem_rayDegrees hn) f ∈
      (D.principalWallSpaces d).wallGroup w
        (D.principalNormal w.generator).toAddMonoidHom := by
  rw [D.principalWallSpaces_wallGroup_eq_completedRaySubgroup]
  exact SkewLieAlgebra.rayExp_mem_completedRaySubgroup _ _ _ _ hn f

end Mei.SkewLatticeDatum
