/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.WallSpace.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Projection

/-!
# Projected principal wall spaces

Project the geometric directions of the positive skew Lie algebra from the
principal lattice to the character lattice. The original unfrozen grading and
positive degree function are retained, so radical degrees remain present even
though their projected spatial direction is zero. The projected integral normal
pulls back to the principal normal. Eligible normals carry the entire homogeneous
skew piece, and the completed wall groups are exactly the principal cylinder wall
groups for the pulled back normals.

We reuse `SkewLatticeDatum.principalWallSpaces` and
`DirectedWallSpaces.project`. The principal and projected realizations follow
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N]
  (D : SkewLatticeDatum N)

local notation "M°" => Module.Dual ℤ D.sublattice

variable {R : Type*} [CommRing R] [Algebra ℚ R] (d : PositiveDegrees D.unfrozen)

local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) d

/-- Principal wall spaces with spatial directions projected to the character
lattice. The degree lattice and all its cutoff orders are unchanged. -/
def projectedPrincipalWallSpaces : DirectedWallSpaces D.principalCharacter.toAddMonoidHom ℒ := by
  let H := (D.principalWallSpaces (R := R) d).project (AddMonoidHom.fst M° D.unfrozen)
  have hρ : (AddMonoidHom.fst M° D.unfrozen).comp
      D.principalEmbedding.toAddMonoidHom = D.principalCharacter.toAddMonoidHom := by
    ext n
    simp
  exact { H with
    nontangent := by
      intro n m hm
      apply H.nontangent n m
      simpa only [hρ] using hm
    bracket_mem := by
      intro n n' m m' x y hx hy
      simpa only [hρ] using H.bracket_mem hx hy }

/-- Projection selects the original principal wall space for the cylinder normal. -/
theorem projectedPrincipalWallSpaces_wall_eq (n : D.unfrozen) (m : M° →+ ℤ) :
    (D.projectedPrincipalWallSpaces (R := R) d).wall n m =
      (D.principalWallSpaces d).wall n (m.comp (AddMonoidHom.fst M° D.unfrozen)) := by
  simp only [projectedPrincipalWallSpaces, DirectedWallSpaces.project_wall]

open Classical in
/-- The complete projected wall-space formula. A normal is eligible precisely
when it is nonzero and has the kernel of the normalized projected normal. -/
@[simp]
theorem projectedPrincipalWallSpaces_wall (n : D.unfrozen) (m : M° →+ ℤ) :
    (D.projectedPrincipalWallSpaces (R := R) d).wall n m =
      if m ≠ 0 ∧ m.ker = (D.projectedPrincipalNormal n).toAddMonoidHom.ker
      then ℒ n else ⊥ := by
  classical
  rw [D.projectedPrincipalWallSpaces_wall_eq, D.principalWallSpaces_wall,
    ← D.projectedPrincipalNormal_comp_fst]
  have hf : Function.Surjective (AddMonoidHom.fst M° D.unfrozen) :=
    fun φ => ⟨(φ, 0), rfl⟩
  have hzero : m.comp (AddMonoidHom.fst M° D.unfrozen) = 0 ↔ m = 0 := by
    simpa only [AddMonoidHom.zero_comp] using
      (AddMonoidHom.cancel_right (g₁ := m) (g₂ := 0) hf)
  have hker : (m.comp (AddMonoidHom.fst M° D.unfrozen)).ker =
        ((D.projectedPrincipalNormal n).toAddMonoidHom.comp
          (AddMonoidHom.fst M° D.unfrozen)).ker ↔
      m.ker = (D.projectedPrincipalNormal n).toAddMonoidHom.ker := by
    rw [← AddMonoidHom.comap_ker, ← AddMonoidHom.comap_ker]
    exact (AddSubgroup.comap_injective hf).eq_iff
  simp only [ne_eq, hzero, hker]

variable [DecidableEq D.unfrozen]

/-- Projected and principal cylinder wall labels form the same completed subgroup.
In particular this comparison does not discard labels with zero spatial direction. -/
@[simp↓]
theorem projectedPrincipalWallSpaces_wallGroup (w : SupportedRay d) (m : M° →+ ℤ) :
    (D.projectedPrincipalWallSpaces (R := R) d).wallGroup w m =
      (D.principalWallSpaces d).wallGroup w (m.comp (AddMonoidHom.fst M° D.unfrozen)) := by
  ext g
  simp only [DirectedWallSpaces.mem_wallGroup,
    DirectedWallSpaces.mem_truncatedRayLieSubalgebra, DirectedWallSpaces.raySubmodule_def,
    D.projectedPrincipalWallSpaces_wall_eq]

end Mei.SkewLatticeDatum
