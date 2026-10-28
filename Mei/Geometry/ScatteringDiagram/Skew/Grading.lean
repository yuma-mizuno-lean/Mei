/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Embedding
public import Mei.Algebra.Lie.BCH.Graph

/-!
# Principal graph grading of the skew Lie algebra

The positive skew Lie algebra can be graded by the principal exponent lattice:
the piece at `r(n) = (p₁*(n), n)` is the original exponent-`n` piece, and every
piece off the graph is zero. The general graph-grading instances provide its
positive internal Lie grading and preserve every degree ideal. In particular,
`PositiveDegrees.graphBCHGroupEquiv` identifies its completed group with the
original completed skew group at the same finite orders.

The principal embedding becomes a fixed-degree graded Lie map after this
reindexing. Its completed map factors the original principal completed map
through that graph equivalence. This supplies the algebraic degree comparison
needed to put principal wall geometry and its labels on one exponent lattice.

The principal realization follows Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2. The construction uses
`principalGradedLieHom` and the general graph regrading and completed-map APIs.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N R : Type*} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  (D : SkewLatticeDatum N) (d : PositiveDegrees D.unfrozen)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) d
local notation "ℳ" => tropicalVertexGrading
  (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr)

/-- The positive skew Lie algebra graded on the principal exponent lattice,
retaining the original skew piece at each principal graph degree. -/
abbrev principalGrading : Lpr → Submodule R
    (SkewLieAlgebra.positiveLieAlgebra (D.coefficientForm R) (D.isAlt_coefficientForm R) d) :=
  graphGrading ℒ D.principalCharacter.toAddMonoidHom

/-- The principal embedding as a fixed-degree map on the graph-graded skew algebra. -/
def principalGraphGradedLieHom :
    GradedLieHom (PositiveDegreeMap.id (D.principalPositiveDegrees d))
      (D.principalGrading (R := R) d) ℳ where
  toLieHom := (D.principalGradedLieHom d).toLieHom
  map_mem := by
    rintro ⟨m, n⟩ x hx
    by_cases hm : m = D.principalCharacter n
    · subst m
      have hx' : x ∈ ℒ n := by
        simpa only [principalGrading, LinearMap.toAddMonoidHom_coe, graphGrading_apply] using hx
      simpa only [PositiveDegreeMap.id_apply, PositiveDegrees.graphMap_apply,
        LinearMap.toAddMonoidHom_coe] using
        (D.principalGradedLieHom d).map_mem hx'
    · have hbot := graphGrading_eq_bot ℒ D.principalCharacter.toAddMonoidHom
        (p := (m, n)) hm
      have hx0 : x = 0 := by
        simpa only [principalGrading, hbot, Submodule.mem_bot] using hx
      simp [hx0]

/-- The fixed-degree map has the same underlying principal Lie realization. -/
@[simp]
theorem principalGraphGradedLieHom_toLieHom :
    (D.principalGraphGradedLieHom (R := R) d).toLieHom =
      (D.principalGradedLieHom d).toLieHom := (rfl)

variable [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

/-- The original principal completed map factors through graph regrading, without
changing its cutoff order or its value on any completed skew label. -/
theorem completedMap_principalGradedLieHom :
    (D.principalGradedLieHom (R := R) d).completedMap =
      (D.principalGraphGradedLieHom d).completedMap.comp
        (d.graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom).toMonoidHom := by
  have h := GradedLieHom.completedMap_eq_of_toLieHom_eq
    ((D.principalGraphGradedLieHom d).comp
      (graphGradedLieHom ℒ D.principalCharacter.toAddMonoidHom d))
    (D.principalGradedLieHom d) (by simp)
  rw [GradedLieHom.completedMap_comp] at h
  apply MonoidHom.ext
  intro x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    PositiveDegrees.graphBCHGroupEquiv_apply] using DFunLike.congr_fun h.symm x

end Mei.SkewLatticeDatum
