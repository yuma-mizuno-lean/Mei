/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Grading
public import Mei.Geometry.ScatteringDiagram.Skew.Projection
public import Mei.Geometry.ScatteringDiagram.WallSpace.Graph

/-!
# Principal wall spaces on the principal degree lattice

The principal graph grading places skew degree `n` at `r(n) = (p₁*(n), n)`.
We give it directed wall spaces with identity spatial map, and their projected
version with spatial map the first projection. The integral normals and wall
coefficients are those of the original unfrozen-indexed wall spaces. Degrees
outside the graph carry zero spaces, and radical degrees survive projection.

The graph BCH equivalence identifies the completed wall groups. The fixed-degree
principal Lie embedding preserves the graph wall spaces, allowing these labels
to act through the formal tropical vertex realization.

The principal realization follows Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2. We reuse
`principalWallSpaces`, `principalGrading` and `DirectedWallSpaces.graph`.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N R : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [CommRing R] [Algebra ℚ R] (D : SkewLatticeDatum N)
  (d : PositiveDegrees D.unfrozen)

local notation "M°" => Module.Dual ℤ D.sublattice
local notation "Lpr" => M° × D.unfrozen

/-- Principal wall spaces with degrees and spatial directions both in the
principal exponent lattice. Off-graph degrees have zero wall spaces. -/
def principalGraphWallSpaces :
    DirectedWallSpaces (AddMonoidHom.id Lpr) (D.principalGrading (R := R) d) :=
  (D.principalWallSpaces d).graph D.principalCharacter.toAddMonoidHom
    (AddMonoidHom.id Lpr) (fun n => by simp)

/-- The principal wall family is the graph reindexing of the original family;
it retains every on-graph space and vanishes elsewhere. -/
@[simp]
theorem principalGraphWallSpaces_wall (p : Lpr) (m : Lpr →+ ℤ) :
    (D.principalGraphWallSpaces (R := R) d).wall p m =
      graphGrading (fun n => (D.principalWallSpaces d).wall n m)
        D.principalCharacter.toAddMonoidHom p := by
  exact DirectedWallSpaces.graph_wall _ _ _ _ p m

/-- The fixed-degree principal realization preserves homogeneous wall spaces. -/
theorem principalGraphGradedLieHom_mem_wall {p : Lpr} {m : Lpr →+ ℤ}
    {x : SkewLieAlgebra.positiveLieAlgebra
      (D.coefficientForm R) (D.isAlt_coefficientForm R) d}
    (hx : x ∈ (D.principalGraphWallSpaces d).wall p m) :
    D.principalGraphGradedLieHom d x ∈
      (tropicalVertexWallSpaces (R := R) (D.principalPositiveDegrees d)
        (AddMonoidHom.id Lpr)).wall p m := by
  rcases p with ⟨a, n⟩
  by_cases ha : a = D.principalCharacter n
  · subst a
    have hx' : x ∈ (D.principalWallSpaces d).wall n m := by
      simpa only [D.principalGraphWallSpaces_wall, LinearMap.toAddMonoidHom_coe,
        graphGrading_apply] using hx
    have hmap : D.principalGraphGradedLieHom d x = D.principalGradedLieHom d x :=
      DFunLike.congr_fun (D.principalGraphGradedLieHom_toLieHom d) x
    rw [hmap]
    simpa only [D.principalEmbedding_apply] using
      ((D.mem_principalWallSpaces_iff d n m x).mp hx').2
  · have hz : (D.principalGraphWallSpaces (R := R) d).wall (a, n) m = ⊥ :=
      (D.principalGraphWallSpaces_wall d (a, n) m).trans
        (graphGrading_eq_bot _ _ (p := (a, n)) ha)
    rw [hz, Submodule.mem_bot] at hx
    simp [hx]

/-- Projected principal wall spaces on the full principal degree lattice.
The unfrozen coordinate is retained in degrees even when its spatial image is zero. -/
def projectedPrincipalGraphWallSpaces :
    DirectedWallSpaces (AddMonoidHom.fst M° D.unfrozen) (D.principalGrading (R := R) d) :=
  (D.projectedPrincipalWallSpaces d).graph D.principalCharacter.toAddMonoidHom
    (AddMonoidHom.fst M° D.unfrozen) (fun _ => rfl)

/-- The projected wall family retains precisely the original projected wall
coefficients on graph degrees, and is zero off the graph. -/
@[simp]
theorem projectedPrincipalGraphWallSpaces_wall (p : Lpr) (m : M° →+ ℤ) :
    (D.projectedPrincipalGraphWallSpaces (R := R) d).wall p m =
      graphGrading (fun n => (D.projectedPrincipalWallSpaces d).wall n m)
        D.principalCharacter.toAddMonoidHom p := by
  exact DirectedWallSpaces.graph_wall _ _ _ _ p m

/-- Graph reindexing and spatial projection select the same wall submodules,
including at off-graph indices and at radical degrees. -/
theorem projectedPrincipalGraphWallSpaces_wall_eq (p : Lpr) (m : M° →+ ℤ) :
    (D.projectedPrincipalGraphWallSpaces (R := R) d).wall p m =
      (D.principalGraphWallSpaces d).wall p (m.comp (AddMonoidHom.fst M° D.unfrozen)) := by
  simp only [D.projectedPrincipalGraphWallSpaces_wall, D.principalGraphWallSpaces_wall,
    D.projectedPrincipalWallSpaces_wall_eq]

variable [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) d

/-- The principal graph comparison identifies the completed wall groups at the
same cutoff orders, retaining their primitive normals. -/
@[simp]
theorem map_principalGraphWallGroup (w : SupportedRay d) (m : Lpr →+ ℤ) :
    ((D.principalWallSpaces (R := R) d).wallGroup w m).map
        (d.graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom).toMonoidHom =
      (D.principalGraphWallSpaces d).wallGroup (w.graph D.principalCharacter.toAddMonoidHom) m := by
  exact DirectedWallSpaces.map_graph_wallGroup _ _ _ _ w m

/-- Projected labels are also carried onto their graph-graded wall group.
Projection does not discard labels whose spatial direction is zero. -/
theorem map_projectedPrincipalGraphWallGroup (w : SupportedRay d) (m : M° →+ ℤ) :
    ((D.projectedPrincipalWallSpaces (R := R) d).wallGroup w m).map
        (d.graphBCHGroupEquiv ℒ D.principalCharacter.toAddMonoidHom).toMonoidHom =
      (D.projectedPrincipalGraphWallSpaces d).wallGroup
        (w.graph D.principalCharacter.toAddMonoidHom) m := by
  exact DirectedWallSpaces.map_graph_wallGroup _ _ _ _ w m

end Mei.SkewLatticeDatum
