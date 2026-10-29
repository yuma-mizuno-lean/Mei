/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Cylinder.Transport

/-!
# Equivalence through cylinder diagrams

Cylinder lifting preserves and reflects equivalence, at each finite order and
in the completion. Projection compares arbitrary common cylinder paths; lifting
base paths at one fixed extra coordinate proves reflection. In particular, adding
unrestricted spatial coordinates neither loses nor creates path-product information,
even for inconsistent diagrams and unrelated wall index types.

The argument uses `levelPathProduct_cylinder` and
`levelPathProduct_levelCylinderLift`. The geometric cylinder comparison is used in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

open Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ K R L V E ι κ : Type*}
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup K]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ Λ × K} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {j : K →+ E} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) ι}
  {F : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) κ}
  (h' : TauCeti.Toric.IsIntegralLattice j)

/-- Equivalent base diagrams have equivalent cylinders at the same cutoff. -/
theorem LevelEquivalent.cylinder {k : ℕ} (hDF : D.LevelEquivalent F k) :
    (D.cylinder h').LevelEquivalent (F.cylinder h') k := by
  rw [levelEquivalent_def] at hDF ⊢
  intro x y x' y' p q hpq
  rw [levelPathProduct_cylinder, levelPathProduct_cylinder]
  apply hDF
  have hv := congrArg (List.map Prod.fst) hpq
  simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    levelCylinderProjection_obj_val] using hv

/-- Cylinders agree at a cutoff exactly when their base diagrams do. -/
@[simp]
theorem cylinder_levelEquivalent_iff (k : ℕ) :
    (D.cylinder h').LevelEquivalent (F.cylinder h') k ↔ D.LevelEquivalent F k := by
  constructor
  · intro hDF
    rw [levelEquivalent_def] at hDF ⊢
    intro x y x' y' p q hpq
    have hv :
        ((D.levelCylinderLift h' k (0 : E)).mapPath p).vertices.map WallComplement.val =
          ((F.levelCylinderLift h' k (0 : E)).mapPath q).vertices.map WallComplement.val := by
      have hv := congrArg (List.map (fun v : V => (v, (0 : E)))) hpq
      simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        levelCylinderLift_obj_val] using hv
    simpa only [levelPathProduct_levelCylinderLift] using hDF _ _ hv
  · exact fun hDF => hDF.cylinder h'

/-- Equivalence at all orders is preserved by adjoining unrestricted coordinates. -/
theorem Equivalent.cylinder (hDF : D.Equivalent F) :
    (D.cylinder h').Equivalent (F.cylinder h') := by
  rw [equivalent_iff] at hDF ⊢
  exact fun k => (hDF k).cylinder h'

/-- Cylinder lifting preserves and reflects completed diagram equivalence. -/
@[simp]
theorem cylinder_equivalent_iff :
    (D.cylinder h').Equivalent (F.cylinder h') ↔ D.Equivalent F := by
  simp only [equivalent_iff, cylinder_levelEquivalent_iff]

end Mei.DirectedDiagram
