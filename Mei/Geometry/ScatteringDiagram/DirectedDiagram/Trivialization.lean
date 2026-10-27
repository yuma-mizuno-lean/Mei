/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Adapted
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Chamber
public import Mei.Geometry.Convex.PolyhedralComplex.Chamber

/-!
# Finite chamber lifts on adapted complexes

The full-dimensional cells of an adapted ambient complex index finitely many
chambers. Their interiors miss the active supports and each lies in one connected
chamber of every lower-order active-wall complement. Lower-order consistency
therefore supplies a transport value on each such cell. These values admit lifts
to the higher BCH group, normalized to one on the base chamber.

The projection formula holds at every point of each cell interior, independently
of the representative used to select its lift. Gauging a higher-order path by the
lifts of its source and target cells puts its product in the truncation kernel;
at successive orders this is the central kernel in which crossing defects live.

This connects `DirectedDiagram.exists_chamberTransport_lifts` with the actual
finite cells of `DirectedDiagram.adaptedComplex`, using convex connectedness of
cell interiors. At successive orders, the existing
`PositiveDegrees.ker_truncationMap_succ_le_center` identifies the kernel as central.
No consistency at the lifted
order, local finiteness of the all-order wall union, or salient support is needed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- A point off the adapted skeleton lies on no active directed support. -/
theorem notMem_support_of_notMem_adapted_skeleton {k : ℕ} {x : V}
    (hx : x ∉ ((D.adaptedComplex k).codimensionAtLeast 1).support) (j : D.active k) :
    x ∉ (D.wall j).support := by
  intro hxj
  obtain ⟨Q, hQ, hxQ, -⟩ := D.exists_mem_adaptedComplex_walls_subset k j hxj
  exact hx (FinitePolyhedralComplex.mem_support.mpr ⟨Q,
    (D.adaptedComplex k).cellsOfCodimension_subset_codimensionAtLeast_cells 1 hQ, hxQ⟩)

/-- Every point in an adapted full cell interior is allowed at each lower cutoff. -/
theorem notMem_support_of_mem_interior_adapted {k l : ℕ} (hkl : k ≤ l)
    {P : Set V} (hP : P ∈ (D.adaptedComplex l).cellsOfCodimension 0)
    {x : V} (hx : x ∈ interior P) (j : D.active k) : x ∉ (D.wall j).support :=
  D.notMem_support_of_notMem_adapted_skeleton
    ((D.adaptedComplex l).interior_subset_compl_support_codimensionAtLeast_one hP hx)
    ⟨j.val, D.active_mono hkl j.property⟩

/-- An adapted full cell interior lies in a single actual chamber of every
lower-order active-wall complement. No consistency is required. -/
theorem levelChamber_eq_of_mem_interior_adapted {k l : ℕ} (hkl : k ≤ l)
    {P : Set V} (hP : P ∈ (D.adaptedComplex l).cellsOfCodimension 0)
    (x y : WallComplement (fun j : D.active k => (D.wall j).support))
    (hx : x.val ∈ interior P) (hy : y.val ∈ interior P) :
    D.levelChamber x = D.levelChamber y := by
  let U := {z : V // ∀ j : D.active k, z ∉ (D.wall j).support}
  let f : interior P → U := fun z =>
    ⟨z.val, D.notMem_support_of_mem_interior_adapted hkl hP z.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hPC := ((D.adaptedComplex l).mem_cellsOfCodimension 0 P).mp hP
  have hconn : IsPreconnected (range f) := by
    have hpre := (D.adaptedComplex l).isConvexPolyhedron hPC.1 |>.convex.interior.isPreconnected
    let : PreconnectedSpace (interior P) := isPreconnected_iff_preconnectedSpace.mp hpre
    simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
  apply (D.levelChamber_eq_iff x y).mpr
  exact hconn.subset_connectedComponent ⟨⟨y.val, hy⟩, rfl⟩ ⟨⟨x.val, hx⟩, rfl⟩

/-- Lower-order consistent transport has normalized lifts on the finite full
cells of the higher-order adapted complex. The projection formula holds for
every interior point, not just a selected representative. -/
theorem exists_adapted_chamber_lifts {k l : ℕ} (hkl : k ≤ l)
    (hk : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    (hb : b.val ∉ ((D.adaptedComplex l).codimensionAtLeast 1).support) :
    ∃ (B : (D.adaptedComplex l).cellsOfCodimension 0)
      (t : (D.adaptedComplex l).cellsOfCodimension 0 → d.truncatedGroup ℒ l),
      b.val ∈ interior (B : Set V) ∧ t B = 1 ∧
      ∀ (P : (D.adaptedComplex l).cellsOfCodimension 0)
        (x : WallComplement (fun j : D.active k => (D.wall j).support)),
        x.val ∈ interior (P : Set V) →
        (d.truncationMap ℒ hkl).bchGroupMap (t P) = D.levelTransport k hk b x := by
  classical
  obtain ⟨B, ⟨hB, hbB⟩, -⟩ :=
    (D.adaptedComplex l).exists_unique_mem_interior_cellsOfCodimension_zero
      (D.support_adaptedComplex l) hb
  obtain ⟨s, hsbase, hs⟩ := D.exists_chamberTransport_lifts hkl hk b
  have hpoint (P : (D.adaptedComplex l).cellsOfCodimension 0) :=
    (D.adaptedComplex l).interior_nonempty_of_mem_cellsOfCodimension_zero P.property
  let x (P : (D.adaptedComplex l).cellsOfCodimension 0) :
      WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨(hpoint P).choose,
      D.notMem_support_of_mem_interior_adapted hkl P.property (hpoint P).choose_spec⟩
  have hx (P : (D.adaptedComplex l).cellsOfCodimension 0) :
      (x P).val ∈ interior (P : Set V) := (hpoint P).choose_spec
  refine ⟨⟨B, hB⟩, fun P => s (D.levelChamber (x P)), hbB, ?_, ?_⟩
  · exact (congrArg s (D.levelChamber_eq_of_mem_interior_adapted hkl hB
      (x ⟨B, hB⟩) b (hx ⟨B, hB⟩) hbB)).trans hsbase
  · intro P y hy
    rw [hs, D.levelChamber_eq_of_mem_interior_adapted hkl P.property (x P) y (hx P) hy,
      D.chamberTransport_levelChamber]

/-- Gauging a higher-order path with finite chamber lifts gives an element of
the truncation kernel. The path may cross arbitrarily many adapted walls. -/
theorem adapted_chamber_lift_path_mem_ker {k l : ℕ} (hkl : k ≤ l)
    (hk : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    (t : (D.adaptedComplex l).cellsOfCodimension 0 → d.truncatedGroup ℒ l)
    (ht : ∀ (P : (D.adaptedComplex l).cellsOfCodimension 0)
      (x : WallComplement (fun j : D.active k => (D.wall j).support)),
      x.val ∈ interior (P : Set V) →
      (d.truncationMap ℒ hkl).bchGroupMap (t P) = D.levelTransport k hk b x)
    {x y : WallComplement (fun j : D.active l => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (P Q : (D.adaptedComplex l).cellsOfCodimension 0)
    (hx : x.val ∈ interior (P : Set V)) (hy : y.val ∈ interior (Q : Set V)) :
    (t Q)⁻¹ * D.levelPathProduct l p * t P ∈
      (d.truncationMap ℒ hkl).bchGroupMap.ker := by
  let r := WallComplement.restrictPrefunctor (fun j : D.active l => (D.wall j).support)
    (Set.inclusion (D.active_mono hkl))
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht P (r.obj x) hx, ht Q (r.obj y) hy,
    D.truncation_levelPathProduct hkl,
    ← D.levelTransport_eq_levelPathProduct hk]
  dsimp only [r]
  rw [mul_assoc, ← D.levelTransport_comp hk b, inv_mul_cancel]

end Mei.DirectedDiagram
