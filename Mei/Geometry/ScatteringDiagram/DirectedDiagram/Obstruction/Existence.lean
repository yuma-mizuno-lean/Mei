/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Coboundary
public import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus

/-!
# Existence of chamber trivializations and their joint obstructions

Every directed diagram consistent at order `k` admits finite chamber data at
order `k + 1`: oriented adapted walls, actual positive crossings between incident
chambers, a basepoint in a full cell interior, and normalized lifts of lower-order
transport. Choose oriented joints and arbitrarily small positive isolating
meridians simultaneously. Their kernel-valued obstruction cochain is the
coboundary of the crossing-defect cochain associated to these same choices.

The construction uses `exists_adapted_chamber_lifts`,
`AdaptedWallCrossing`'s geometric existence theorem, and
`exists_jointObstructionCochain_eq_coboundary`. Orientations are supplied by
`IsRationalNormalPolyhedron.exists_orientedCell`, extracted from the normal-form
argument for polyhedral cochains. The meridians meet only original active
supports containing their joint, including repeated and coincident supports.
No initial-wall presentation or consistency at the higher order is required.

These are the chamber trivializations and central obstructions in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Module Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Lower-order consistency supplies normalized finite chamber lifts, oriented
wall crossings, and positive isolating joint meridians whose obstruction is the
boundary of the crossing-defect cochain. Each meridian lies within its prescribed
positive radius about its centroid in the joint interior and meets only active
supports containing that joint. All geometric and transport choices are outputs. -/
theorem exists_chamber_trivialization {k : ℕ} (hk : D.LevelConsistent k)
    (ε : (D.adaptedComplex (k + 1)).joints → ℝ) (hε : ∀ J, 0 < ε J) :
    ∃ (σ : (D.adaptedComplex (k + 1)).walls → OrientedCell h 1)
      (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
      (cross : ∀ Q, D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
      (b : WallComplement (fun j : D.active k => (D.wall j).support))
      (B : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
      (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
      (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
        (x : WallComplement (fun j : D.active k => (D.wall j).support)),
        x.val ∈ interior (P : Set V) →
        (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)
      (τ : (D.adaptedComplex (k + 1)).joints → OrientedCell h 2)
      (hτ : ∀ J, (τ J).carrier = (J : Set V))
      (s : (D.adaptedComplex (k + 1)).joints → Affine.Triangle ℝ V)
      (x : (D.adaptedComplex (k + 1)).joints →
        WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
      (γ : ∀ J, AdmissiblePLPath (x J) (x J)),
      b.val ∈ interior (B : Set V) ∧ t B = 1 ∧
      (∀ J,
        0 < (τ J).orientation.someVector
          (fun j : Fin 2 => (s J).points j.succ - (s J).points 0) ∧
        (s J).centroid ∈ intrinsicInterior ℝ (J : Set V) ∧
        (γ J).vertices.map WallComplement.val =
          [(s J).points 0, (s J).points 1, (s J).points 2, (s J).points 0] ∧
        IsCompl (affineSpan ℝ (J : Set V)).direction (vectorSpan ℝ (range (s J).points)) ∧
        convexHull ℝ (range (s J).points) ⊆ Metric.ball (s J).centroid (ε J) ∧
        convexHull ℝ (range (s J).points) ∩
          ((D.adaptedComplex (k + 1)).codimensionAtLeast 2).support = {(s J).centroid} ∧
        Disjoint (convexHull ℝ (range (s J).points)) (intrinsicFrontier ℝ (J : Set V)) ∧
        (∀ Q ∈ (D.adaptedComplex (k + 1)).joints, Q ≠ (J : Set V) →
          Disjoint (convexHull ℝ (range (s J).points)) Q) ∧
        ∀ j : D.active (k + 1),
          (convexHull ℝ (range (s J).points) ∩ (D.wall j).support).Nonempty →
            (J : Set V) ⊆ (D.wall j).support) ∧
      D.jointObstructionCochain τ x γ hτ hk =
        PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht) := by
  classical
  let := h.finiteDimensional
  let C := D.adaptedComplex (k + 1)
  have horient (m : ℕ) (Q : C.cellsOfCodimension m) :
      ∃ υ : OrientedCell h m, υ.carrier = (Q : Set V) := by
    obtain ⟨hQC, hdim⟩ := (C.mem_cellsOfCodimension m Q).mp Q.property
    exact (C.rational Q hQC).exists_orientedCell (C.nonempty Q hQC) hdim
  choose σ hσ using horient 1
  choose τ hτ using horient 2
  let cross (Q : C.walls) :
      D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property) :=
    Classical.choice inferInstance
  -- An ambient full cell has a nonempty ordinary interior, even in dimension zero.
  obtain ⟨P, hP, -⟩ := C.exists_mem_cellsOfCodimension_zero (D.support_adaptedComplex _) 0
  obtain ⟨z, hz⟩ := C.interior_nonempty_of_mem_cellsOfCodimension_zero hP
  have hzoff := C.interior_subset_compl_support_codimensionAtLeast_one hP hz
  let b : WallComplement (fun j : D.active k => (D.wall j).support) :=
    ⟨z, D.notMem_support_of_mem_interior_adapted (Nat.le_succ k) hP hz⟩
  obtain ⟨B, t, hbB, htB, ht⟩ :=
    D.exists_adapted_chamber_lifts (Nat.le_succ k) hk b hzoff
  have hcenter (J : C.joints) : (intrinsicInterior ℝ (J : Set V)).Nonempty :=
    (C.nonempty J ((C.mem_cellsOfCodimension 2 J).mp J.property).1).intrinsicInterior
      (C.isConvexPolyhedron ((C.mem_cellsOfCodimension 2 J).mp J.property).1).convex
  choose q hq using hcenter
  -- These additional radii ensure isolation for every original indexed support.
  choose r hr hisolate hfrontier hother hincident using fun J : C.joints =>
    C.exists_isolating_ball J.property (hq J)
  obtain ⟨s, x, γ, hs, he⟩ := exists_jointObstructionCochain_eq_coboundary
    σ hσ cross hk b t ht τ hτ q hq (fun J => min (ε J) (r J))
      (fun J => lt_min (hε J) (hr J))
  refine ⟨σ, hσ, cross, b, B, t, ht, τ, hτ, s, x, γ, hbB, htB, ?_, he⟩
  intro J
  obtain ⟨hp, hc, hv, hcompl, hball, hskel, hf, ho⟩ := hs J
  have hsmall : convexHull ℝ (range (s J).points) ⊆ Metric.ball (q J) (r J) :=
    hball.trans (Metric.ball_subset_ball (min_le_right _ _))
  refine ⟨hp, hc.symm ▸ hq J, hv, hcompl, ?_, hc.symm ▸ hskel, hf, ho, ?_⟩
  · rw [hc]
    exact hball.trans (Metric.ball_subset_ball (min_le_left _ _))
  · rintro j ⟨y, hy, hyj⟩
    obtain ⟨Q, hQ, hyQ, hsub⟩ := D.exists_mem_adaptedComplex_walls_subset (k + 1) j hyj
    exact (hincident J Q (C.mem_cells_of_mem_walls hQ) ⟨y, hsmall hy, hyQ⟩).trans hsub

end Mei.DirectedDiagram
