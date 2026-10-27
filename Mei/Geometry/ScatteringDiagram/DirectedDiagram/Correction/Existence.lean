/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Coboundary
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Boundary

/-!
# Outgoing corrections with a proved boundary identity

For a lower-order chamber trivialization, choose positive isolating meridians
and a finite family of outgoing homogeneous correction walls simultaneously.
The joint obstruction is a coboundary, hence closed, and the logarithmic
correction cochain has exactly this obstruction as its coboundary. Consequently
subtracting the correction cochain from the ambient crossing-defect cochain
produces a closed cochain. This is an equality in the quotient by orientation
and subdivision relations, so it survives passage to a common refinement.

The construction combines
`DirectedDiagram.exists_jointObstructionCochain_eq_coboundary` with
`DirectedDiagram.exists_joint_sweep_correction_family`. The meridians must be
chosen inside the local obstruction radii before their logarithms are swept;
closedness follows from square-zero rather than being assumed. Repeated and
coincident correction walls retain their joint-degree indices.

This is the cochain cancellation in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, proof of Theorem 2.6, and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix
C.3. Global path consistency of the corrected diagram is a separate assertion.
-/

public section

noncomputable section

open Set Module Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι} {k : ℕ}

/-- For every lower-order chamber trivialization, construct positive isolating
meridians and finite outgoing corrections whose logarithmic cochain bounds the
actual joint obstruction. Subtracting it from the ambient crossing-defect
cochain is closed. Initial walls are full hyperplanes and the remaining labels
are pure of lower birth order; neither closedness of the obstruction nor
consistency at the correction order is assumed. Centers and positive upper
bounds on the meridian radii may be prescribed independently at every joint. -/
theorem exists_joint_correction_boundary
    (σ : (D.adaptedComplex (k + 1)).walls → OrientedCell h 1)
    (hσ : ∀ Q, (σ Q).carrier = (Q : Set V))
    (cross : ∀ Q, D.AdaptedWallCrossing (l := k + 1) (σ Q) ((hσ Q).symm ▸ Q.property))
    (hk : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 → d.truncatedGroup ℒ (k + 1))
    (ht : ∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
      (x : WallComplement (fun j : D.active k => (D.wall j).support)),
      x.val ∈ interior (P : Set V) →
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) = D.levelTransport k hk b x)
    (τ : (D.adaptedComplex (k + 1)).joints → OrientedCell h 2)
    (hτ : ∀ J, (τ J).carrier = (J : Set V))
    (q : (D.adaptedComplex (k + 1)).joints → V)
    (hq : ∀ J : (D.adaptedComplex (k + 1)).joints,
      q J ∈ intrinsicInterior ℝ (J : Set V))
    (ε : (D.adaptedComplex (k + 1)).joints → ℝ) (hε : ∀ J, 0 < ε J)
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a})
    (hpure : ∀ j ∉ initial, ∃ n : Γ, d.degree n < k + 1 ∧
      ∃ a ∈ ℒ n, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ (s : (D.adaptedComplex (k + 1)).joints → Affine.Triangle ℝ V)
      (x : (D.adaptedComplex (k + 1)).joints →
        WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
      (γ : ∀ J, AdmissiblePLPath (x J) (x J)),
      (∀ J,
        0 < (τ J).orientation.someVector (fun j : Fin 2 => (s J).points j.succ - (s J).points 0) ∧
        (s J).centroid = q J ∧
        (γ J).vertices.map WallComplement.val =
          [(s J).points 0, (s J).points 1, (s J).points 2, (s J).points 0] ∧
        IsCompl (affineSpan ℝ (J : Set V)).direction (vectorSpan ℝ (range (s J).points)) ∧
        convexHull ℝ (range (s J).points) ⊆ Metric.ball (q J) (ε J) ∧
        convexHull ℝ (range (s J).points) ∩
          ((D.adaptedComplex (k + 1)).codimensionAtLeast 2).support = {q J} ∧
        Disjoint (convexHull ℝ (range (s J).points)) (intrinsicFrontier ℝ (J : Set V)) ∧
        ∀ Q ∈ (D.adaptedComplex (k + 1)).joints, Q ≠ (J : Set V) →
          Disjoint (convexHull ℝ (range (s J).points)) Q) ∧
      D.jointObstructionCochain τ x γ hτ hk =
        PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht) ∧
      letI := Fintype.ofFinite (D.adaptedComplex (k + 1)).joints
      ∃ (htrans : ∀ a : D.JointCorrectionIndex x γ,
          i (ρ a.2.val) ∉ (affineSpan ℝ (τ a.1).carrier).direction)
        (E : DirectedDiagram (d := d) h H (D.JointCorrectionIndex x γ)),
        (∀ a : D.JointCorrectionIndex x γ,
          (E.wall a).support = ((τ a.1).sweep (ρ a.2.val) (htrans a)).carrier ∧
          (∀ v : V, SignType.sign (h.realCharacter (E.wall a).normal v) =
            ((τ a.1).sweep (ρ a.2.val) (htrans a)).orientation.evalSign (fun _ : Fin 1 => v)) ∧
          a.2.val ∈ (E.wall a).ray.rayDegrees ∧
          (∃ c ∈ ℒ a.2.val, (E.wall a).label = d.expToCompletion ℒ (-c)) ∧
          (E.wall a).Outgoing ∧
          log (CompletedGroup.projection (k + 1) (E.wall a).label) =
            -(DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
              (log (D.levelPathProduct (k + 1) (γ a.1))) a.2.val : d.truncatedLie ℒ (k + 1)) ∧
          ∀ l : ℕ, a ∈ E.active l ↔ k + 1 ≤ l) ∧
        let B := PolyhedralCochain.ofFinsupp (R := R)
          (∑ a : D.JointCorrectionIndex x γ,
            Finsupp.single ((τ a.1).sweep (ρ a.2.val) (htrans a))
              (log (CompletedGroup.projection (k + 1) (E.wall a).label)))
        PolyhedralCochain.coboundary B =
          ∑ J, PolyhedralCochain.mk (τ J) (log (D.levelPathProduct (k + 1) (γ J))) ∧
        PolyhedralCochain.coboundary
          (PolyhedralCochain.map (d.truncationMap ℒ (Nat.le_succ k)).ker.subtype
            (crossingDefectCochain σ hσ cross hk b t ht) - B) = 0 := by
  classical
  -- First obtain the radii required by the local homogeneous obstruction theorem.
  obtain ⟨r, hr, hcorrection⟩ :=
    D.exists_joint_sweep_correction_family hk τ hτ q hq initial hfull hpure
  obtain ⟨s, x, γ, hs, hcomparison⟩ :=
    exists_jointObstructionCochain_eq_coboundary σ hσ cross hk b t ht τ hτ q hq
      (fun J => min (ε J) (r J)) (fun J => lt_min (hε J) (hr J))
  have hvertices (J : (D.adaptedComplex (k + 1)).joints) :
      ∀ z ∈ (γ J).vertices, z.val ∈ Metric.ball (q J) (r J) := by
    have hb (j : Fin 3) : (s J).points j ∈ Metric.ball (q J) (r J) :=
      Metric.ball_subset_ball (min_le_right _ _)
        ((hs J).2.2.2.2.1 (subset_convexHull ℝ _ (mem_range_self j)))
    have hv : ∀ v ∈ (γ J).vertices.map WallComplement.val, v ∈ Metric.ball (q J) (r J) := by
      rw [(hs J).2.2.1]
      simp only [List.forall_mem_cons]
      exact ⟨hb 0, hb 1, hb 2, hb 0, by simp⟩
    exact List.forall_mem_map.mp hv
  have hclosed : PolyhedralCochain.coboundary (D.jointObstructionCochain τ x γ hτ hk) = 0 := by
    rw [hcomparison, PolyhedralCochain.coboundary_coboundary]
  let := Fintype.ofFinite (D.adaptedComplex (k + 1)).joints
  obtain ⟨htrans, E, hE, hboundary⟩ := hcorrection x γ hvertices
  have hboundary' := hboundary hclosed
  refine ⟨s, x, γ, ?_, hcomparison, htrans, E, hE, ?_⟩
  · intro J
    obtain ⟨hp, hc, hv, ht, hb, hskel, hf, ho⟩ := hs J
    exact ⟨hp, hc, hv, ht, hb.trans (Metric.ball_subset_ball (min_le_left _ _)),
      hskel, hf, ho⟩
  · dsimp only
    rw [PolyhedralCochain.coboundary_ofFinsupp]
    refine ⟨hboundary', ?_⟩
    have hsource := (D.jointObstructionCochain_eq_iff τ x γ hτ hk
      (PolyhedralCochain.coboundary (crossingDefectCochain σ hσ cross hk b t ht))).mp hcomparison
    rw [map_sub, PolyhedralCochain.coboundary_ofFinsupp, hboundary',
      ← PolyhedralCochain.map_coboundary, ← hsource, sub_self]

end Mei.DirectedDiagram
