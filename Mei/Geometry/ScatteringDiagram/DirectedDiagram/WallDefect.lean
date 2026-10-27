/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Trivialization
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.CellCrossing
public import Mei.Algebra.Lie.BCH.CentralExtension

/-!
# Central defects at adapted wall crossings

Finite chamber lifts and oriented wall labels determine kernel-valued crossing
errors. At each relative interior point of an adapted wall, a positive transverse
velocity determines two distinct incident full cells. Every sufficiently short
crossing has its endpoints in their ordinary interiors and realizes the wall's
crossing label. Lower-order consistency then places the gauged label in the
successive truncation kernel.

`exists_adapted_wall_defects` chooses normalized finite chamber lifts and supplies
these local coefficients simultaneously for every wall, coorientation, interior
point and positive transverse velocity. Each coefficient is characterized by its
logarithm formula, and reversing the crossing negates it. These are the local
coefficients from which a codimension-one central defect cochain is assembled;
no cochain boundary identity is asserted here.

The construction combines `exists_adapted_chamber_lifts`,
`FinitePolyhedralComplex.exists_transverse_wall_chambers`,
`eventually_exists_levelPathProduct_eq_wallCrossingLabel`, and `LieHom.logDefect`.
The central errors follow Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, proof of Theorem 2.6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Normalized finite chamber lifts supply a central coefficient at every actual
oriented wall crossing. The coefficient is computed by the same gauged label for
all sufficiently short crossings at the specified point and velocity. Reversing
the label and exchanging the incident lifts gives its negative.

The coefficients take values in the successive Lie kernel, without assuming
consistency at the higher order or a pre-existing lower-order crossing equation. -/
theorem exists_adapted_wall_defects (k : ℕ) (hk : D.LevelConsistent k)
    (b : WallComplement (fun j : D.active k => (D.wall j).support))
    (hb : b.val ∉ ((D.adaptedComplex (k + 1)).codimensionAtLeast 1).support) :
    ∃ (B : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
      (t : (D.adaptedComplex (k + 1)).cellsOfCodimension 0 →
        d.truncatedGroup ℒ (k + 1)),
      b.val ∈ interior (B : Set V) ∧ t B = 1 ∧
      (∀ (P : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
        (x : WallComplement (fun j : D.active k => (D.wall j).support)),
        x.val ∈ interior (P : Set V) →
        (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t P) =
          D.levelTransport k hk b x) ∧
      ∀ (Q : (D.adaptedComplex (k + 1)).walls) (ν : V →ₗ[ℝ] ℝ)
        (hν : ν.ker = (affineSpan ℝ (Q : Set V)).direction)
        (θ v : V), θ ∈ intrinsicInterior ℝ (Q : Set V) → 0 < ν v →
        ∃ (Pminus Pplus : (D.adaptedComplex (k + 1)).cellsOfCodimension 0)
          (c : (d.truncationMap ℒ (Nat.le_succ k)).ker),
          Pminus ≠ Pplus ∧ (Pminus : Set V) ∩ (Pplus : Set V) = (Q : Set V) ∧
          (c : d.truncatedLie ℒ (k + 1)) =
            BCHGroup.log ((t Pplus)⁻¹ * D.wallCrossingLabel Q ν hν * t Pminus) ∧
          BCHGroup.log ((t Pminus)⁻¹ * D.wallCrossingLabel Q (-ν)
            (by simpa using hν) * t Pplus) =
            -(c : d.truncatedLie ℒ (k + 1)) ∧
          ∀ᶠ a : ℝ in 𝓝[>] 0,
            ∃ (x y : WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
              (e : x ⟶ y),
              x.val = θ - a • v ∧ y.val = θ + a • v ∧
              x.val ∈ interior (Pminus : Set V) ∧ y.val ∈ interior (Pplus : Set V) ∧
              D.levelPathProduct (k + 1) e.toPath = D.wallCrossingLabel Q ν hν ∧
              BCHGroup.log ((t Pplus)⁻¹ * D.levelPathProduct (k + 1) e.toPath * t Pminus) =
                (c : d.truncatedLie ℒ (k + 1)) := by
  obtain ⟨B, t, hbB, htB, ht⟩ := D.exists_adapted_chamber_lifts (Nat.le_succ k) hk b hb
  refine ⟨B, t, hbB, htB, ht, ?_⟩
  intro Q ν hν θ v hθ hv
  obtain ⟨Pminus, Pplus, hne, hinter, hcross⟩ := D.exists_adapted_wall_crossing Q ν hν hθ hv
  -- Realize one short crossing to prove the lower-order equation; the same
  -- finite lifts and wall label then compute every short crossing.
  obtain ⟨a, x, y, e, _, _, hx, hy, he⟩ := hcross.exists
  have hker := D.adapted_chamber_lift_path_mem_ker (Nat.le_succ k) hk b t ht
    e.toPath Pminus Pplus hx hy
  rw [he] at hker
  have hX : (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
        (D.wallCrossingLabel Q ν hν) *
        (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t Pminus) =
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (t Pplus) := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, mul_assoc, inv_mul_eq_one] at hker
    exact hker.symm
  let c := (d.truncationMap ℒ (Nat.le_succ k)).logDefect
    (t Pminus) (t Pplus) (D.wallCrossingLabel Q ν hν) hX
  have hc : (c : d.truncatedLie ℒ (k + 1)) =
      BCHGroup.log ((t Pplus)⁻¹ * D.wallCrossingLabel Q ν hν * t Pminus) :=
    LieHom.coe_logDefect _ _ _ _ _
  refine ⟨Pminus, Pplus, c, hne, hinter, hc, ?_, ?_⟩
  · rw [D.wallCrossingLabel_neg Q ν hν, hc, ← BCHGroup.log_inv]
    congr 1
    group
  · filter_upwards [hcross] with a ha
    obtain ⟨x, y, e, hx, hy, hxm, hyp, he⟩ := ha
    exact ⟨x, y, e, hx, hy, hxm, hyp, he, by rw [he, ← hc]⟩

end Mei.DirectedDiagram
