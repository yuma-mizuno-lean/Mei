/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.LinearAlgebra.Dual.Order

/-!
# Combined labels on regular incidence strata

A combined wall label depends only on the incident indexed walls and the side
of a representative normal. It is independent of the particular regular point
in that incidence stratum and of the transverse direction on the chosen side.
This supplies well-defined propagation labels for signed simultaneous events,
without requiring an adapted cell or choosing a transverse vector for each use.

This generalizes the comparison argument of
`DirectedDiagram.combinedLabel_eq_of_mem_intrinsicInterior_adaptedWall`.
The proof reuses `DirectedDiagram.combinedLabel_eq_prod` and
`LinearMap.apply_pos_iff_of_ker_le_ker`. Its geometric input is
`Convex.affineSpan_eq_of_notMem_singularSupport`: all walls through a regular
point have the same tangent hyperplane. The crossing conventions follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
equation (8) and §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

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
  {k : ℕ} {θ η v w : V}

/-- Equal incident index sets and equal choices of signed factors give equal
combined labels. Nontransverse directions are allowed in this comparison. -/
theorem combinedLabel_eq_of_incident_iff_of_pos_iff
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hη : η ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hinc : ∀ j : D.active k, θ ∈ (D.wall j).support ↔ η ∈ (D.wall j).support)
    (hsign : ∀ j : D.active k, θ ∈ (D.wall j).support →
      (0 < h.realCharacter (D.wall j).normal v ↔
        0 < h.realCharacter (D.wall j).normal w)) :
    D.combinedLabel k θ v hθ = D.combinedLabel k η w hη := by
  classical
  let S := (Set.toFinite {j : D.active k | θ ∈ (D.wall j).support}).toFinset
  have hS (j : D.active k) : j ∈ S.toList ↔ θ ∈ (D.wall j).support := by simp [S]
  rw [D.combinedLabel_eq_prod k θ v hθ S.toList S.nodup_toList hS,
    D.combinedLabel_eq_prod k η w hη S.toList S.nodup_toList (fun j => (hS j).trans (hinc j))]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  simp only [hsign j ((hS j).mp hj)]

/-- On a regular incidence stratum, matching nonzero signs at one incident wall
suffice to identify the entire combined label. All other incident normals may
have either coorientation. No consistency or adapted-cell hypothesis is needed. -/
theorem combinedLabel_eq_of_incident_iff_of_mul_pos
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hη : η ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hinc : ∀ j : D.active k, θ ∈ (D.wall j).support ↔ η ∈ (D.wall j).support)
    (b : D.active k) (hb : θ ∈ (D.wall b).support)
    (hsign : 0 < h.realCharacter (D.wall b).normal v *
      h.realCharacter (D.wall b).normal w) :
    D.combinedLabel k θ v hθ = D.combinedLabel k η w hη := by
  apply D.combinedLabel_eq_of_incident_iff_of_pos_iff hθ hη hinc
  intro j hj
  have hdir := congrArg AffineSubspace.direction
    (affineSpan_eq_of_notMem_singularSupport hθ hb hj)
  have hker : (h.realCharacter (D.wall b).normal).ker ≤
      (h.realCharacter (D.wall j).normal).ker := by
    rw [← (D.wall b).direction_support, ← (D.wall j).direction_support]
    exact hdir.le
  rcases mul_pos_iff.mp hsign with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · exact (h.realCharacter (D.wall b).normal).apply_pos_iff_of_ker_le_ker _ hker hv hw
  · have hker' : (-h.realCharacter (D.wall b).normal).ker ≤
        (h.realCharacter (D.wall j).normal).ker := by simpa only [LinearMap.ker_neg] using hker
    exact (-h.realCharacter (D.wall b).normal).apply_pos_iff_of_ker_le_ker _ hker'
      (by simpa only [LinearMap.neg_apply] using neg_pos.mpr hv)
      (by simpa only [LinearMap.neg_apply] using neg_pos.mpr hw)

end Mei.DirectedDiagram
