/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Cylinder
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Map.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Replacement

/-!
# The charge-zero part of a probe completion

Forgetting the module summand and reincluding the base gives a degree-preserving
Lie endomorphism of the probe. It preserves every wall space, fixes base labels
and kills module labels. Thus it acts on directed diagrams without moving their
supports or normals.

The charge-zero image of any outgoing completion of a cylinder input and its
probe is equivalent to the cylinder over any outgoing completion of the base
input. This identifies its base transport without requiring a particular choice
of correction walls, or a faithful coefficient action.

We use Mathlib's semidirect projection and inclusion, `DirectedDiagram.map`,
`ModuleProbe.completedBaseProjection`, and
`DirectedDiagram.IsOutgoingCompletion.equivalent_of_input`. The probe construction
and the charge-zero comparison follow Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E : Type*} {M L : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

section WallSpaces

variable [AddCommMonoid Λ] {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [IsWallAnnihilating H ℳ]

/-- Forgetting charge one preserves all the directed probe wall spaces. -/
theorem chargeZeroGradedLieHom_mem_wall (n : Γ × ℤ × ℤ) (m : (Λ × ℤ × ℤ) →+ ℤ)
    (x : ProbeLie d ℳ p ℒ) (hx : x ∈ (wallSpaces d ℳ p ℒ H).wall n m) :
    chargeZeroGradedLieHom d ℳ p ℒ x ∈ (wallSpaces d ℳ p ℒ H).wall n m := by
  rw [wallSpaces_wall, mem_wallSubmodule_iff] at hx ⊢
  rcases hx with rfl | ⟨q, m₀, y, rfl, rfl, hy, rfl⟩ | ⟨q, c, rfl, hc, rfl, hx⟩
  · exact Or.inl (map_zero _)
  · exact Or.inr (Or.inl ⟨q, m₀, y, rfl, rfl, hy, by simp⟩)
  · exact Or.inl (by simp [((mem_grading_module d ℳ p ℒ q x).mp hx).1])

end WallSpaces

variable [AddCommGroup Λ] {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [IsWallAnnihilating H ℳ] [DirectSum.Decomposition ℳ]
  [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)

/-- A charge-zero cylinder wall is fixed by forgetting the module summand. -/
@[simp]
theorem baseCylinder_map_chargeZeroGradedLieHom (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H) = baseCylinder d ℳ p ℒ H h h' W := by
  apply DirectedWall.ext <;> simp

/-- Forgetting the module summand deletes the probe label, including nonzero inputs. -/
@[simp]
theorem completedBaseProjection_probeWall_label (a : ℳ p) :
    completedBaseProjection d ℳ p ℒ (probeWall d ℳ p ℒ H h h' a).label = 1 := by
  rw [probeWall_label, completedBaseProjection_expToCompletion]
  simp [moduleInclusion]

/-- At every cutoff, the charge-zero initial input is just the cylinder input:
the additional full probe hyperplane carries the identity label. -/
theorem initialDiagram_map_chargeZeroGradedLieHom_equivalent_cylinderDiagram {ι : Type*}
    (D : DirectedDiagram (d := d) h H ι) (a : ℳ p) :
    ((initialDiagram d ℳ p ℒ H h h' D a).map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' D) := by
  let Z := DirectedDiagram.ofFinite (fun _ : Unit =>
    (probeWall d ℳ p ℒ H h h' a).map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H))
  have he : (initialDiagram d ℳ p ℒ H h h' D a).map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H) =
      (cylinderDiagram d ℳ p ℒ H h h' D).append Z := by
    apply DirectedDiagram.ext
    funext b
    cases b <;> simp [Z]
  rw [he, DirectedDiagram.equivalent_iff]
  intro k
  apply DirectedDiagram.append_levelEquivalent_left
  intro b
  simp only [Z, DirectedDiagram.ofFinite_wall, DirectedWall.map_label,
    completedMap_chargeZeroGradedLieHom, completedBaseProjection_probeWall_label, map_one]

/-- The charge-zero part of a probe completion is the cylinder over a prescribed
base completion, up to all-order diagram equivalence. No purity or choice of
correction algorithm is needed. -/
theorem map_chargeZeroGradedLieHom_equivalent_cylinderDiagram_of_isOutgoingCompletion
    {ι κ κ' : Type*}
    (D₀ : DirectedDiagram (d := d) h H ι)
    (D : DirectedDiagram (d := d) h H (ι ⊕ κ)) (a : ℳ p)
    (F : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ'))
    (hD : DirectedDiagram.IsOutgoingCompletion D₀.wall D)
    (hF : DirectedDiagram.IsOutgoingCompletion (initialDiagram d ℳ p ℒ H h h' D₀ a).wall F) :
    (F.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' D) := by
  have hC : DirectedDiagram.IsOutgoingCompletion
      (cylinderDiagram d ℳ p ℒ H h h' D₀).wall
      (cylinderDiagram d ℳ p ℒ H h h' D) := by
    convert cylinderDiagram_isOutgoingCompletion d ℳ p ℒ H h h' hD using 1
    exact funext (cylinderDiagram_wall d ℳ p ℒ H h h' D₀)
  have hZ : DirectedDiagram.IsOutgoingCompletion
      ((initialDiagram d ℳ p ℒ H h h' D₀ a).map (chargeZeroGradedLieHom d ℳ p ℒ)
        (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).wall
      (F.map (chargeZeroGradedLieHom d ℳ p ℒ)
        (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)) := by
    convert hF.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H) using 1
    exact funext ((initialDiagram d ℳ p ℒ H h h' D₀ a).map_wall _ _)
  exact hZ.equivalent_of_input hC
    (initialDiagram_map_chargeZeroGradedLieHom_equivalent_cylinderDiagram d ℳ p ℒ H h h' D₀ a)

end Mei.ModuleProbe
