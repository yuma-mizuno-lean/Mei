/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Crossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Rectangle

/-!
# Height independence of probe coefficients

Over an endpoint missing the affine spans of active base walls, every regular
height gives the same vertical probe coefficient in a consistent diagram. The
segment joining two heights may cross module-wall boundaries: the comparison
uses short upward crossings and disjoint parallel segments above and below the
slice. Intermediate heights need not be regular.

The normal classification in `ModuleProbe.wallGroup_cases_of_ne_one` makes the
height direction tangent to every active wall. We apply
`DirectedDiagram.combinedLabel_eq_of_parallel_displacement` and the coefficient
extraction of `ModuleProbe.verticalCoefficient`. This is the height comparison
for the probe construction of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)

local notation "v" => (0, j (0, 1))
local notation "y" => (0, j (1, 0))

/-- At any two regular heights over an endpoint off the active base-wall
hyperplanes, the vertical coefficients of a consistent probe diagram agree.
There is no assumption on the intermediate heights. The point may lie in any
probe slice, and the height displacement may have either sign. -/
theorem verticalCoefficient_eq_of_height (k : ℕ) (hD : D.LevelConsistent (k + 1))
    (θ : V × E) (t : ℝ)
    (hθ : θ ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (hη : θ + t • y ∉ singularSupport
      (fun a : D.active (k + 1) => (D.wall a).support))
    (hbase : ∀ a : D.active (k + 1),
      (D.wall a).normal ∈ Set.range (baseNormal (Λ := Λ)) →
        θ ∉ affineSpan ℝ (D.wall a).support) :
    verticalCoefficient d ℳ p ℒ H h h' D k (θ + t • y) hη =
      verticalCoefficient d ℳ p ℒ H h h' D k θ hθ := by
  have hparallel (a : D.active (k + 1))
      (ha : (h.prod h').realCharacter (D.wall a).normal v = 0) :
      θ ∉ affineSpan ℝ (D.wall a).support := by
    apply hbase a
    apply (mem_range_baseNormal _).mpr
    refine ⟨normal_height_eq_zero_of_label_ne_one d ℳ p ℒ H h h' (D.wall a)
      (D.label_ne_one_of_mem_active a.property), ?_⟩
    have he := (h.prod h').realCharacter_apply (D.wall a).normal (0, 0, 1)
    have hc : ((D.wall a).normal (0, 0, 1) : ℝ) = 0 := by
      simpa only [AddMonoidHom.coe_prodMap, Prod.map_apply, map_zero, ha] using he.symm
    exact Int.cast_eq_zero.mp hc
  have he := D.combinedLabel_eq_of_parallel_displacement (k + 1) hD θ v (t • y)
    hθ hη (fun a => by
      rw [map_smul]
      have hz := normal_height_eq_zero_of_label_ne_one d ℳ p ℒ H h h' (D.wall a)
        (D.label_ne_one_of_mem_active a.property)
      have heval := (h.prod h').realCharacter_apply (D.wall a).normal (0, 1, 0)
      have heval' : (h.prod h').realCharacter (D.wall a).normal y = 0 := by
        simpa only [AddMonoidHom.coe_prodMap, Prod.map_apply, map_zero, hz, Int.cast_zero]
          using heval
      rw [heval', smul_zero])
    hparallel
  simp only [verticalCoefficient_def, he]

end Mei.ModuleProbe
