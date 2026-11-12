/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Crossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Vertical

/-!
# Generic endpoints admit probe coefficients

At each relative cutoff there is a finite exceptional arrangement of base
endpoints `Q` such that `(Q, 0)` is a regular point of the probe slice, every
incident wall is transverse to the upward probe direction, and no active base-wall
hyperplane contains `(Q, 0)`. Arbitrarily short upward crossings at `(Q, 0)` then
compute the negative exponential of the extracted coefficient. This applies to every
probe diagram, in particular to outgoing completions of the initial cylinders and
probe wall; consistency and purity of birth logarithms are unnecessary.

We combine `DirectedDiagram.exists_regular_vertical_points` with
`ModuleProbe.eventually_exists_levelPathProduct_eq_moduleBCHInclusion_neg_verticalCoefficient`.
The construction follows Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (DirectedWallSpaces)

open Set Filter Topology Mei.Convex

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
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)

local notation "v" => (0, j 1)

/-- An endpoint arrangement outside which the zero-slice point is regular and every
wall whose affine span contains it is transverse to the upward probe direction. -/
def coefficientArrangement (k : ℕ) : ExceptionalArrangement V :=
  (D.exists_regular_vertical_points h h' (k + 1)).choose

/-- Over a generic endpoint the zero-slice point is regular. -/
theorem regular_of_isGeneric (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) :
    (Q, (0 : E)) ∉ singularSupport (fun a : D.active (k + 1) => (D.wall a).support) :=
  ((D.exists_regular_vertical_points h h' (k + 1)).choose_spec Q hQ).1

/-- Over a generic endpoint every wall whose affine span contains the zero-slice
point is transverse to the upward probe direction. -/
theorem vertical_transverse_of_mem_affineSpan (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (a : D.active (k + 1)) (ha : (Q, (0 : E)) ∈ affineSpan ℝ (D.wall a).support) :
    (h.prod h').realCharacter (D.wall a).normal v ≠ 0 :=
  ((D.exists_regular_vertical_points h h' (k + 1)).choose_spec Q hQ).2 a ha

/-- All incident active walls over a generic endpoint are vertically transverse. -/
theorem vertical_transverse_of_isGeneric (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (a : D.active (k + 1)) (ha : (Q, (0 : E)) ∈ (D.wall a).support) :
    (h.prod h').realCharacter (D.wall a).normal v ≠ 0 :=
  vertical_transverse_of_mem_affineSpan d ℳ p ℒ H h h' D k Q hQ a
    (subset_affineSpan ℝ _ ha)

/-- An active base-wall hyperplane misses the zero-slice point over a generic
endpoint, since lifted base normals vanish on the upward probe direction. -/
theorem not_mem_base_affineSpan_of_isGeneric (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (a : D.active (k + 1)) (ha : (D.wall a).normal ∈ Set.range (baseNormal (Λ := Λ))) :
    (Q, (0 : E)) ∉ affineSpan ℝ (D.wall a).support := by
  intro hy
  obtain ⟨m, hm⟩ := ha
  apply vertical_transverse_of_mem_affineSpan d ℳ p ℒ H h h' D k Q hQ a hy
  rw [← hm]
  simp

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Over generic base endpoints, all sufficiently short upward crossings at the
zero-slice point compute the negative exponential of the same relative order-`k`
coefficient. -/
theorem eventually_exists_levelPathProduct_eq_of_isGeneric (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∃ (x z : WallComplement (fun a : D.active (k + 1) => (D.wall a).support))
        (e : x ⟶ z),
        x.val = (Q, (0 : E)) - t • v ∧ z.val = (Q, (0 : E)) + t • v ∧
        D.levelPathProduct (k + 1) e.toPath = moduleBCHInclusion d ℳ p ℒ k
          (Multiplicative.ofAdd (-verticalCoefficient d ℳ p ℒ H h h' D k (Q, 0)
            (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ))) :=
  eventually_exists_levelPathProduct_eq_moduleBCHInclusion_neg_verticalCoefficient
    d ℳ p ℒ H h h' D k _ _ (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)

end Mei.ModuleProbe
