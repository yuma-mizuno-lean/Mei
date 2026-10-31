/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension
public import Mei.Algebra.Lie.Graded.Shifted.Correction

/-!
# Lower-degree crossing recursion for probe coefficients

The degree-`q` change of the probe coefficient across a regular wall germ is a
finite sum of the signed combined wall action on strictly lower-degree input
components. The input components are read from the actual probe field one
cutoff earlier. Short transverse crossings realize this formula at every regular
germ, without requiring auxiliary genericity of their endpoints.

Coincident walls contribute their combined label. Entire homogeneous decorations
are retained, including changes invisible under the spatial direction map. The
formula is the local step in the backward-ray recursion comparing probe
coefficients with broken-line sums in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).

We combine `ModuleProbe.extendedCoefficientField_eq_transport`, its cutoff
compatibility, the finite shifted BCH correction formula, and
`DirectedDiagram.eventually_exists_levelPathProduct_eq_combinedLabel`.
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
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
  (B : DirectedDiagram (d := d) h H κ)

local notation "A" => d.shiftedLieFiltration ℒ ℳ p
local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B

/-- The change of a retained probe component along a base path is computed from
strictly lower-degree coefficients at its initial endpoint. The lower coefficients
are those of the compatible extended probe field at the preceding cutoff. -/
theorem shiftedQuotientComponent_extendedCoefficientField_eq_add_sum
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (γ : AdmissiblePLPath x y) (q : Γ) (hq : d.degree (q - p) = k + 1) :
    d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc y) =
      d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc x) +
        ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
          d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
            ((A).truncatedBCHAction d ℒ (k + 1) (B.levelPathProduct (k + 1) γ)
              (Submodule.Quotient.mk
                (shiftedInclusion ℳ d.monoid p
                  ⟨n.val, (d.mem_cutoff.mp
                    ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                  (d.shiftedQuotientComponent ℳ p (p + n.val) k
                    (by simpa only [add_sub_cancel_left] using
                      (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp
                        n.property)).2)
                    (field k (hBc.mono (Nat.le_succ k))
                      ((WallComplement.restrictPrefunctor
                        (fun c : B.active (k + 1) => (B.wall c).support)
                        (Set.inclusion (B.active_mono (Nat.le_succ k)))).obj x)))))) := by
  classical
  have he := extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B (k + 1) hBc x y
  rw [B.levelTransport_eq_levelPathProduct hBc γ] at he
  rw [he, d.shiftedQuotientComponent_truncatedBCHAction_eq_add_sum ℒ ℳ p k _ _ q hq]
  rw [transition_extendedCoefficientField d ℳ p ℒ H h h' D B
    (Nat.le_succ k) (hBc.mono (Nat.le_succ k)) hBc hD hB]

/-- Every regular transverse wall germ admits arbitrarily short crossings whose
probe-coefficient jump is the finite lower-degree recursion for its signed
combined label. The endpoints need only avoid the active base walls. -/
theorem eventually_exists_extendedCoefficientField_eq_add_sum
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (θ v : V)
    (hθ : θ ∉ singularSupport (fun c : B.active (k + 1) => (B.wall c).support))
    (hv : ∀ c : B.active (k + 1), θ ∈ (B.wall c).support →
      h.realCharacter (B.wall c).normal v ≠ 0)
    (q : Γ) (hq : d.degree (q - p) = k + 1) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∃ x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
        x.val = θ - ε • v ∧ y.val = θ + ε • v ∧
        d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc y) =
          d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc x) +
            ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
              d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
                ((A).truncatedBCHAction d ℒ (k + 1) (B.combinedLabel (k + 1) θ v hθ)
                  (Submodule.Quotient.mk
                    (shiftedInclusion ℳ d.monoid p
                      ⟨n.val, (d.mem_cutoff.mp
                        ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                      (d.shiftedQuotientComponent ℳ p (p + n.val) k
                        (by simpa only [add_sub_cancel_left] using
                          (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp
                            n.property)).2)
                        (field k (hBc.mono (Nat.le_succ k))
                          ((WallComplement.restrictPrefunctor
                            (fun c : B.active (k + 1) => (B.wall c).support)
                            (Set.inclusion (B.active_mono (Nat.le_succ k)))).obj x)))))) := by
  filter_upwards [B.eventually_exists_levelPathProduct_eq_combinedLabel (k + 1) θ v hθ hv]
    with ε hε
  obtain ⟨x, y, e, hx, hy, he⟩ := hε
  refine ⟨x, y, hx, hy, ?_⟩
  simpa only [he] using
    shiftedQuotientComponent_extendedCoefficientField_eq_add_sum
      d ℳ p ℒ H h h' D B k hBc hD hB e.toPath q hq

end Mei.ModuleProbe
