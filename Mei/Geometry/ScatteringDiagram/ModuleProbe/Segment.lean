/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension
public import Mei.Algebra.Lie.Graded.Shifted.Correction

/-!
# Summing probe corrections along an admissible segment

The change in the probe field along a finite admissible segment is the sum of
its crossing corrections. Each simultaneous event uses the signed combined
label, retaining coincident indexed walls. Its input is transported through the
earlier events at one lower coefficient cutoff. Thus the component of relative
degree `k + 1` is computed from degrees at most `k`, event by event, without
assuming that the labels commute or choosing lifts of lower-order coefficients.

The event list is in multiplication order, so its rightmost factor is the first
crossing. A suffix of that list transports the incoming coefficient up to the
next event. These are algebraic transported inputs; identification with probe
values on geometric incoming germs and the infinite backward-ray initial
condition are separate steps.

We use `ModuleFiltration.truncatedBCHAction_list_prod_eq_add_sum`, the shifted
homogeneous correction formula, and the transport and cutoff compatibility of
`ModuleProbe.extendedCoefficientField`. The recursion follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex Mei.Convex.WallComplement

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
local notation "labels" k:max e:max => (List.map
  (crossingEventProduct (G := d.truncatedGroup ℒ k)
    (fun c : B.active k => h.realCharacter
      (DirectedWall.normal (DirectedDiagram.wall B c)))
    (fun c => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall B c)))
    (B.activeLabels_commute k) e)
      (List.reverse (orderedCrossingTimes e)))
local notation "restriction" k:max => (WallComplement.restrictPrefunctor
  (fun c : B.active (k + 1) => DirectedWall.support (DirectedDiagram.wall B c))
  (Set.inclusion (B.active_mono (Nat.le_succ k))))

/-- The actual probe field changes by the sum of all simultaneous crossing
corrections. Every correction reads an input transported only at the preceding
cutoff. Empty crossing lists give zero change, and inverse crossings need no
separate convention. -/
theorem extendedCoefficientField_eq_add_sum_crossings
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (e : x ⟶ y) :
    let g := labels (k + 1) e
    field (k + 1) hBc y = field (k + 1) hBc x +
      ∑ j : Fin g.length, (A).truncatedBCHCorrection d ℒ k g[j]
        ((A).truncatedBCHAction d ℒ k
          ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (g.drop (j.val + 1)).prod)
          (field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj x))) := by
  dsimp only
  have he : B.levelPathProduct (k + 1) e.toPath = (labels (k + 1) e).prod := by
    rw [B.levelPathProduct_eq_wallPathProduct _ _ (B.activeLabels_commute _),
      Quiver.Path.wallPathProduct_toPath, segmentPathProduct_def]
    -- The tower projection has the same group structure as the truncated BCH group.
    rfl
  rw [extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B (k + 1) hBc x y,
    B.levelTransport_eq_levelPathProduct hBc e.toPath, he,
    (A).truncatedBCHAction_list_prod_eq_add_sum d ℒ k,
    transition_extendedCoefficientField d ℳ p ℒ H h h' D B
      (Nat.le_succ k) (hBc.mono (Nat.le_succ k)) hBc hD hB]

/-- At a fixed outgoing degree, the segment jump is a finite double sum over
crossing events and strictly lower input degrees. The input to each event is
transported through the earlier events at order `k`; the signed event action
then selects the whole outgoing component at order `k + 1`. -/
theorem shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_crossings
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (e : x ⟶ y) (q : Γ) (hq : d.degree (q - p) = k + 1) :
    let g := labels (k + 1) e
    d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc y) =
      d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc x) +
        ∑ j : Fin g.length, ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
          d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
            ((A).truncatedBCHAction d ℒ (k + 1) g[j]
              (Submodule.Quotient.mk
                (shiftedInclusion ℳ d.monoid p
                  ⟨n.val, (d.mem_cutoff.mp
                    ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                  (d.shiftedQuotientComponent ℳ p (p + n.val) k
                    (by simpa only [add_sub_cancel_left] using
                      (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp n.property)).2)
                    ((A).truncatedBCHAction d ℒ k
                      ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
                        (g.drop (j.val + 1)).prod)
                      (field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj x))))))) := by
  dsimp only
  rw [extendedCoefficientField_eq_add_sum_crossings d ℳ p ℒ H h h' D B k hBc hD hB e,
    map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact d.shiftedQuotientComponent_truncatedBCHCorrection_eq_sum ℒ ℳ p k _ _ q hq

end Mei.ModuleProbe
