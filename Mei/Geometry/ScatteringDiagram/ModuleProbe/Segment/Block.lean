/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Segment
public import Mei.Algebra.Lie.Graded.Shifted.Block

/-!
# All degree blocks of probe segment corrections

At one fixed wall inventory, every retained probe component changes by the sum
of crossing blocks applied to the preceding-cutoff inputs. The output degree
need not be the highest retained degree. Keeping all output degrees at this
same geometric cutoff permits comparison with actual decorated-ray recurrences
without changing their encounter alphabet.

We combine `extendedCoefficientField_eq_add_sum_crossings` with the degree-block
expansion of a BCH correction. The backward-ray interpretation follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

open TauCeti (WallComplement)

public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

open Mei.Convex TauCeti.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
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

/-- Every retained component of a segment jump is the finite sum of its
crossing blocks. Inputs are transported at the preceding cutoff; all event
labels and output components use the fixed larger cutoff. -/
theorem shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_labelBlock
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (e : x ⟶ y) (n : d.cutoff (k + 1)) :
    let g : List (d.truncatedGroup ℒ (k + 1)) := labels (k + 1) e
    d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1)
        (PositiveDegrees.degree_add_val_sub_self_le d p (k + 1) n)
        (field (k + 1) hBc y) =
      d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1)
        (PositiveDegrees.degree_add_val_sub_self_le d p (k + 1) n)
        (field (k + 1) hBc x) +
      ∑ b : Fin g.length, ∑ m : d.cutoff k,
        PositiveDegrees.labelBlock d ℳ p ℒ (k + 1) (g[b]) n
          ⟨m.val, d.cutoff_mono (Nat.le_succ k) m.property⟩
          (d.shiftedQuotientComponent ℳ p (p + m.val) k
            (PositiveDegrees.degree_add_val_sub_self_le d p k m)
            ((A).truncatedBCHAction d ℒ k
              ((d.lieTruncationMap ℒ (Nat.le_succ k)).bchGroupMap
                (g.drop (b.val + 1)).prod)
              (field k (hBc.mono (Nat.le_succ k))
                ((WallComplement.restrictPrefunctor (fun c : B.active (k + 1) => (B.wall c).support)
                  (Set.inclusion (B.active_mono (Nat.le_succ k)))).obj x)))) := by
  dsimp only
  rw [extendedCoefficientField_eq_add_sum_crossings d ℳ p ℒ H h h' D B k hBc hD hB e,
    map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact PositiveDegrees.shiftedQuotientComponent_truncatedBCHCorrection_eq_sum_labelBlock
    d ℳ p ℒ k _ _ n

end Mei.ModuleProbe
