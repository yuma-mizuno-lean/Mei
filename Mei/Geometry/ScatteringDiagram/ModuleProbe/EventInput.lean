/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Segment
public import Mei.Geometry.Convex.Polyhedron.Path.Prefix

/-!
# Geometric incoming inputs for probe crossing sums

Every partial transport occurring in the segment correction formula is the actual
probe field immediately before that crossing. For every sufficiently small
common positive displacement, evaluate the correction sum at the resulting
allowed incoming points. The lower-cutoff inputs are independent of how small
this displacement is chosen.

Simultaneous indexed walls remain a single signed event; labels at different
events need not commute. This is the geometric input to the backward-ray
recursion in Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5). We use
`WallComplement.eventually_exists_segmentPathProduct_eq_drop`, the transport law
of `extendedCoefficientField`, and its existing segment correction sum.
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

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
local notation "events" l:max e:max => (List.map
  (crossingEventProduct (G := d.truncatedGroup ℒ l)
    (fun c : B.active l => h.realCharacter
      (DirectedWall.normal (DirectedDiagram.wall B c)))
    (fun c => CompletedGroup.projection l
      (DirectedWall.label (DirectedDiagram.wall B c)))
    (B.activeLabels_commute l) e)
      (List.reverse (orderedCrossingTimes e)))
local notation "restriction" hkl:max => (WallComplement.restrictPrefunctor
  (fun c : B.active _ => DirectedWall.support (DirectedDiagram.wall B c))
  (Set.inclusion (B.active_mono hkl)))

/-- At any smaller cutoff, the suffix transport before an event equals the
actual probe field on every sufficiently short incoming subsegment. No
consistency of the probe diagram is required for this transport identity. -/
theorem eventually_exists_extendedCoefficientField_eq_drop
    {k l : ℕ} (hkl : k ≤ l) (hBc : B.LevelConsistent k)
    {x y : WallComplement (fun c : B.active l => (B.wall c).support)}
    (e : x ⟶ y) (j : Fin (orderedCrossingTimes e).reverse.length) :
    let g := events l e
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∃ z : WallComplement (fun c : B.active l => (B.wall c).support),
        z.val = AffineMap.lineMap x.val y.val ((orderedCrossingTimes e).reverse[j.val] - ε) ∧
        field k hBc ((restriction hkl).obj z) =
          (A).truncatedBCHAction d ℒ k
            ((d.truncationMap ℒ hkl).bchGroupMap (g.drop (j.val + 1)).prod)
            (field k hBc ((restriction hkl).obj x)) := by
  dsimp only
  filter_upwards [eventually_exists_segmentPathProduct_eq_drop
    (fun c : B.active l => h.realCharacter
      (DirectedWall.normal (DirectedDiagram.wall B c)))
    (fun c => CompletedGroup.projection l
      (DirectedWall.label (DirectedDiagram.wall B c)))
    (B.activeLabels_commute l) e j] with ε hε
  obtain ⟨z, e₁, hz, he⟩ := hε
  refine ⟨z, hz, ?_⟩
  have hprod : B.levelPathProduct l e₁.toPath = ((events l e).drop (j.val + 1)).prod := by
    rw [B.levelPathProduct_eq_wallPathProduct _ _ (B.activeLabels_commute _),
      Quiver.Path.wallPathProduct_toPath, he, List.map_drop]
    -- Tower projections and Lie truncations use the same BCH group structure.
    rfl
  rw [extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k hBc
    ((restriction hkl).obj x) ((restriction hkl).obj z),
    B.levelTransport_eq_levelPathProduct hBc ((restriction hkl).mapPath e₁.toPath),
    ← B.truncation_levelPathProduct hkl e₁.toPath, hprod]

/-- For every sufficiently small common displacement, the segment correction
sum reads the actual probe field immediately before each crossing. Only the
preceding-cutoff values at these allowed incoming points enter the corrections. -/
theorem eventually_exists_extendedCoefficientField_eq_add_sum_incoming
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (e : x ⟶ y) :
    let g := events (k + 1) e
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∃ z : Fin g.length → WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
      (∀ j : Fin g.length, (z j).val = AffineMap.lineMap x.val y.val
        ((orderedCrossingTimes e).reverse[j.val]'(by
          simpa only [g, List.length_map] using j.isLt) - ε)) ∧
      field (k + 1) hBc y = field (k + 1) hBc x +
        ∑ j : Fin g.length, (A).truncatedBCHCorrection d ℒ k g[j]
          (field k (hBc.mono (Nat.le_succ k)) ((restriction (Nat.le_succ k)).obj (z j))) := by
  classical
  dsimp only
  have hg (j : Fin (events (k + 1) e).length) :=
    eventually_exists_extendedCoefficientField_eq_drop d ℳ p ℒ H h h' D B
      (Nat.le_succ k) (hBc.mono (Nat.le_succ k)) e
      ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
  filter_upwards [Filter.eventually_all.mpr hg] with ε hε
  choose z hz hvalue using hε
  refine ⟨z, hz, ?_⟩
  rw [extendedCoefficientField_eq_add_sum_crossings d ℳ p ℒ H h h' D B k hBc hD hB e]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hvalue j]

end Mei.ModuleProbe
