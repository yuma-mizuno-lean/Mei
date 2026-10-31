/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Segment
public import Mei.Geometry.Convex.Polyhedron.Path.Incoming

import Mathlib.Topology.Algebra.Group.Order

/-!
# Geometric inputs to the segment probe recursion

The suffix-transported coefficients in the segment recursion are actual probe
values just before the corresponding simultaneous crossing. These values can
be read arbitrarily close to each event on the original incoming segment.
The identification extends to any smaller cutoff. A common sufficiently small
positive displacement supplies incoming inputs for all events at once.
Consequently the finite correction sum can use geometric incoming values,
without retaining transport through all previous events in every summand.

We combine `WallComplement.eventually_exists_segmentPathProduct_eq_drop`,
`ModuleProbe.extendedCoefficientField_eq_transport`, cutoff compatibility of
base transport, and the existing segment correction formula. This is the finite
segment step of the backward-ray recursion in Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
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

local notation "cutoffRestriction" hkl:max => (WallComplement.restrictPrefunctor
  (fun c : B.active _ => DirectedWall.support (DirectedDiagram.wall B c))
  (Set.inclusion (B.active_mono hkl)))

/-- Each algebraic event input is the actual lower-cutoff probe field at points
of the initial segment arbitrarily close to that event from the incoming side,
at any smaller cutoff. Only consistency of the base diagram is needed for this
identification. -/
theorem eventually_exists_extendedCoefficientField_eq_eventInput
    {k l : ℕ} (hkl : k ≤ l) (hBc : B.LevelConsistent k)
    {x y : WallComplement (fun c : B.active l => (B.wall c).support)}
    (e : x ⟶ y) (j : Fin (orderedCrossingTimes e).length) :
    let T := (orderedCrossingTimes e).reverse
    let g := labels l e
    ∀ᶠ t : ℝ in 𝓝[<] T[j.val]'(by simpa only [T, List.length_reverse] using j.isLt),
      t ∈ Ioo (0 : ℝ) 1 ∧
      ∃ z : WallComplement (fun c : B.active l => (B.wall c).support),
        z.val = AffineMap.lineMap x.val y.val t ∧
        field k hBc ((cutoffRestriction hkl).obj z) =
          (A).truncatedBCHAction d ℒ k
            ((d.truncationMap ℒ hkl).bchGroupMap (g.drop (j.val + 1)).prod)
            (field k hBc ((cutoffRestriction hkl).obj x)) := by
  dsimp only
  filter_upwards [eventually_exists_segmentPathProduct_eq_drop
    (fun c : B.active l => h.realCharacter (B.wall c).normal)
    (fun c => CompletedGroup.projection l (B.wall c).label)
    (B.activeLabels_commute l) e j] with t ht
  obtain ⟨ht, z, a, hz, ha⟩ := ht
  refine ⟨ht, z, hz, ?_⟩
  rw [extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k
      hBc ((cutoffRestriction hkl).obj x) ((cutoffRestriction hkl).obj z),
    B.levelTransport_eq_levelPathProduct hBc ((cutoffRestriction hkl).mapPath a.toPath),
    ← B.truncation_levelPathProduct hkl a.toPath,
    B.levelPathProduct_eq_wallPathProduct _ _ (B.activeLabels_commute _),
    Quiver.Path.wallPathProduct_toPath, ha]
  -- The tower projection carries the same group structure as the truncated BCH group.
  rfl

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
    let g := labels (k + 1) e
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∃ z : Fin g.length → WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
      (∀ j : Fin g.length, (z j).val = AffineMap.lineMap x.val y.val
        ((orderedCrossingTimes e).reverse[j.val]'(by
          simpa only [g, List.length_map] using j.isLt) - ε)) ∧
      field (k + 1) hBc y = field (k + 1) hBc x +
        ∑ j : Fin g.length, (A).truncatedBCHCorrection d ℒ k g[j]
          (field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj (z j))) := by
  classical
  dsimp only
  have hg (j : Fin (labels (k + 1) e).length) :
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ∃ z : WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
          z.val = AffineMap.lineMap x.val y.val
            ((orderedCrossingTimes e).reverse[j.val]'(by
              simpa only [List.length_map] using j.isLt) - ε) ∧
          field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj z) =
            (A).truncatedBCHAction d ℒ k
              ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
                ((labels (k + 1) e).drop (j.val + 1)).prod)
              (field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj x)) := by
    have hj : j.val < (orderedCrossingTimes e).reverse.length := by
      simpa only [List.length_map] using j.isLt
    have htendsto : Tendsto
        (fun ε : ℝ => (orderedCrossingTimes e).reverse[j.val] - ε)
        (𝓝[>] 0) (𝓝[<] (orderedCrossingTimes e).reverse[j.val]) := by
      simpa only [Tendsto, sub_zero] using
        (Filter.map_subLeft_nhdsGT
          (c := (orderedCrossingTimes e).reverse[j.val]) (a := (0 : ℝ))).le
    filter_upwards [htendsto.eventually
      (eventually_exists_extendedCoefficientField_eq_eventInput d ℳ p ℒ H h h' D B
        (Nat.le_succ k) (hBc.mono (Nat.le_succ k)) e
        ⟨j.val, by simpa only [List.length_reverse] using hj⟩)] with ε hε
    exact hε.2
  filter_upwards [Filter.eventually_all.mpr hg] with ε hε
  choose z hz hvalue using hε
  refine ⟨z, hz, ?_⟩
  rw [extendedCoefficientField_eq_add_sum_crossings d ℳ p ℒ H h h' D B k hBc hD hB e]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hvalue j]

end Mei.ModuleProbe
