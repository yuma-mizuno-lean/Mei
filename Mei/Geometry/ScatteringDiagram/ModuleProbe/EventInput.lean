/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Segment
public import Mei.Geometry.Convex.Polyhedron.Path.Incoming

/-!
# Geometric inputs to the segment probe recursion

The suffix-transported coefficients in the segment recursion are actual probe
values just before the corresponding simultaneous crossing. These values can
be read arbitrarily close to each event on the original incoming segment.
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

/-- Each algebraic event input is the actual lower-cutoff probe field at points
of the initial segment arbitrarily close to that event from the incoming side.
Only consistency of the base diagram is needed for this identification. -/
theorem eventually_exists_extendedCoefficientField_eq_eventInput
    (k : ℕ) (hBc : B.LevelConsistent k)
    {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (e : x ⟶ y) (j : Fin (orderedCrossingTimes e).length) :
    let T := (orderedCrossingTimes e).reverse
    let g := labels (k + 1) e
    ∀ᶠ t : ℝ in 𝓝[<] T[j.val]'(by simpa only [T, List.length_reverse] using j.isLt),
      t ∈ Ioo (0 : ℝ) 1 ∧
      ∃ z : WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
        z.val = AffineMap.lineMap x.val y.val t ∧
        field k hBc ((restriction k).obj z) =
          (A).truncatedBCHAction d ℒ k
            ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (g.drop (j.val + 1)).prod)
            (field k hBc ((restriction k).obj x)) := by
  dsimp only
  filter_upwards [eventually_exists_segmentPathProduct_eq_drop
    (fun c : B.active (k + 1) => h.realCharacter (B.wall c).normal)
    (fun c => CompletedGroup.projection (k + 1) (B.wall c).label)
    (B.activeLabels_commute (k + 1)) e j] with t ht
  obtain ⟨ht, z, a, hz, ha⟩ := ht
  refine ⟨ht, z, hz, ?_⟩
  rw [extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k
      hBc ((restriction k).obj x) ((restriction k).obj z),
    B.levelTransport_eq_levelPathProduct hBc ((restriction k).mapPath a.toPath),
    ← B.truncation_levelPathProduct (Nat.le_succ k) a.toPath,
    B.levelPathProduct_eq_wallPathProduct _ _ (B.activeLabels_commute _),
    Quiver.Path.wallPathProduct_toPath, ha]
  -- The tower projection carries the same group structure as the truncated BCH group.
  rfl

/-- The change in the highest retained component is a finite sum over crossings
and strictly lower input degrees, read from the actual probe field at a point on
the incoming side of every event. All these points may be chosen
within any prescribed positive parameter distance of their respective events.
No genericity or commutation between different events is required. -/
theorem exists_shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_eventInputs
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (e : x ⟶ y) (q : Γ) (hq : d.degree (q - p) = k + 1)
    {ε : ℝ} (hε : 0 < ε) :
    let T := (orderedCrossingTimes e).reverse
    let g := labels (k + 1) e
    ∃ (t : Fin g.length → ℝ)
      (z : Fin g.length → WallComplement (fun c : B.active (k + 1) => (B.wall c).support)),
      (∀ j : Fin g.length,
        t j ∈ Ioo (0 : ℝ) (T[j.val]'(by simpa only [g, List.length_map] using j.isLt)) ∧
        T[j.val]'(by simpa only [g, List.length_map] using j.isLt) - t j < ε ∧
        (z j).val = AffineMap.lineMap x.val y.val (t j)) ∧
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
                        (d.mem_cutoff.mp
                          ((d.finite_cutoff k).mem_toFinset.mp n.property)).2)
                      (field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj (z j))))))) := by
  dsimp only
  let T := (orderedCrossingTimes e).reverse
  let g := labels (k + 1) e
  have hchoose (j : Fin g.length) :
      ∃ (t : ℝ) (z : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)),
        t ∈ Ioo (0 : ℝ) (T[j.val]'(by simpa only [g, List.length_map] using j.isLt)) ∧
        T[j.val]'(by simpa only [g, List.length_map] using j.isLt) - t < ε ∧
        z.val = AffineMap.lineMap x.val y.val t ∧
        field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj z) =
          (A).truncatedBCHAction d ℒ k
            ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (g.drop (j.val + 1)).prod)
            (field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj x)) := by
    have hj : j.val < (orderedCrossingTimes e).length := by
      simpa only [g, List.length_map, List.length_reverse] using j.isLt
    have hjT : j.val < T.length := by simpa only [T, List.length_reverse] using hj
    have hevent := eventually_exists_extendedCoefficientField_eq_eventInput
      d ℳ p ℒ H h h' D B k (hBc.mono (Nat.le_succ k)) e ⟨j.val, hj⟩
    have hnear : ∀ᶠ t : ℝ in 𝓝[<] T[j.val], T[j.val] - ε < t :=
      (eventually_gt_nhds (by linarith : T[j.val] - ε < T[j.val])).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨t, ⟨⟨ht, z, hz, he⟩, hnear⟩, htτ⟩ :=
      (hevent.and hnear |>.and self_mem_nhdsWithin).exists
    exact ⟨t, z, ⟨ht.1, htτ⟩, by linarith, hz, he⟩
  choose t z ht hnear hz he using hchoose
  refine ⟨t, z, fun j => ⟨ht j, hnear j, hz j⟩, ?_⟩
  rw [shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_crossings
    d ℳ p ℒ H h h' D B k hBc hD hB e q hq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← he j]

end Mei.ModuleProbe
