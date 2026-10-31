/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.EventInput.Straight

/-!
# Probe correction sums at generic incoming points

One arbitrarily small perturbation works for finitely many incoming directions,
every admissible segment in those directions, and every simultaneous crossing
of each segment. For all sufficiently small positive displacements, the perturbed
incoming points avoid any prescribed finite exceptional arrangement. The probe
correction sum reads its lower-order inputs at these generic points.

The direction is normalized independently of segment length. The perturbation
is chosen before the segment and its endpoints; only the eventual displacement
bound depends on the segment. Thus degree induction can use generic incoming
values even when the crossing itself lies on the exceptional arrangement.
Coincident wall indices remain a single event, with their combined signed label.

We combine `eventually_exists_extendedCoefficientField_eq_eventInput_of_mul_pos`,
`eventually_exists_extendedCoefficientField_eq_of_mul_pos`, and
`ExceptionalArrangement.exists_norm_lt_forall_eventually_isGeneric` with the
existing finite component correction formula. The recursion follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
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
    (B.activeLabels_commute k) e) (List.reverse (orderedCrossingTimes e)))
local notation "restriction" k:max => (WallComplement.restrictPrefunctor
  (fun c : B.active (k + 1) => DirectedWall.support (DirectedDiagram.wall B c))
  (Set.inclusion (B.active_mono (Nat.le_succ k))))

/-- A single arbitrarily small perturbation, chosen for a finite set of normalized
incoming directions, makes every lower-order event input generic for a prescribed
finite arrangement. For every admissible segment in one of those directions,
the highest-component correction formula holds at all sufficiently small common
positive displacements from its events. The perturbation is independent of segment
length, endpoints and output degree; only the eventual bound may vary.

The first crossing is the rightmost label. The sum keeps simultaneous wall
crossings combined, and its input degrees have order at most `k`. Zero directions
and segments without crossings are allowed. -/
theorem exists_norm_lt_forall_eventually_extendedCoefficientField_eq_add_sum_genericInputs
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (F : ExceptionalArrangement V) {η : Type*} [Finite η] (v : η → V)
    {s : ℝ} (hs : 0 < s) :
    ∃ r : V, ‖r‖ < s ∧
      (∀ a (c : B.active (k + 1)), h.realCharacter (B.wall c).normal (v a) ≠ 0 →
        0 < h.realCharacter (B.wall c).normal (v a + r) *
          h.realCharacter (B.wall c).normal (v a)) ∧
      ∀ (x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support))
        (e : x ⟶ y) (a : η) (l : ℝ), 0 < l → x.val - y.val = l • v a →
        ∀ (q : Γ) (hq : d.degree (q - p) = k + 1),
          let τ := (orderedCrossingTimes e).reverse
          let g := labels (k + 1) e
          ∀ᶠ δ : ℝ in 𝓝[>] 0,
            ∃ z : Fin g.length → WallComplement (fun c : B.active k => (B.wall c).support),
              (∀ b : Fin g.length,
                (z b).val = AffineMap.lineMap x.val y.val
                  (τ[b.val]'(by simpa only [g, List.length_map] using b.isLt)) +
                    δ • (v a + r) ∧ F.IsGeneric (z b).val) ∧
              d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc y) =
                d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) (field (k + 1) hBc x) +
                  ∑ b : Fin g.length, ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
                    d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
                      ((A).truncatedBCHAction d ℒ (k + 1) g[b]
                        (Submodule.Quotient.mk
                          (shiftedInclusion ℳ d.monoid p
                            ⟨n.val, (d.mem_cutoff.mp
                              ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                            (d.shiftedQuotientComponent ℳ p (p + n.val) k
                              (by simpa only [add_sub_cancel_left] using
                                (d.mem_cutoff.mp
                                  ((d.finite_cutoff k).mem_toFinset.mp n.property)).2)
                              (field k (hBc.mono (Nat.le_succ k)) (z b)))))) := by
  classical
  let := h.finiteDimensional
  obtain ⟨r, hr, hsign, -, hgeneric⟩ :=
    F.exists_norm_lt_forall_eventually_isGeneric v
      (fun c : B.active (k + 1) =>
        (h.realCharacter (B.wall c).normal).toContinuousLinearMap) hs
  simp only [LinearMap.coe_toContinuousLinearMap'] at hsign
  refine ⟨r, hr, hsign, fun x y e a l hl hxy q hq => ?_⟩
  dsimp only
  let g := labels (k + 1) e
  let τ := (orderedCrossingTimes e).reverse
  -- Compare every algebraic suffix input with its perturbed geometric germ.
  have hevent (b : Fin g.length) :
      ∀ᶠ δ : ℝ in 𝓝[>] 0,
        ∃ z : WallComplement (fun c : B.active k => (B.wall c).support),
          z.val = AffineMap.lineMap x.val y.val
            (τ[b.val]'(by simpa only [g, List.length_map] using b.isLt)) + δ • (v a + r) ∧
          F.IsGeneric z.val ∧
          field k (hBc.mono (Nat.le_succ k)) z =
            (A).truncatedBCHAction d ℒ k
              ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (g.drop (b.val + 1)).prod)
              (field k (hBc.mono (Nat.le_succ k)) ((restriction k).obj x)) := by
    have hb : b.val < (orderedCrossingTimes e).length := by
      simpa only [g, List.length_map, List.length_reverse] using b.isLt
    have hbτ : b.val < τ.length := by simpa only [τ, List.length_reverse] using hb
    have hτ := mem_Ioo_of_mem_orderedCrossingTimes e
      (List.mem_reverse.mp (List.getElem_mem hbτ))
    filter_upwards [eventually_exists_extendedCoefficientField_eq_eventInput_of_mul_pos
      d ℳ p ℒ H h h' D B
      (Nat.le_succ k) (hBc.mono (Nat.le_succ k)) e (v a) (v a + r) hl hxy
      ⟨b.val, hb⟩ (fun c hc => by
        have ht := e.down.transverse
          ⟨c.val, B.active_mono (Nat.le_succ k) c.property⟩
          ⟨τ[b.val], Ioo_subset_Icc_self hτ, hc⟩
        have hv : h.realCharacter (B.wall c).normal (v a) ≠ 0 := by
          rw [(B.wall c).direction_support, LinearMap.mem_ker] at ht
          intro hz
          exact ht (by rw [← neg_sub, hxy]; simp [hz])
        simpa only [mul_comm] using
          hsign a ⟨c.val, B.active_mono (Nat.le_succ k) c.property⟩ hv),
      hgeneric (AffineMap.lineMap x.val y.val
        (τ[b.val]'(by simpa only [g, List.length_map] using b.isLt)))] with δ hi hgen
    obtain ⟨z, hz, he⟩ := hi
    exact ⟨z, hz, by simpa only [hz, vadd_eq_add, add_comm] using hgen a, he⟩
  -- Finitely many events admit one common positive displacement bound.
  filter_upwards [eventually_all.mpr hevent] with δ hδ
  choose z hz hgen he using hδ
  refine ⟨z, fun b => ⟨hz b, hgen b⟩, ?_⟩
  rw [shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_crossings
    d ℳ p ℒ H h h' D B k hBc hD hB e q hq]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [← he b]

end Mei.ModuleProbe
