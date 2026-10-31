/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.IncomingSegment
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.EventInput

/-!
# Backward-ray recursion for probe coefficients

A positive relative-degree component of the probe field is a finite sum of
signed crossing actions on strictly lower-degree incoming components. The sum
uses the actual simultaneous events on a sufficiently long backward segment in
the outgoing degree's spatial direction. The distant initial component vanishes
by the outgoing condition. All incoming values are read arbitrarily close to
their crossing, on its incoming straight germ.

One finite exceptional arrangement and one eventual bound on segment length
work for every retained degree. Coincident indexed walls remain in the combined
event label; changes of coefficient degree with unchanged spatial direction
remain in the lower-degree sum. Spatially stationary degrees are allowed too.

We combine `ModuleProbe.exists_incomingSegmentArrangement`
and `ModuleProbe.exists_shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_eventInputs`.
This is the probe-side recursion in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ κ' : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')

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

/-- Outside one finite arrangement, each positive top-degree probe component is
computed entirely from lower-degree incoming field values at its backward-ray
crossings. The distant endpoint and actual admissible segment exist for every
sufficiently large length, uniformly over the finite degree cutoff. The incoming
points can be chosen within any positive ray-parameter distance of their events.
Only additional active probe walls carrying the top degrees must be outgoing. -/
theorem exists_backwardRecursionArrangement
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hD : D.LevelConsistent (k + 2)) (hBc : B.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (hout : ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 → ∀ b, Sum.inr b ∈ D.active (k + 2) →
      (p + n.val, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees →
        (D.wall (.inr b)).Outgoing) :
    ∃ C : ExceptionalArrangement V, ∀ Q, C.IsGeneric Q →
      ∃ y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
        y.val = Q ∧ ∀ᶠ T : ℝ in atTop, 0 < T ∧
          ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
            ∃ (x : WallComplement (fun c : B.active (k + 1) => (B.wall c).support))
              (e : x ⟶ y), x.val = Q + T • i (ρ (p + n.val)) ∧
              ∀ ε : ℝ, 0 < ε →
                let τ := (orderedCrossingTimes e).reverse
                let g := labels (k + 1) e
                ∃ (s : Fin g.length → ℝ)
                  (z : Fin g.length → WallComplement
                    (fun c : B.active (k + 1) => (B.wall c).support)),
                  (∀ j : Fin g.length, s j ∈ Ioo (0 : ℝ) ε ∧
                    (z j).val = AffineMap.lineMap x.val y.val
                      (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) +
                        s j • i (ρ (p + n.val))) ∧
                  d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1)
                    (by simpa only [add_sub_cancel_left] using
                      (d.mem_cutoff.mp n.property).2) (field (k + 1) hBc y) =
                    ∑ j : Fin g.length, ∑ m ∈ (d.finite_cutoff k).toFinset.attach,
                      d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1)
                        (by simpa only [add_sub_cancel_left] using
                          (d.mem_cutoff.mp n.property).2)
                        ((A).truncatedBCHAction d ℒ (k + 1) g[j]
                          (Submodule.Quotient.mk
                            (shiftedInclusion ℳ d.monoid p
                              ⟨m.val, (d.mem_cutoff.mp
                                ((d.finite_cutoff k).mem_toFinset.mp m.property)).1⟩
                              (d.shiftedQuotientComponent ℳ p (p + m.val) k
                                (by simpa only [add_sub_cancel_left] using
                                  (d.mem_cutoff.mp
                                    ((d.finite_cutoff k).mem_toFinset.mp m.property)).2)
                                (field k (hBc.mono (Nat.le_succ k))
                                  ((restriction k).obj (z j))))))) := by
  classical
  obtain ⟨C, hC⟩ := exists_incomingSegmentArrangement
    d ℳ p ℒ H h h' D₀ a D B hinitial (k + 1) hD hBc hB
    (fun n => d.degree n.val = k + 1) hout
  refine ⟨C, fun Q hQ => ?_⟩
  obtain ⟨y, hy, hsegment⟩ := hC Q hQ
  -- First choose distant incoming segments and coefficients, with a common bound.
  let : Finite (d.cutoff (k + 1)) := (d.finite_cutoff (k + 1)).to_subtype
  refine ⟨y, hy, ?_⟩
  filter_upwards [Filter.eventually_all.mpr
    (fun n => eventually_imp_distrib_left.mpr (hsegment n)), eventually_gt_atTop (0 : ℝ)]
    with T hT hTpos
  refine ⟨hTpos, fun n hn => ?_⟩
  obtain ⟨x, e, hx, hin⟩ := hT n hn
  -- Then expand each crossing using actual lower-degree incoming field values.
  refine ⟨x, e, hx, fun ε hε => ?_⟩
  dsimp only
  let τ := (orderedCrossingTimes e).reverse
  let g := labels (k + 1) e
  have hq : d.degree ((p + n.val) - p) = k + 1 := by simpa using hn
  obtain ⟨t, z, ht, hvalue⟩ :=
    exists_shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_eventInputs
      d ℳ p ℒ H h h' D B k hBc hD hB e (p + n.val) hq (div_pos hε hTpos)
  refine ⟨fun j => T * (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt) - t j),
    z, fun j => ?_, ?_⟩
  · obtain ⟨htj, hnear, hz⟩ := ht j
    refine ⟨⟨mul_pos hTpos (sub_pos.mpr htj.2),
      by nlinarith [(lt_div_iff₀ hTpos).mp hnear]⟩, ?_⟩
    rw [hz, hx, hy]
    simp only [AffineMap.lineMap_apply_module]
    module
  · have hne : p ≠ p + n.val := by
      intro heq
      have hnzero : n.val = 0 := by simpa only [left_eq_add] using heq
      simp only [hnzero, map_zero] at hn
      omega
    have hzero : DirectSum.decompose ℳ (a : M) (p + n.val) = 0 :=
      Subtype.ext (DirectSum.decompose_of_mem_ne ℳ a.property hne)
    rw [hin, hzero, zero_add] at hvalue
    exact hvalue

end Mei.ModuleProbe
