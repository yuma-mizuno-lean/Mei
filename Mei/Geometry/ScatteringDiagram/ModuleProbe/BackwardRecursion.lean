/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.IncomingSegment
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.GenericRecursion

/-!
# The probe recursion along complete backward rays

At a generic endpoint, the probe component of positive relative degree is the
sum of the crossing contributions on its backward ray. A sufficiently long
admissible segment contains every encounter on that half-ray and starts where
the component has its prescribed incoming value, which is zero in positive
relative degree. Each contribution reads whole coefficients at the preceding
cutoff, at generic incoming points arbitrarily close to its simultaneous event.
One arbitrarily small perturbation works for all endpoints, all retained degrees
and all sufficiently long segments, for any prescribed exceptional refinement.

The finite arrangement works simultaneously for every degree of a given order.
Coincident indexed walls remain one combined event, and no commutation between
different events is assumed. Zero spatial directions and empty event lists are
included. Only additional probe walls carrying the component in question must
be outgoing.

We assemble `ModuleProbe.exists_incomingSegmentArrangement` and
`ModuleProbe.exists_norm_lt_forall_eventually_extendedCoefficientField_eq_add_sum_genericInputs`.
The backward-ray recursion follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
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

/-- One arrangement gives the positive-degree backward-ray recursion for every
retained degree of order `k + 1`. All sufficiently long segments contain every
backward encounter: the entire ray beyond their starting point misses all active
walls. At every sufficiently small common positive displacement, the finite sum
reads lower-order probe values at incoming germs generic for the prescribed
arrangement. One arbitrarily small perturbation works for all these rays.

The output degree is `p + n`; the sum uses relative input degrees at most `k`.
The crossing list is in multiplication order, with the first crossing rightmost.
No nonzero spatial direction or coefficient-basis hypothesis is required. -/
theorem exists_backwardRayRecursionArrangement
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (hout : ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
      ∀ b, Sum.inr b ∈ D.active (k + 2) →
        (p + n.val, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees →
          (D.wall (.inr b)).Outgoing)
    (F : ExceptionalArrangement V) {s : ℝ} (hs : 0 < s) :
    ∃ (E : ExceptionalArrangement V) (r : V), ‖r‖ < s ∧
      (∀ (n : d.cutoff (k + 1)) (c : B.active (k + 1)),
        h.realCharacter (B.wall c).normal (i (ρ (p + n.val))) ≠ 0 →
          0 < h.realCharacter (B.wall c).normal (i (ρ (p + n.val)) + r) *
            h.realCharacter (B.wall c).normal (i (ρ (p + n.val)))) ∧
      ∀ Q, E.IsGeneric Q →
      ∃ y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
        y.val = Q ∧ ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
          ∀ᶠ T : ℝ in atTop, 0 < T ∧
            (∀ s ≥ T, ∀ c : B.active (k + 1),
              Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
            ∃ (x : WallComplement (fun c : B.active (k + 1) => (B.wall c).support))
              (e : x ⟶ y), x.val = Q + T • i (ρ (p + n.val)) ∧
              let τ := (orderedCrossingTimes e).reverse
              let g := labels (k + 1) e
              ∀ᶠ δ : ℝ in 𝓝[>] 0,
                ∃ z : Fin g.length →
                    WallComplement (fun c : B.active k => (B.wall c).support),
                  (∀ j : Fin g.length,
                    (z j).val = Q + ((1 - τ[j.val]'(by
                      simpa only [g, List.length_map] using j.isLt)) * T) •
                        i (ρ (p + n.val)) + δ • (i (ρ (p + n.val)) + r) ∧
                      F.IsGeneric (z j).val) ∧
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
                                  (z j)))))) := by
  classical
  obtain ⟨E, hE⟩ := exists_incomingSegmentArrangement
    d ℳ p ℒ H h h' D₀ a D B hinitial (k + 1) hD hBc hB
  obtain ⟨r, hr, hsign, hrec⟩ :=
    exists_norm_lt_forall_eventually_extendedCoefficientField_eq_add_sum_genericInputs
      d ℳ p ℒ H h h' D B k hBc hD hB F
      (fun n : d.cutoff (k + 1) => i (ρ (p + n.val))) hs
  refine ⟨E, r, hr, hsign, fun Q hQ => ?_⟩
  obtain ⟨y, hy, hsegment⟩ := hE Q hQ
  refine ⟨y, hy, fun n hn => ?_⟩
  have hq : d.degree ((p + n.val) - p) = k + 1 := by
    simpa only [add_sub_cancel_left] using hn
  have hne : p ≠ p + n.val := by
    intro he
    rw [← he, sub_self, map_zero] at hq
    omega
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsegment n (hout n hn)] with T hT hseg
  obtain ⟨htail, x, e, hx, hvalue⟩ := hseg
  -- The distant initial component vanishes because the output has positive relative degree.
  have hzero : d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1) (by omega)
      (field (k + 1) hBc x) = 0 :=
    hvalue.trans (Subtype.ext (DirectSum.decompose_of_mem_ne ℳ a.property hne))
  refine ⟨hT, htail, x, e, hx, ?_⟩
  dsimp only
  have hxy : x.val - y.val = T • i (ρ (p + n.val)) := by rw [hx, hy]; module
  filter_upwards [hrec x y e n T hT hxy (p + n.val) hq] with δ hδ
  obtain ⟨z, hz, hsum⟩ := hδ
  refine ⟨z, fun j => ⟨?_, (hz j).2⟩, ?_⟩
  · rw [(hz j).1, hx, hy, AffineMap.lineMap_apply_module']
    module
  · simpa only [hzero, zero_add] using hsum

end Mei.ModuleProbe
