/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Recursion
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Wall-event recursions with generic incoming coefficients

For any prescribed exceptional arrangement, refine the outgoing endpoint
exceptions so that the actual wall-event recurrence reads only generic straight
incoming points. Each event uses one displacement for all retained incoming
degrees with the same normal velocity, including zero coefficient terms. The
refinement works for all output degrees and complete backward segments and is
independent of the incoming coefficient and source cell.

The resulting formula uses the canonical `eventEndpointStep` blocks. It retains
whole simultaneous events and the original incoming histories. It concerns
positive relative degrees; the source component and the assembly of the global
endpoint equation are separate statements.

We use `exists_cutoffWallEventEvaluation_eq_sum_eventBlock`, the backward-segment
admissibility arrangement, and `exists_forall_eventually_isGeneric_sweepProjection`.
The backward-ray interpretation follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V ι : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H ι)

local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)
local notation "evaluation" k:max a:max C:max Q:max =>
  cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) a C Q

open Classical in
/-- Refine endpoint exceptions so every complete backward segment gives the
positive-degree event-block recurrence with generic incoming read points for a
prescribed arrangement. Each event has one arbitrarily small displacement that
works for every retained degree with matching normal velocity. -/
theorem exists_cutoffWallEventEvaluation_eq_sum_eventBlock_generic
    (k : ℕ) (A : ExceptionalArrangement V) :
    ∃ F : ExceptionalArrangement V,
      ∀ (n : d.cutoff (k + 1)), n.val ≠ 0 →
        ∀ {x y : WallComplement (B.activeSupport (k + 1))}, F.IsGeneric y.val →
          ∀ (e : x ⟶ y) (T : ℝ), 0 < T →
            x.val - y.val = T • i (ρ (p + n.val)) →
            (∀ s ≥ T, ∀ c : B.active (k + 1),
              y.val + s • i (ρ (p + n.val)) ∉ (B.wall c).support) →
            ∀ (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V),
              ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
                (∀ b ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
                  0 < η b ∧ η b < θ ∧
                  ∀ m : d.cutoff (k + 1),
                    b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
                        b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
                      A.IsGeneric (y.val +
                        segmentEventParameter (B.activeNormal (k + 1)) e T b •
                          i (ρ (p + n.val)) + η b • i (ρ (p + m.val)))) ∧
                (component (k + 1) n) (evaluation (k + 1) a C y.val) =
                  ∑ b ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
                    ∑ m : d.cutoff (k + 1),
                      if _hmn : d.Precedes m.val n.val then
                        if b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
                            b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) then
                          eventBlock d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _) b n m
                            ((component (k + 1) m) (evaluation (k + 1) a C
                              (y.val + segmentEventParameter (B.activeNormal (k + 1)) e T b •
                                i (ρ (p + n.val)) + η b • i (ρ (p + m.val)))))
                        else 0
                      else 0 := by
  classical
  let Z := {z : WallEvent (B.active (k + 1)) × d.cutoff (k + 1) × d.cutoff (k + 1) //
    z.1.normal (B.activeNormal (k + 1)) (i (ρ (p + z.2.2.val))) ≠ 0}
  obtain ⟨F, hF⟩ := exists_forall_eventually_isGeneric_sweepProjection A
    (fun z : Z => z.val.1.normal (B.activeNormal (k + 1)))
    (fun z => z.val.1.offset (B.activeOffset (k + 1)))
    (fun z => (z.val.1.normal (B.activeNormal (k + 1))
      (i (ρ (p + z.val.2.1.val))))⁻¹ • i (ρ (p + z.val.2.1.val)))
    (fun z => i (ρ (p + z.val.2.2.val))) (fun z => z.property)
  refine ⟨F, fun n hn x y hy e T hT hxy htail a C θ hθ => ?_⟩
  -- Shrink the existing recurrence's displacement bound; every smaller positive
  -- choice is generic simultaneously for the finite normal/direction inventory.
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hF y.val hy)
  obtain ⟨η, hη, hrec⟩ := exists_cutoffWallEventEvaluation_eq_sum_eventBlock
    d ℳ p ℒ H h B k a C n hn e T hT hxy htail (min θ δ) (lt_min hθ hδ)
  refine ⟨η, fun b hb => ⟨(hη b hb).1, lt_of_lt_of_le (hη b hb).2 (min_le_left _ _),
    fun m hnormal => ?_⟩, hrec⟩
  obtain ⟨t, ht, rfl⟩ := (mem_segmentWallEvents_iff (B.activeNormal (k + 1)) e b).mp hb
  let b := crossingWallEvent (B.activeNormal (k + 1)) e t ht
  -- Admissibility makes the outgoing normal velocity nonzero, and matching
  -- velocities give the incoming transversality required by the arrangement.
  have hmem := mem_chosenWall_crossingWallEvent (B.activeNormal (k + 1)) e t ht
  have hdir := e.down.transverse b.1.property.choose
    ⟨t, Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e ht), hmem⟩
  rw [(B.wall b.1.property.choose).direction_support, LinearMap.mem_ker] at hdir
  have hv : b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) ≠ 0 := by
    intro hz
    apply hdir
    have hyx : y.val - x.val = -T • i (ρ (p + n.val)) := by
      rw [← neg_sub, hxy, neg_smul]
    simpa only [WallEvent.normal_def, B.activeNormal_apply,
      h.continuousRealCharacter_apply, hyx, map_smul, smul_zero] using
      congrArg (fun u : ℝ => (-T) • u) hz
  have hw : b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) ≠ 0 :=
    hnormal ▸ hv
  let z : Z := ⟨(b, n, m), hw⟩
  -- The actual event point is the normalized sweep projection of the endpoint.
  have hline : AffineMap.lineMap x.val y.val t = y.val +
      segmentEventParameter (B.activeNormal (k + 1)) e T b • i (ρ (p + n.val)) := by
    rw [lineMap_eq_add_smul (t := t) hxy, segmentEventParameter_of_mem]
  have hheight : b.normal (B.activeNormal (k + 1))
      (y.val + segmentEventParameter (B.activeNormal (k + 1)) e T b •
        i (ρ (p + n.val))) = b.offset (B.activeOffset (k + 1)) := by
    rw [← hline, WallEvent.normal_def, WallEvent.offset_def]
    exact (B.wall b.1.property.choose).offset_eq hmem
  have htime : (b.offset (B.activeOffset (k + 1)) -
      b.normal (B.activeNormal (k + 1)) y.val) /
        b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
          segmentEventParameter (B.activeNormal (k + 1)) e T b := by
    apply (div_eq_iff hv).mpr
    rw [map_add, map_smul, smul_eq_mul] at hheight
    linarith
  have hgen := hsmall ⟨(hη b hb).1,
    lt_of_lt_of_le (hη b hb).2 (min_le_right _ _)⟩ z
  simpa only [z, sweepProjection_apply, smul_smul, ← div_eq_mul_inv, htime] using hgen

open Classical in
/-- One refinement gives complete backward segments and the actual event
endpoint-step formula in every positive relative degree, with all compatible
incoming points generic for the prescribed arrangement. The refinement and
segments are chosen before the coefficient and source cell. -/
theorem exists_wallEventRecursionArrangement_generic (k : ℕ) (A : ExceptionalArrangement V) :
    ∃ E : ExceptionalArrangement V, ∀ Q, E.IsGeneric Q →
      ∃ y : WallComplement (B.activeSupport (k + 1)), y.val = Q ∧
        ∀ n : d.cutoff (k + 1), n.val ≠ 0 → ∀ᶠ T : ℝ in atTop,
          0 < T ∧
          (∀ s ≥ T, ∀ c : B.active (k + 1),
            Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
          ∃ (x : WallComplement (B.activeSupport (k + 1))) (e : x ⟶ y),
            x.val = Q + T • i (ρ (p + n.val)) ∧
            ∀ (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V),
              ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
                (∀ b ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
                  0 < η b ∧ η b < θ ∧
                  ∀ m : d.cutoff (k + 1),
                    b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
                        b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
                      A.IsGeneric (Q +
                        segmentEventParameter (B.activeNormal (k + 1)) e T b •
                          i (ρ (p + n.val)) + η b • i (ρ (p + m.val)))) ∧
                (component (k + 1) n) (evaluation (k + 1) a C Q) =
                  eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
                    (fun _ _ => segmentWallEvents (B.activeNormal (k + 1)) e)
                    (fun b X r m => X +
                      segmentEventParameter (B.activeNormal (k + 1)) e T b •
                        i (ρ (p + r.val)) + η b • i (ρ (p + m.val)))
                    (fun X m => (component (k + 1) m) (evaluation (k + 1) a C X)) Q n := by
  classical
  let := h.finiteDimensional
  let vectors := (d.finite_cutoff (k + 1)).toFinset.image (fun n => i (ρ (p + n)))
  obtain ⟨E, hE⟩ := exists_ray_admissibilityArrangement
    (B.activeSupport (k + 1)) (fun c => (B.wall c).isConvexPolyhedron)
    (fun c => (B.wall c).finrank_direction_add_one) vectors
  obtain ⟨F, hF⟩ := exists_cutoffWallEventEvaluation_eq_sum_eventBlock_generic
    d ℳ p ℒ H h B k A
  refine ⟨E.union F, fun Q hQ => ?_⟩
  obtain ⟨hQE, hQF⟩ := ExceptionalArrangement.isGeneric_union.mp hQ
  obtain ⟨y, hy, hsegment⟩ := hE Q hQE
  refine ⟨y, hy, fun n hn => ?_⟩
  have hnmem : i (ρ (p + n.val)) ∈ vectors :=
    Finset.mem_image.mpr ⟨n.val, (d.finite_cutoff (k + 1)).mem_toFinset.mpr n.property, rfl⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsegment _ hnmem] with T hT hs
  obtain ⟨ht, x, hx, he⟩ := hs
  let e : x ⟶ y := ⟨he⟩
  refine ⟨hT, ht, x, e, hx, fun a C θ hθ => ?_⟩
  have hxy : x.val - y.val = T • i (ρ (p + n.val)) := by rw [hx, hy]; module
  obtain ⟨η, hη, hrec⟩ := hF n hn (by rwa [hy]) e T hT hxy
    (by simpa only [hy] using ht) a C θ hθ
  refine ⟨η, by simpa only [hy] using hη, ?_⟩
  rw [eventEndpointStep_apply, ← hy, hrec]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> rfl

end Mei.ModuleProbe
