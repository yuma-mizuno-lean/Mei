/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block

/-!
# Probe recursions at straight incoming cuts

The independent probe recurrence reads the same straight incoming cuts as
weighted decorated rays. At every simultaneous event, each retained input degree
uses its own spatial direction. Normal-velocity conservation removes incompatible
blocks. One exceptional arrangement makes all compatible cuts generic for any
prescribed finite arrangement, with a common sufficiently small displacement.

The resulting component equation uses `eventEndpointStep` and any extension of
the preceding-cutoff probe components to endpoint functions. Values outside the
allowed locus do not enter the equation. Specializing to complete backward
segments allows the far-ray condition to remove the initial positive-degree term.

We reuse `exists_straightEventInputArrangement`, the finite segment correction
sum, and normal-velocity preservation of canonical wall events. The interpretation
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

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
    (B.activeLabels_commute k) e) (List.reverse (orderedCrossingTimes e)))

local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)

/-- One endpoint arrangement makes the independent probe jump equal the event
endpoint step at straight generic incoming cuts. The endpoint function may be any
extension of the actual preceding-cutoff components. The formula holds for every
sufficiently small common displacement and every admissible segment in a highest
retained degree's direction. -/
theorem exists_straightProbeStepArrangement
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (F : ExceptionalArrangement V) :
    ∃ G : ExceptionalArrangement V,
      ∀ (x y : WallComplement (B.activeSupport (k + 1))), G.IsGeneric y.val →
        ∀ (e : x ⟶ y) (n : d.cutoff (k + 1)), d.degree n.val = k + 1 →
          ∀ T : ℝ, 0 < T → x.val - y.val = T • i (ρ (p + n.val)) →
          ∀ f : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1),
            (∀ (z : WallComplement (B.activeSupport k)) (m : d.cutoff k),
              let m' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
                ⟨(d.mem_cutoff.mp m.property).1,
                  (d.mem_cutoff.mp m.property).2.trans
                    (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
              f z.val m' = (component k m) (field k (hBc.mono (Nat.le_succ k)) z)) →
          ∀ᶠ δ : ℝ in 𝓝[>] 0,
            (∀ b ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
              ∀ m : d.cutoff (k + 1),
                b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
                  b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
                F.IsGeneric (y.val +
                  segmentEventParameter (B.activeNormal (k + 1)) e T b •
                    i (ρ (p + n.val)) + δ • i (ρ (p + m.val)))) ∧
            (component (k + 1) n) (field (k + 1) hBc y) =
              (component (k + 1) n) (field (k + 1) hBc x) +
                eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
                  (fun _ _ => segmentWallEvents (B.activeNormal (k + 1)) e)
                  (fun b X r m => X +
                    segmentEventParameter (B.activeNormal (k + 1)) e T b •
                      i (ρ (p + r.val)) + δ • i (ρ (p + m.val))) f y.val n := by
  classical
  obtain ⟨G, hG⟩ := exists_straightEventInputArrangement d ℳ p ℒ H h h' D B
    (Nat.le_succ k) (hBc.mono (Nat.le_succ k)) F
    (fun n : d.cutoff (k + 1) => i (ρ (p + n.val)))
    (fun n : d.cutoff (k + 1) => i (ρ (p + n.val)))
  refine ⟨G, fun x y hy e n hn T hT hxy f hf => ?_⟩
  let τ := (orderedCrossingTimes e).reverse
  let g := labels (k + 1) e
  let event (b : Fin g.length) := crossingWallEvent (B.activeNormal (k + 1)) e
    (τ[b.val]'(by simpa only [g, List.length_map] using b.isLt))
    (List.mem_reverse.mp (List.getElem_mem (by
      simpa only [g, List.length_map] using b.isLt)))
  have hline (b : Fin g.length) :
      AffineMap.lineMap x.val y.val (τ[b.val]'(by simpa only [g, List.length_map] using b.isLt)) =
        y.val + segmentEventParameter (B.activeNormal (k + 1)) e T (event b) •
          i (ρ (p + n.val)) := by
    rw [lineMap_eq_add_smul hxy, segmentEventParameter_of_mem]
  -- Equality for the representative normal implies equality for every
  -- incident normal, since regular incident walls have the same kernel.
  have hsign (b : Fin g.length) (m : d.cutoff (k + 1))
      (hv : (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
        (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))))
      (c : B.active (k + 1))
      (hc : AffineMap.lineMap x.val y.val
        (τ[b.val]'(by simpa only [g, List.length_map] using b.isLt)) ∈ (B.wall c).support) :
      0 < h.realCharacter (B.wall c).normal (i (ρ (p + n.val))) *
        h.realCharacter (B.wall c).normal (i (ρ (p + m.val))) := by
    have htmem : τ[b.val]'(by simpa only [g, List.length_map] using b.isLt) ∈
        orderedCrossingTimes e := List.mem_reverse.mp (List.getElem_mem (by
          simpa only [g, List.length_map] using b.isLt))
    have ht := mem_Ioo_of_mem_orderedCrossingTimes e htmem
    have hker := B.ker_normal_eq_of_mem_support
      (e.down.regular _ (Ioo_subset_Icc_self ht))
      (mem_chosenWall_crossingWallEvent (B.activeNormal (k + 1)) e _ htmem) hc
    have heq : h.realCharacter (B.wall c).normal (i (ρ (p + n.val))) =
        h.realCharacter (B.wall c).normal (i (ρ (p + m.val))) := by
      apply sub_eq_zero.mp
      rw [← map_sub, ← LinearMap.mem_ker, ← hker, LinearMap.mem_ker, map_sub]
      simpa only [event, WallEvent.normal_def, B.activeNormal_apply,
        h.continuousRealCharacter_apply, sub_eq_zero] using hv
    have htrans := e.down.transverse c ⟨_, Ioo_subset_Icc_self ht, hc⟩
    rw [(B.wall c).direction_support, LinearMap.mem_ker] at htrans
    have hvn : h.realCharacter (B.wall c).normal (i (ρ (p + n.val))) ≠ 0 := by
      intro hz
      exact htrans (by rw [← neg_sub, hxy, map_neg, map_smul, hz]; simp only [smul_zero, neg_zero])
    rw [← heq]
    exact mul_self_pos.mpr hvn
  filter_upwards [hG x y hy e n T hT hxy] with δ hδ
  have hinput (b : Fin g.length) (m : d.cutoff (k + 1))
      (hv : (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
        (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + m.val)))) :=
    hδ b m (hsign b m hv)
  refine ⟨?_, ?_⟩
  · intro b hb m hv
    obtain ⟨t, ht, rfl⟩ := (mem_segmentWallEvents_iff (B.activeNormal (k + 1)) e b).mp hb
    obtain ⟨j, hj, hjt⟩ := List.mem_iff_getElem.mp (List.mem_reverse.mpr ht)
    let b : Fin g.length := ⟨j, by simpa only [g, List.length_map] using hj⟩
    have hevent : event b = crossingWallEvent (B.activeNormal (k + 1)) e t ht := by
      simp only [event, b, τ, hjt]
    obtain ⟨z, hz, hgen, -⟩ := hinput b m (hevent ▸ hv)
    rw [hline b, hevent] at hz
    exact hz ▸ hgen
  · rw [eventEndpointStep_apply_sum_cutoff d ℳ p ℒ H h B k (k + 1) (Nat.le_refl _)
      _ _ f y.val n,
      sum_segmentWallEvents]
    have hsum := shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_crossings
      d ℳ p ℒ H h h' D B k hBc hD hB e (p + n.val)
      (by simpa only [add_sub_cancel_left] using hn)
    dsimp only at hsum
    rw [hsum]
    congr 1
    -- Both lists enumerate the same reversed crossing times.
    refine Fintype.sum_equiv (finCongr (by
      simp only [List.length_map, List.length_reverse])) _ _ ?_
    intro b
    rw [← Finset.sum_coe_sort_eq_attach]
    refine Fintype.sum_equiv (d.finite_cutoff k).subtypeEquivToFinset.symm _ _ ?_
    intro m
    let m' : d.cutoff k := ⟨m.val, (d.finite_cutoff k).mem_toFinset.mp m.property⟩
    let m'' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
      ⟨(d.mem_cutoff.mp m'.property).1,
        (d.mem_cutoff.mp m'.property).2.trans (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
    have hmn : m.val ≠ n.val := by
      have hmdeg := (d.mem_cutoff.mp m'.property).2
      intro he
      rw [he, hn] at hmdeg
      omega
    have htmem : τ[b.val]'(by simpa only [g, List.length_map] using b.isLt) ∈
        orderedCrossingTimes e := List.mem_reverse.mp (List.getElem_mem (by
          simpa only [g, List.length_map] using b.isLt))
    have hlabel : g[b] = B.wallEventLabel (k + 1) (event b) := by
      refine (List.getElem_map _).trans ?_
      exact B.crossingEventProduct_eq_wallEventLabel (k + 1) e
        (Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e htmem)) _
        ((WallEvent.mem_support _ _ _).mpr fun c => mem_crossingWallEvent _ e _ htmem c)
        (normal_sign_crossingWallEvent _ e _ htmem)
    rw [hlabel]
    have hblock := eventBlock_apply_of_ne d ℳ p ℒ H h B
      (k + 1) (k + 1) (Nat.le_refl _) (event b) n m'' hmn
    simp only [d.truncationMap_refl, LieHom.bchGroupMap_id, MonoidHom.id_apply] at hblock
    rw [← hblock]
    let input := (A).truncatedBCHAction d ℒ k
      ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap (g.drop (b.val + 1)).prod)
      (field k (hBc.mono (Nat.le_succ k))
        ((WallComplement.restrictPrefunctor (B.activeSupport (k + 1))
          (Set.inclusion (B.active_mono (Nat.le_succ k)))).obj x))
    -- Reindexing has inserted cutoff and crossing-time casts. Their values
    -- agree; their membership proofs agree by proof irrelevance.
    change eventBlock d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
        (event b) n m'' ((component k m') input) =
      (if (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
          (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) then
        eventBlock d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _) (event b) n m''
      else 0) (f (y.val + segmentEventParameter (B.activeNormal (k + 1)) e T
        (event b) • i (ρ (p + n.val)) + δ • i (ρ (p + m.val))) m'')
    by_cases hv : (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
        (event b).normal (B.activeNormal (k + 1)) (i (ρ (p + m.val)))
    · obtain ⟨z, hz, -, he⟩ := hinput b m'' hv
      have hz' : z.val = y.val +
          segmentEventParameter (B.activeNormal (k + 1)) e T (event b) •
            i (ρ (p + n.val)) + δ • i (ρ (p + m.val)) := by rw [hz, hline b]
      have he' : field k (hBc.mono (Nat.le_succ k)) z = input := he
      rw [ite_eq_left hv, ← he', ← hf z m', hz']
    · rw [ite_eq_right hv, eventBlock_eq_zero_of_normal_ne d ℳ p ℒ H h B
        (k + 1) (k + 1) (Nat.le_refl _) (event b) n m'' hv]
      rfl

end Mei.ModuleProbe
