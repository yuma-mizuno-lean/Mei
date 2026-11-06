/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block

/-!
# The broken-line recursion in event blocks

The positive relative-degree components of actual simultaneous-event weighted
ray evaluations satisfy the finite backward recurrence in the blocks used by
`eventEndpointStep`. Each term reads the whole lower-degree component at an
arbitrarily close incoming germ. The event inventory comes from an admissible
segment containing every encounter of the backward half-line.

One exceptional arrangement supplies such segments for all retained relative
degrees. The source cell remains arbitrary: its incoming-tail condition stays
in the evaluated ray fibers. The recurrence does not replace these fibers by
unrestricted operator words, and retains degree changes of zero spatial shift.
The incoming germs are not asserted to avoid an auxiliary arrangement.

We apply `exists_decompose_cutoffWallEventEvaluation_eq_sum_lastChange` and
`PositiveDegrees.labelBlock_apply_component`. The backward-ray interpretation
follows Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
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
/-- The actual weighted evaluation satisfies the positive-degree backward
recurrence in the event operator's blocks. Every event of the whole backward
ray must lie on the supplied admissible segment. The incoming displacements
can be arbitrarily small, and no coefficient injectivity or genericity of the
incoming germs is assumed. -/
theorem exists_cutoffWallEventEvaluation_eq_sum_eventBlock (k : ℕ)
    (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V)
    (n : d.cutoff (k + 1)) (hn0 : n.val ≠ 0)
    {x y : WallComplement (B.activeSupport (k + 1))} (e : x ⟶ y)
    (T : ℝ) (hT : 0 < T) (hxy : x.val - y.val = T • i (ρ (p + n.val)))
    (htail : ∀ s ≥ T, ∀ c : B.active (k + 1),
      y.val + s • i (ρ (p + n.val)) ∉ (B.wall c).support) :
    ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
      (∀ b ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
        0 < η b ∧ η b < θ) ∧
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
  intro θ hθ
  obtain ⟨η, hη, heq⟩ := exists_decompose_cutoffWallEventEvaluation_eq_sum_lastChange
    d ℳ p ℒ H h B k a C e T hT hxy htail n.property hn0 θ hθ
  refine ⟨η, hη, ?_⟩
  have he := congrArg (component (k + 1) n) heq
  rw [d.shiftedQuotientComponent_decompose_same ℳ p (k + 1)
    ⟨n.val, (d.mem_cutoff.mp n.property).1⟩ (d.mem_cutoff.mp n.property).2] at he
  simp only [map_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_filter]
  rw [Finset.sum_subtype (d.finite_cutoff (k + 1)).toFinset
    (fun m => (d.finite_cutoff (k + 1)).mem_toFinset)]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmn : d.Precedes m.val n.val
  · by_cases hv : b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
        b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val)))
    · rw [ite_eq_left ⟨(d.precedes_iff.mp hmn).1, (d.precedes_iff.mp hmn).2, hv⟩,
        dite_eq_left hmn, ite_eq_left hv]
      rw [d.shiftedQuotientComponent_decompose_same ℳ p (k + 1)
        ⟨n.val, (d.mem_cutoff.mp n.property).1⟩ (d.mem_cutoff.mp n.property).2]
      rw [eventBlock_def, PositiveDegrees.labelBlock_apply_component d ℳ p ℒ (k + 1) _ n m
        (d.precedes_iff.mp hmn).1, wallEventPropagation_def,
        d.truncationMap_refl, LieHom.bchGroupMap_id, MonoidHom.id_apply]
      rfl
    · rw [ite_eq_right (fun h => hv h.2.2), dite_eq_left hmn, ite_eq_right hv]
  · have hnot : ¬ (m.val ≠ n.val ∧ n.val - m.val ∈ d.monoid) := by
      simpa only [← d.precedes_iff] using hmn
    simp only [hmn, ↓reduceDIte]
    rw [ite_eq_right (fun h => hnot ⟨h.1, h.2.1⟩)]

open Classical in
/-- One exceptional arrangement makes the actual ray sums satisfy the event
endpoint step in every nonzero retained relative degree. All sufficiently long
backward segments give this formula, with arbitrarily close incoming germs.
The arrangement and the segments are independent of the incoming coefficient
and source cell. The event inventory in this local step is the inventory of
the supplied complete segment; the assertion concerns its specified output
degree at its final endpoint. -/
theorem exists_wallEventRecursionArrangement (k : ℕ) :
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
                  0 < η b ∧ η b < θ) ∧
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
  refine ⟨E, fun Q hQ => ?_⟩
  obtain ⟨y, hy, hsegment⟩ := hE Q hQ
  refine ⟨y, hy, fun n hn => ?_⟩
  have hnmem : i (ρ (p + n.val)) ∈ vectors :=
    Finset.mem_image.mpr ⟨n.val, (d.finite_cutoff (k + 1)).mem_toFinset.mpr n.property, rfl⟩
  have htail : ∀ᶠ T : ℝ in atTop, ∀ s ≥ T, ∀ c : B.active (k + 1),
      Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support :=
    (eventually_forall_ge_atTop.mpr (hsegment _ hnmem)).mono fun T hT s hs c hmem => by
      obtain ⟨x, hx, _⟩ := hT s hs
      exact x.notMem c (hx ▸ hmem)
  filter_upwards [eventually_gt_atTop (0 : ℝ), htail, hsegment _ hnmem] with T hT ht hs
  obtain ⟨x, hx, he⟩ := hs
  let e : x ⟶ y := ⟨he⟩
  refine ⟨hT, ht, x, e, hx, fun a C θ hθ => ?_⟩
  have hxy : x.val - y.val = T • i (ρ (p + n.val)) := by rw [hx, hy]; module
  obtain ⟨η, hη, hrec⟩ := exists_cutoffWallEventEvaluation_eq_sum_eventBlock
    d ℳ p ℒ H h B k a C n hn e T hT hxy (by simpa only [hy] using ht) θ hθ
  refine ⟨η, hη, ?_⟩
  rw [eventEndpointStep_apply, ← hy, hrec]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> rfl

end Mei.ModuleProbe
