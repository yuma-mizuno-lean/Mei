/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3.1 Pro
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion
public import Mei.Algebra.Lie.Graded.Shifted.Support
public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Recursion
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Linear
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Completion
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.ZeroDirection.Quotient
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallEvent.Action
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.WallEvent.Parameters
public import Mei.Geometry.Convex.Polyhedron.Line
public import Mei.Algebra.Order.Sign
public import Mei.Geometry.Convex.Sweep.Admissible.WallEvent

/-!
# Canonical simultaneous wall-event evaluations

The weighted evaluation of finite decorated-ray itineraries is specialized to
canonical simultaneous events of a directed diagram. Each genuine crossing of
an admissible segment determines one event, retaining every coincident indexed
wall. The degree component at the final endpoint decomposes over those events,
with arbitrarily close incoming germs of strictly lower relative degree;
unchanged-degree encounters do not occur in this decomposition.

The coefficient quotient may have a smaller cutoff than the geometric wall
inventory, and lowering it commutes with the entire weighted evaluation. The
recursion follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  (B : DirectedDiagram (d := d) h H ι)

local notation "A" => d.shiftedLieFiltration ℒ ℳ p

/-- The truncated BCH action of a signed simultaneous event of a directed diagram.
The geometric inventory and the coefficient quotient may use different cutoffs. -/
def wallEventPropagation (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K)) :
    Module.End R ((d.shiftedLieFiltration ℒ ℳ p).quotient k) :=
  ((A).truncatedBCHAction d ℒ k
    ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b))).toLinearMap

omit [IsWallAnnihilating H ℳ] in
@[simp]
theorem wallEventPropagation_apply (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K))
    (z : (d.shiftedLieFiltration ℒ ℳ p).quotient k) :
    wallEventPropagation d ℳ p ℒ H h B k K hkK b z =
      (A).truncatedBCHAction d ℒ k
        ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b)) z := (rfl)

omit [IsWallAnnihilating H ℳ] in
/-- Characterization of simultaneous-event propagation as a whole linear map. -/
theorem wallEventPropagation_def (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K)) :
    wallEventPropagation d ℳ p ℒ H h B k K hkK b =
      ((A).truncatedBCHAction d ℒ k
        ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b))).toLinearMap := (rfl)

omit [IsWallAnnihilating H ℳ] in
/-- With matching geometric and coefficient cutoffs, event propagation is simply the
fixed event's truncated BCH action. -/
theorem wallEventPropagation_self (k : ℕ) (b : WallEvent (B.active k))
    (z : (d.shiftedLieFiltration ℒ ℳ p).quotient k) :
    wallEventPropagation d ℳ p ℒ H h B k k (Nat.le_refl k) b z =
      (A).truncatedBCHAction d ℒ k (B.wallEventLabel k b) z := by
  rw [wallEventPropagation_apply, d.truncationMap_refl, LieHom.bchGroupMap_id,
    MonoidHom.id_apply]

/-- Weighted evaluation of every finite itinerary of canonical simultaneous wall events.
The coefficients live in the same shifted finite quotient as the probe field, while
avoidance and the event alphabet retain the possibly larger geometric cutoff. -/
def cutoffWallEventEvaluation (k K : ℕ) (hkK : k ≤ K)
    (a : (d.shiftedQuotientGrading ℳ p k).piece 0) (C : Set V) (Q : V) :
    (d.shiftedLieFiltration ℒ ℳ p).quotient k :=
  cutoffDecoratedEvaluation d (d.shiftedQuotientGrading ℳ p k).piece
    (fun e : WallEvent (B.active K) => wallEventPropagation d ℳ p ℒ H h B k K hkK e)
    a (fun n => i (ρ (p + n)))
    (fun e => e.normal ((B.activeNormal K)))
    (fun e => e.offset ((B.activeOffset K)))
    (fun e => e.2) (fun e => e.support ((B.activeSupport K)))
    ((B.activeSupport K))
    (fun _ : Unit => singularSupport ((B.activeSupport K))) C k Q

omit [IsWallAnnihilating H ℳ] in
/-- Defining equation for canonical simultaneous-event weighted evaluation. -/
theorem cutoffWallEventEvaluation_def (k K : ℕ) (hkK : k ≤ K)
    (a : (d.shiftedQuotientGrading ℳ p k).piece 0) (C : Set V) (Q : V) :
    cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a C Q =
      cutoffDecoratedEvaluation d (d.shiftedQuotientGrading ℳ p k).piece
        (fun e : WallEvent (B.active K) => wallEventPropagation d ℳ p ℒ H h B k K hkK e)
        a (fun n => i (ρ (p + n)))
        (fun e => e.normal
          ((B.activeNormal K)))
        (fun e => e.offset ((B.activeOffset K)))
        (fun e => e.2)
        (fun e => e.support ((B.activeSupport K)))
        ((B.activeSupport K))
        (fun _ : Unit =>
          singularSupport ((B.activeSupport K))) C k Q := (rfl)

omit [IsWallAnnihilating H ℳ] in
/-- A fixed event preserves a homogeneous component of the current coefficient
quotient when geometric and coefficient cutoffs agree. -/
theorem decompose_wallEventPropagation_self (k : ℕ) (b : WallEvent (B.active k))
    {n : Γ} (z : (d.shiftedLieFiltration ℒ ℳ p).quotient k)
    (hz : z ∈ (d.shiftedQuotientGrading ℳ p k).piece n) :
    (DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece
      (wallEventPropagation d ℳ p ℒ H h B k k (Nat.le_refl k) b z) n :
        (d.shiftedLieFiltration ℒ ℳ p).quotient k) = z := by
  rw [wallEventPropagation_self]
  exact d.decompose_truncatedBCHAction_same ℒ ℳ p k (B.wallEventLabel k b) hz

omit [IsWallAnnihilating H ℳ] in
/-- A genuine crossing gives a positive ray parameter, nonzero transversality,
both signs used by the backward action, the event height, and its precise incident
wall set. The common proof does not depend on weighted evaluation. -/
theorem crossing_event_data (k : ℕ) {n : Γ}
    {x y : WallComplement (B.activeSupport k)}
    (e : x ⟶ y) (T : ℝ) (hTpos : 0 < T)
    (hxy : x.val - y.val = T • i (ρ (p + n)))
    {b : WallEvent (B.active k)} {t : ℝ} (ht : t ∈ orderedCrossingTimes e)
    (hb : b = crossingWallEvent (B.activeNormal k) e t ht) :
    0 < segmentEventParameter (B.activeNormal k) e T b ∧
      (b.normal (B.activeNormal k)) (i (ρ (p + n))) ≠ 0 ∧
      SignType.sign ((b.normal (B.activeNormal k)) (i (ρ (p + n)))) = b.2 ∧
      SignType.sign ((b.normal (B.activeNormal k)) (x.val - y.val)) = b.2 ∧
      (b.normal (B.activeNormal k)) (y.val +
        segmentEventParameter (B.activeNormal k) e T b • i (ρ (p + n))) =
        b.offset (B.activeOffset k) ∧
      y.val + segmentEventParameter (B.activeNormal k) e T b • i (ρ (p + n)) ∈
        b.support (B.activeSupport k) := by
  subst b
  set c := crossingWallEvent (B.activeNormal k) e t ht with hc
  have hs := segmentEventParameter_pos (B.activeNormal k) e T hTpos ht
  have hline : AffineMap.lineMap x.val y.val t = y.val +
      segmentEventParameter (B.activeNormal k) e T
        c • i (ρ (p + n)) := by
    rw [lineMap_eq_add_smul (t := t) hxy, segmentEventParameter_of_mem]
  have hmem : AffineMap.lineMap x.val y.val t ∈
      (B.wall c.1.property.choose).support :=
    mem_chosenWall_crossingWallEvent (B.activeNormal k) e t ht
  have hdir := e.down.transverse
    c.1.property.choose
    ⟨t, Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e ht), hmem⟩
  rw [(B.wall c.1.property.choose).direction_support,
    LinearMap.mem_ker] at hdir
  have htrans : c.normal
      (B.activeNormal k) (y.val - x.val) ≠ 0 := by
    simpa only [B.activeNormal_apply, WallEvent.normal_def,
      h.continuousRealCharacter_apply] using hdir
  have hv : c.normal
      (B.activeNormal k) (i (ρ (p + n))) ≠ 0 := by
    intro hz
    apply htrans
    have hyx : y.val - x.val = (-T) • i (ρ (p + n)) := by
      calc
        y.val - x.val = -(x.val - y.val) := by abel
        _ = -T • i (ρ (p + n)) := by rw [hxy]; module
    simp only [hyx, map_smul, hz, smul_zero]
  have hsign : SignType.sign (c.normal
      (B.activeNormal k) (i (ρ (p + n)))) =
      c.2 := by
    have hn := normal_sign_crossingWallEvent (B.activeNormal k) e t ht
    calc
      SignType.sign (c.normal
        (B.activeNormal k) (i (ρ (p + n)))) =
          SignType.sign (c.normal
            (B.activeNormal k) (x.val - y.val)) := by
        rw [hxy]
        exact (LinearMap.sign_pos_smul (c.normal (B.activeNormal k)).toLinearMap _ hTpos).symm
      _ = _ := by simpa only using hn
  have hinc : y.val + segmentEventParameter (B.activeNormal k) e T
      c • i (ρ (p + n)) ∈
      c.support (B.activeSupport k) := by
    rw [← hline]
    exact (WallEvent.mem_support _ _ _).2 (fun j => by
      simpa only [B.activeSupport_apply] using mem_crossingWallEvent _ e t ht j)
  have hoff := WallEvent.normal_apply_of_mem_support
    c (B.activeSupport k)
    (B.activeNormal k) (B.activeOffset k)
    (fun c z hz => by
      rw [B.activeNormal_apply, B.activeOffset_apply]
      exact (B.wall c).offset_eq hz) hinc
  exact ⟨hs, hv, hsign, (normal_sign_crossingWallEvent (B.activeNormal k) e t ht), hoff,
    hinc⟩

omit [IsWallAnnihilating H ℳ] in
/-- A wall point on a positive interior ray gives the genuine ordered crossing
time at which the ray meets that wall, together with the computed event parameter. -/
private theorem exists_crossingTime_of_pos_of_wall (k : ℕ) {n : Γ}
    {x y : WallComplement (B.activeSupport k)}
    (e : x ⟶ y) {T u : ℝ} (hTpos : 0 < T)
    (hxy : x.val - y.val = T • i (ρ (p + n)))
    (htail : ∀ s ≥ T, ∀ c : B.active k,
      y.val + s • i (ρ (p + n)) ∉ (B.wall c).support)
    (hu : 0 ≤ u) (c : B.active k)
    (hc : y.val + u • i (ρ (p + n)) ∈ B.activeSupport k c) :
    ∃ t : ℝ, ∃ ht : t ∈ orderedCrossingTimes e,
      segmentEventParameter (B.activeNormal k) e T
        (crossingWallEvent (B.activeNormal k) e t ht) = u ∧
      y.val + u • i (ρ (p + n)) = AffineMap.lineMap x.val y.val t := by
  have hu0 : 0 < u := by
    rcases hu.eq_or_lt with rfl | hu
    · exact (y.notMem c (by simpa using hc)).elim
    · exact hu
  have huT : u < T := by
    by_contra hnT
    exact htail u (le_of_not_gt hnT) c hc
  obtain ⟨t, hti, htu, hline⟩ :=
    lineMap_eq_add_smul_of_pos_of_lt (w := i (ρ (p + n))) hTpos hxy hu0 huT
  have ht : t ∈ orderedCrossingTimes e := by
    rw [mem_orderedCrossingTimes]
    exact ⟨c, (mem_crossings x y c t).mpr
      ⟨Set.Ioo_subset_Icc_self hti, by rw [← hline]; exact hc⟩⟩
  exact ⟨t, ht, (segmentEventParameter_of_mem (B.activeNormal k) e T ht).trans htu.symm,
    hline⟩

omit [IsWallAnnihilating H ℳ] in
/-- A supported wall point on the ray, with matching sign, is the canonical
simultaneous event at its genuine crossing time. -/
private theorem eq_crossingWallEvent_of_mem_support_of_sign (k : ℕ) {n : Γ}
    {x y : WallComplement (B.activeSupport k)}
    (e : x ⟶ y) {T u : ℝ} (hTpos : 0 < T)
    (hxy : x.val - y.val = T • i (ρ (p + n)))
    (htail : ∀ s ≥ T, ∀ c : B.active k,
      y.val + s • i (ρ (p + n)) ∉ (B.wall c).support)
    (b : WallEvent (B.active k)) (hu : 0 ≤ u)
    (hsg : SignType.sign (b.normal (B.activeNormal k) (i (ρ (p + n)))) = b.2)
    (hm : y.val + u • i (ρ (p + n)) ∈ b.support (B.activeSupport k)) :
    ∃ t : ℝ, ∃ ht : t ∈ orderedCrossingTimes e,
      b = crossingWallEvent (B.activeNormal k) e t ht ∧
      segmentEventParameter (B.activeNormal k) e T b = u := by
  obtain ⟨c, hc⟩ := b.1.property
  obtain ⟨t, ht, htu, hline⟩ := exists_crossingTime_of_pos_of_wall d p ℒ H h B k
    (c := b.1.property.choose) e hTpos hxy htail hu
      (b.support_subset (B.activeSupport k) b.1.property.choose_spec hm)
  have hmem : ∀ c : B.active k,
      AffineMap.lineMap x.val y.val t ∈ B.activeSupport k c ↔ c ∈ b.1.val := by
    intro c
    rw [← hline]
    exact (WallEvent.mem_support b (B.activeSupport k) _).mp hm c
  have hbeq : b = crossingWallEvent (B.activeNormal k) e t ht :=
    WallEvent.eq_of_mem_support_of_normal_sign_eq
      (x := AffineMap.lineMap x.val y.val t)
      b (crossingWallEvent (B.activeNormal k) e t ht) (B.activeSupport k)
      (B.activeNormal k) (x.val - y.val)
      ((WallEvent.mem_support b (B.activeSupport k) _).2 (fun c => hmem c))
      ((WallEvent.mem_support _ (B.activeSupport k) _).2 (fun c =>
        mem_crossingWallEvent _ e t ht c))
      (by
        calc
          SignType.sign (b.normal (B.activeNormal k) (x.val - y.val)) =
              SignType.sign (b.normal (B.activeNormal k) (i (ρ (p + n)))) := by
            rw [hxy]
            exact LinearMap.sign_pos_smul (b.normal (B.activeNormal k)).toLinearMap _ hTpos
          _ = b.2 := hsg)
      (normal_sign_crossingWallEvent _ e t ht)
  exact ⟨t, ht, hbeq, hbeq.symm ▸ htu⟩

omit [IsWallAnnihilating H ℳ] in
/-- At a regular crossing, the selected event normal agrees with its offset at
any point of an incident wall. -/
private theorem normal_crossingWallEvent_eq_of_mem (k : ℕ)
    {x y : WallComplement (B.activeSupport k)} (e : x ⟶ y) {t : ℝ}
    (ht : t ∈ orderedCrossingTimes e) (c : B.active k)
    (hc : AffineMap.lineMap x.val y.val t ∈ (B.wall c).support)
    {Q : V} (hQ : Q ∈ (B.wall c).support) :
    (crossingWallEvent (B.activeNormal k) e t ht).normal (B.activeNormal k) Q =
      (crossingWallEvent (B.activeNormal k) e t ht).offset (B.activeOffset k) := by
  set b := crossingWallEvent (B.activeNormal k) e t ht with hb
  have hmem := mem_chosenWall_crossingWallEvent (B.activeNormal k) e t ht
  have hreg := e.down.regular t (Ioo_subset_Icc_self
    (mem_Ioo_of_mem_orderedCrossingTimes e ht))
  have hd : affineSpan ℝ
      (B.wall b.1.property.choose).support =
      affineSpan ℝ (B.wall c).support :=
    affineSpan_eq_of_notMem_singularSupport (W := B.activeSupport k) hreg hmem hc
  have hQspan : Q ∈ affineSpan ℝ
      (B.wall b.1.property.choose).support := by
    rw [hd]
    exact subset_affineSpan ℝ _ hQ
  have hm := AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ _ hmem) hQspan
  rw [(B.wall b.1.property.choose).direction_support,
    LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at hm
  rw [WallEvent.normal_def]
  have hm' : h.continuousRealCharacter
      (B.wall b.1.property.choose).normal
        (AffineMap.lineMap x.val y.val t) =
      h.continuousRealCharacter
        (B.wall b.1.property.choose).normal Q := by
    simpa only [h.continuousRealCharacter_apply] using hm
  have hoff : (B.wall b.1.property.choose).offset =
      b.offset (B.activeOffset k) :=
    (WallEvent.offset_def b
      (B.activeOffset k)).symm
  exact hm'.symm.trans
    (((B.wall b.1.property.choose).offset_eq
      hmem).trans hoff)

omit [IsWallAnnihilating H ℳ] in
open Classical in
/-- A complete admissible backward segment decomposes the evaluation of
canonical simultaneous wall events at each nonzero relative degree. The input
at each event is an arbitrarily close incoming germ of the indicated lower
relative degree; unchanged-degree encounters are removed. -/
theorem exists_decompose_cutoffWallEventEvaluation_eq_sum_lastChange (k : ℕ)
    (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V)
    {n : Γ} {x y : WallComplement ((B.activeSupport (k + 1)))}
    (e : x ⟶ y) (T : ℝ) (hTpos : 0 < T)
    (hxy : x.val - y.val = T • i (ρ (p + n)))
    (htail : ∀ s ≥ T, ∀ c : B.active (k + 1),
      y.val + s • i (ρ (p + n)) ∉ (B.wall c).support)
    (hn : n ∈ d.cutoff (k + 1)) (hn0 : n ≠ 0) :
    ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
      (∀ b ∈ segmentWallEvents ((B.activeNormal (k + 1))) e,
        0 < η b ∧ η b < θ) ∧
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C y.val) n :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
      ∑ b ∈ segmentWallEvents ((B.activeNormal (k + 1))) e,
        ∑ m ∈ (d.finite_cutoff (k + 1)).toFinset with
          m ≠ n ∧ n - m ∈ d.monoid ∧
            b.normal ((B.activeNormal (k + 1))) (i (ρ (p + n))) =
            b.normal ((B.activeNormal (k + 1))) (i (ρ (p + m))),
        (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
          (wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1)
            (Nat.le_refl (k + 1)) b
            (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
              (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C
                (y.val + segmentEventParameter ((B.activeNormal (k + 1))) e T b • i (ρ (p + n)) +
                  η b • i (ρ (p + m)))) m)) n :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) := by
  classical
  let := h.finiteDimensional
  let E := segmentWallEvents ((B.activeNormal (k + 1))) e
  let s := segmentEventParameter ((B.activeNormal (k + 1))) e T
  let f : WallEvent (B.active (k + 1)) → V →L[ℝ] ℝ := fun b =>
    b.normal ((B.activeNormal (k + 1)))
  let vel : Γ → V := fun m => i (ρ (p + m))
  let walls := B.activeSupport (k + 1)
  have ft (b : WallEvent (B.active (k + 1))) (hb : b ∈ E) :
      ∃ t, ∃ ht : t ∈ orderedCrossingTimes e,
        b = crossingWallEvent ((B.activeNormal (k + 1))) e t ht :=
    (mem_segmentWallEvents_iff ((B.activeNormal (k + 1))) e b).mp hb
  have hP (b : WallEvent (B.active (k + 1))) :
      b.support walls ⊆ ⋃ c, walls c := by
    intro Q hQ
    exact Set.mem_iUnion.mpr ⟨b.1.property.choose,
      b.support_subset walls b.1.property.choose_spec hQ⟩
  have hclosedW (c : B.active (k + 1)) : IsClosed (walls c) :=
    (B.wall c).isConvexPolyhedron.isClosed
  have hclosedS (u : Unit) :
      IsClosed ((fun _ : Unit => singularSupport walls) u) := by
    exact isClosed_singularSupport walls hclosedW
  -- The remaining obligations reduce to genuine event parameters, wall geometry,
  -- and the shifted component-preservation lemma for simultaneous actions.
  refine CutoffDecoratedRay.exists_decompose_cutoffDecoratedEvaluation_eq_sum_lastChange
    hn hn0 E (fun b _ => decompose_wallEventPropagation_self d ℳ p ℒ H h B (k + 1) b)
      hP hclosedW hclosedS s ?_ ?_ ?_ ?_ ?_ ?_
  -- Event parameters are injective on the finite event inventory.
  · exact segmentEventParameter_injOn ((B.activeNormal (k + 1))) e T hTpos
  -- Genuine events have positivity, transversality, signs, height and support.
  · intro b hb
    obtain ⟨t, ht, rfl⟩ := ft b hb
    obtain ⟨hs, hv, hsg, -, hoff, hmem⟩ :=
      crossing_event_data d p ℒ H h B (k + 1) e T hTpos hxy ht rfl
    exact ⟨hs, hv, hsg, hoff, hmem⟩
  -- A matching wall point and sign determine its canonical event.
  · intro b u hu htr hsg hh hm
    obtain ⟨t, ht, hbeq, htu⟩ :=
      eq_crossingWallEvent_of_mem_support_of_sign d p ℒ H h B (k + 1) e hTpos hxy htail b
        hu.le (by simpa only [f, vel] using hsg) (by simpa only [walls, vel] using hm)
    rw [hbeq] at htu
    rw [hbeq]
    exact ⟨crossingWallEvent_mem_segmentWallEvents ((B.activeNormal (k + 1))) e ht, htu⟩
  -- Points on an incident affine hyperplane give the same event offset.
  · intro b hb c hc Q hQ
    obtain ⟨t, ht, hb⟩ := ft b hb
    subst b
    apply normal_crossingWallEvent_eq_of_mem d ℒ H h B (k + 1) e ht c ?_ hQ
    rw [lineMap_eq_add_smul (t := t) hxy]
    simpa only [s, segmentEventParameter_of_mem, walls, B.activeSupport_apply] using hc
  -- Every ambient-wall hit along the ray comes from a genuine crossing event.
  · intro c u hu hmem
    obtain ⟨t, ht, htu, _⟩ := exists_crossingTime_of_pos_of_wall d p ℒ H h B (k + 1)
      e hTpos hxy htail hu c hmem
    exact ⟨crossingWallEvent (B.activeNormal (k + 1)) e t ht,
      crossingWallEvent_mem_segmentWallEvents (B.activeNormal (k + 1)) e ht, htu⟩
  -- The tail does not intersect the singular support.
  · intro _ u hu hsing
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (singularSupport_subset_iUnion walls hclosedW hsing)
    obtain ⟨t, ht, htu, hline⟩ := exists_crossingTime_of_pos_of_wall d p ℒ H h B (k + 1)
      e hTpos hxy htail hu c hc
    exact e.down.regular t (Ioo_subset_Icc_self
      (mem_Ioo_of_mem_orderedCrossingTimes e ht)) (hline ▸ hsing)

omit [IsWallAnnihilating H ℳ] in
/-- Truncating the coefficient quotient commutes with the whole wall-event
weighted evaluation, without changing the geometric event inventory. -/
theorem transition_cutoffWallEventEvaluation {k K : ℕ} (hk : k ≤ K)
    (a : (d.shiftedQuotientGrading ℳ p K).piece 0) (C : Set V) (Q : V) :
    (d.shiftedLieFiltration ℒ ℳ p).transition hk
        (cutoffWallEventEvaluation d ℳ p ℒ H h B K K (Nat.le_refl K) a C Q) =
      cutoffWallEventEvaluation d ℳ p ℒ H h B k K hk
        ⟨(d.shiftedLieFiltration ℒ ℳ p).transition hk a,
          d.transition_mem_shiftedQuotientGrading ℳ p hk a.property⟩ C Q := by
  simp only [cutoffWallEventEvaluation_def, wallEventPropagation_def,
    d.truncationMap_refl, LieHom.bchGroupMap_id, MonoidHom.id_apply]
  exact
    (d.transition_cutoffDecoratedEvaluation_shiftedBCHAction ℒ ℳ p
      (fun n => i (ρ (p + n)))
      (fun e : WallEvent (B.active K) =>
        e.normal ((B.activeNormal K)))
      (fun e : WallEvent (B.active K) =>
        e.offset ((B.activeOffset K)))
      (fun e : WallEvent (B.active K) => e.2)
      (fun e : WallEvent (B.active K) => e.support ((B.activeSupport K)))
      ((B.activeSupport K))
      (fun _ : Unit => singularSupport ((B.activeSupport K)))
      C Q hk (fun e : WallEvent (B.active K) => B.wallEventLabel K e) a)

end Mei.ModuleProbe
