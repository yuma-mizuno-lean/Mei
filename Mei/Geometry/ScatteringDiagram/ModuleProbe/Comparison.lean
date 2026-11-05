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

/-- The real height of a wall, computed from its nonempty support. Every point
of its support has this height because the direction is the kernel of its normal. -/
private def wallOffset (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
    {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
    [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
    {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
    (W : DirectedWall (d := d) h H) : ℝ :=
  h.continuousRealCharacter W.normal W.support_nonempty.choose

private theorem wallOffset_apply (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
    {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
    [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
    {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
    (W : DirectedWall (d := d) h H)
    {x : V} (hx : x ∈ W.support) :
    h.continuousRealCharacter W.normal x = wallOffset d ℒ H h W := by
  simpa only [wallOffset, h.continuousRealCharacter_apply] using
    W.normal_apply_eq hx W.support_nonempty.choose_spec

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

/-- Weighted evaluation of every finite itinerary of canonical simultaneous wall events.
The coefficients live in the same shifted finite quotient as the probe field, while
avoidance and the event alphabet retain the possibly larger geometric cutoff. -/
def cutoffWallEventEvaluation (k K : ℕ) (hkK : k ≤ K)
    (a : (d.shiftedQuotientGrading ℳ p k).piece 0) (C : Set V) (Q : V) :
    (d.shiftedLieFiltration ℒ ℳ p).quotient k :=
  cutoffDecoratedEvaluation d (d.shiftedQuotientGrading ℳ p k).piece
    (fun e : WallEvent (B.active K) => wallEventPropagation d ℳ p ℒ H h B k K hkK e)
    a (fun n => i (ρ (p + n)))
    (fun e => e.normal (fun c : B.active K => h.continuousRealCharacter (B.wall c).normal))
    (fun e => e.offset (fun c : B.active K => wallOffset d ℒ H h (B.wall c)))
    (fun e => e.2) (fun e => e.support (fun c : B.active K => (B.wall c).support))
    (fun c : B.active K => (B.wall c).support)
    (fun _ : Unit => singularSupport (fun c : B.active K => (B.wall c).support)) C k Q

/-- The full inventory of simultaneous events on one admissible segment. -/
def segmentWallEvents (k : ℕ)
    {x y : WallComplement (fun c : B.active k => (B.wall c).support)}
    (e : x ⟶ y) : Finset (WallEvent (B.active k)) := by
  classical
  exact (orderedCrossingTimes e).toFinset.attach.image fun t =>
    crossingWallEvent (fun c : B.active k => h.continuousRealCharacter (B.wall c).normal)
      e t.val (List.mem_toFinset.mp t.property)

/-- The ray parameter of each segment event, defined by recovering its genuine
crossing time from that event. It is zero away from the actual event inventory. -/
def segmentEventParameter (k : ℕ)
    {x y : WallComplement (fun c : B.active k => (B.wall c).support)}
    (e : x ⟶ y) (T : ℝ) (b : WallEvent (B.active k)) : ℝ := by
  classical
  exact if hb : b ∈ segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) k e then
    T * (1 - (Finset.mem_image.mp hb).choose.val) else 0

/-- A genuine segment crossing belongs to its finite simultaneous-event
inventory. -/
@[simp]
theorem mem_segmentWallEvents (k : ℕ)
    {x y : WallComplement (fun c : B.active k => (B.wall c).support)}
    (e : x ⟶ y) {t : ℝ} (ht : t ∈ orderedCrossingTimes e) :
    crossingWallEvent (fun c : B.active k => h.continuousRealCharacter (B.wall c).normal)
      e t ht ∈ segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) k e := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨⟨t, List.mem_toFinset.mpr ht⟩, Finset.mem_attach _ _, rfl⟩

/-- An event's ray parameter is the terminal displacement at its genuine
crossing time. -/
@[simp]
theorem segmentEventParameter_of_mem (k : ℕ)
    {x y : WallComplement (fun c : B.active k => (B.wall c).support)}
    (e : x ⟶ y) (T : ℝ) {t : ℝ} (ht : t ∈ orderedCrossingTimes e) :
    segmentEventParameter (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) k e T
      (crossingWallEvent (fun c : B.active k => h.continuousRealCharacter (B.wall c).normal)
        e t ht) = T * (1 - t) := by
  classical
  let b := crossingWallEvent (fun c : B.active k => h.continuousRealCharacter (B.wall c).normal)
    e t ht
  have hb : b ∈ segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) k e :=
    mem_segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) k e ht
  have he := (Finset.mem_image.mp hb).choose_spec.2
  have ht' : (Finset.mem_image.mp hb).choose.val ∈ orderedCrossingTimes e :=
    List.mem_toFinset.mp (Finset.mem_image.mp hb).choose.property
  rw [segmentEventParameter, dite_eq_left hb]
  congr 2
  exact
    crossingWallEvent_injective
      (fun c : B.active k => h.continuousRealCharacter (B.wall c).normal) e ht' ht he

private theorem realFunctional_sign_pos_smul (f : V →L[ℝ] ℝ)
    (v : V) {t : ℝ} (ht : 0 < t) :
    SignType.sign (f (t • v)) = SignType.sign (f v) := by
  simp [sign_mul, sign_pos ht]

omit [IsWallAnnihilating H ℳ] in
open Classical in
/-- A complete admissible backward segment decomposes the evaluation of
canonical simultaneous wall events at each nonzero relative degree. The input
at each event is an arbitrarily close incoming germ of the indicated lower
relative degree; unchanged-degree encounters are removed. -/
theorem exists_decompose_cutoffWallEventEvaluation_eq_sum_lastChange (k : ℕ)
    (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V)
    {n : Γ} {x y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support)}
    (e : x ⟶ y) (T : ℝ) (hTpos : 0 < T)
    (hxy : x.val - y.val = T • i (ρ (p + n)))
    (htail : ∀ s ≥ T, ∀ c : B.active (k + 1),
      y.val + s • i (ρ (p + n)) ∉ (B.wall c).support)
    (hn : n ∈ d.cutoff (k + 1)) (hn0 : n ≠ 0) :
    ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
      (∀ b ∈ segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) (k + 1) e,
        0 < η b ∧ η b < θ) ∧
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C y.val) n :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
      ∑ b ∈ segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) (k + 1) e,
        ∑ m ∈ (d.finite_cutoff (k + 1)).toFinset with
          m ≠ n ∧ n - m ∈ d.monoid ∧
            b.normal (fun c : B.active (k + 1) =>
              h.continuousRealCharacter (B.wall c).normal) (i (ρ (p + n))) =
            b.normal (fun c : B.active (k + 1) =>
              h.continuousRealCharacter (B.wall c).normal) (i (ρ (p + m))),
        (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
          (wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1)
            (Nat.le_refl (k + 1)) b
            (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
              (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C
                (y.val + segmentEventParameter (d := d) (ℒ := ℒ) (H := H) (h := h)
                  (B := B) (k + 1) e T b • i (ρ (p + n)) +
                  η b • i (ρ (p + m)))) m)) n :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) := by
  classical
  let := h.finiteDimensional
  let E := segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) (k + 1) e
  let s := segmentEventParameter (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) (k + 1) e T
  let f : WallEvent (B.active (k + 1)) → V →L[ℝ] ℝ := fun b =>
    b.normal (fun c : B.active (k + 1) => h.continuousRealCharacter (B.wall c).normal)
  let off : WallEvent (B.active (k + 1)) → ℝ := fun b =>
    b.offset (fun c : B.active (k + 1) => wallOffset d ℒ H h (B.wall c))
  let vel : Γ → V := fun m => i (ρ (p + m))
  let walls : B.active (k + 1) → Set V := fun c => (B.wall c).support
  have ft (b : WallEvent (B.active (k + 1))) (hb : b ∈ E) :
      ∃ t, ∃ ht : t ∈ orderedCrossingTimes e,
        b = crossingWallEvent (fun c : B.active (k + 1) =>
          h.continuousRealCharacter (B.wall c).normal) e t ht := by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hb
    have ht' : t.val ∈ orderedCrossingTimes e := List.mem_toFinset.mp t.property
    refine ⟨t.val, ht', ?_⟩
    simpa only using ht.symm
  have hpoint {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal) e t ht) :
      AffineMap.lineMap x.val y.val t = y.val + s b • vel n := by
    subst b
    calc
      AffineMap.lineMap x.val y.val t = y.val + (1 - t) • (x.val - y.val) := by
        rw [AffineMap.lineMap_apply_module']
        module
      _ = y.val + (T * (1 - t)) • vel n := by
        rw [hxy]
        dsimp only [vel]
        module
      _ = y.val + s _ • vel n := by
        change _ = y.val + segmentEventParameter (d := d) (ℒ := ℒ) (H := H) (h := h)
          (B := B) (k + 1) e T _ • vel n
        rw [segmentEventParameter_of_mem (d := d) (ℒ := ℒ) (H := H) (h := h)
          (B := B) (k + 1) e T ht]
  have hpos {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal) e t ht) :
      0 < s b := by
    subst b
    change 0 < segmentEventParameter (d := d) (ℒ := ℒ) (H := H) (h := h)
      (B := B) (k + 1) e T _
    rw [segmentEventParameter_of_mem (d := d) (ℒ := ℒ) (H := H) (h := h)
      (B := B) (k + 1) e T ht]
    exact mul_pos hTpos (sub_pos.mpr
      (mem_Ioo_of_mem_orderedCrossingTimes e ht).2)
  have hinc {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal) e t ht) :
      y.val + s b • vel n ∈ b.support walls := by
    subst b
    rw [← hpoint ht rfl]
    exact (WallEvent.mem_support _ _ _).2 (fun j => by
      simpa only [walls] using mem_crossingWallEvent _ e t ht j)
  have hplane' {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal) e t ht) :
      f b (y.val + s b • vel n) = off b :=
    WallEvent.normal_apply_of_mem_support b walls (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)
      (fun c => wallOffset d ℒ H h (B.wall c))
      (fun c z hz => wallOffset_apply d ℒ H h (B.wall c) hz) (hinc ht hb)
  have htrans {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal) e t ht) :
      f b (vel n) ≠ 0 := by
    have hmem : AffineMap.lineMap x.val y.val t ∈
        (B.wall b.1.property.choose).support := by
      rw [hpoint ht hb]
      exact (WallEvent.mem_support _ _ _).mp (hinc ht hb) _ |>.mpr
        b.1.property.choose_spec
    have hdir := e.down.transverse b.1.property.choose
      ⟨t, Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e ht), hmem⟩
    rw [(B.wall b.1.property.choose).direction_support, LinearMap.mem_ker] at hdir
    have hdir' : f b (y.val - x.val) ≠ 0 := by
      simpa only [f, WallEvent.normal_def, h.continuousRealCharacter_apply] using hdir
    intro hz
    apply hdir'
    have hyx : y.val - x.val = (-T) • vel n := by
      dsimp only [vel]
      calc
        y.val - x.val = -(x.val - y.val) := by abel
        _ = -T • i (ρ (p + n)) := by rw [hxy]; module
    simp only [hyx, map_smul, hz, smul_zero]
  have hsign {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal) e t ht) :
      SignType.sign (f b (vel n)) = b.2 := by
    have hs := normal_sign_crossingWallEvent
      (fun c : B.active (k + 1) => h.continuousRealCharacter (B.wall c).normal) e t ht
    rw [← hb] at hs
    calc
      SignType.sign (f b (vel n)) = SignType.sign (f b (x.val - y.val)) := by
        rw [hxy]
        exact (realFunctional_sign_pos_smul (f b) (vel n) hTpos).symm
      _ = b.2 := by simpa only [f] using hs
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
  have hdiag (b : WallEvent (B.active (k + 1)))
      (z : (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1))
      (hz : z ∈ (d.shiftedQuotientGrading ℳ p (k + 1)).piece n) :
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl (k + 1)) b z) n :
        (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) = z :=
    by
    simpa [wallEventPropagation, d.truncationMap_refl, wallEventPropagation_apply] using
      (d.decompose_truncatedBCHAction_same ℒ ℳ p (k + 1)
        (B.wallEventLabel (k + 1) b) hz)
  refine CutoffDecoratedRay.exists_decompose_cutoffDecoratedEvaluation_eq_sum_lastChange
    hn hn0 E (fun b hb => hdiag b) hP hclosedW hclosedS s ?_ ?_ ?_ ?_ ?_ ?_
  · intro b hb b' hb' he
    obtain ⟨t, ht, rfl⟩ := ft b hb
    obtain ⟨t', ht', rfl⟩ := ft b' hb'
    change segmentEventParameter (d := d) (ℒ := ℒ) (H := H) (h := h)
      (B := B) (k + 1) e T _ = segmentEventParameter (d := d) (ℒ := ℒ)
        (H := H) (h := h) (B := B) (k + 1) e T _ at he
    rw [segmentEventParameter_of_mem (d := d) (ℒ := ℒ) (H := H) (h := h)
      (B := B) (k + 1) e T ht, segmentEventParameter_of_mem (d := d) (ℒ := ℒ) (H := H)
      (h := h) (B := B) (k + 1) e T ht'] at he
    have htt : t = t' := by
      apply (mul_left_cancel₀ (ne_of_gt hTpos))
      linarith
    subst t'
    rfl
  · intro b hb
    obtain ⟨t, ht, rfl⟩ := ft b hb
    exact ⟨hpos ht rfl, htrans ht rfl, hsign ht rfl, hplane' ht rfl, hinc ht rfl⟩
  · intro b u hu htr hsg hh hm
    have huT : u < T := by
      by_contra hnT
      apply htail u (le_of_not_gt hnT) b.1.property.choose
      exact b.support_subset walls b.1.property.choose_spec hm
    let t := 1 - u / T
    have hlt : u / T < 1 := (div_lt_one hTpos).mpr huT
    have htz : 0 < t := by dsimp only [t]; exact sub_pos.mpr hlt
    have ht1 : t < 1 := by
      have hu' : 0 < u / T := div_pos hu hTpos
      dsimp only [t]
      linarith
    have htu : u = T * (1 - t) := by dsimp only [t]; field_simp; ring
    have hline : y.val + u • vel n = AffineMap.lineMap x.val y.val t := by
      calc
        y.val + u • vel n = y.val + (1 - t) • (x.val - y.val) := by
          rw [htu, hxy]
          dsimp only [vel]
          module
        _ = AffineMap.lineMap x.val y.val t := by
          rw [AffineMap.lineMap_apply_module']
          module
    have hmem : ∀ c : B.active (k + 1),
        AffineMap.lineMap x.val y.val t ∈ walls c ↔ c ∈ b.1.val := by
      intro c
      rw [← hline]
      exact (WallEvent.mem_support b walls _).mp hm c
    obtain ⟨c, hc⟩ := b.1.property
    have ht : t ∈ orderedCrossingTimes e := by
      rw [mem_orderedCrossingTimes]
      exact ⟨c, (mem_crossings x y c t).mpr ⟨⟨htz.le, ht1.le⟩, (hmem c).mpr hc⟩⟩
    have hbeq : b = crossingWallEvent (fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal) e t ht :=
      WallEvent.eq_of_mem_support_of_normal_sign_eq
        (x := AffineMap.lineMap x.val y.val t)
        b (crossingWallEvent (fun c : B.active (k + 1) =>
          h.continuousRealCharacter (B.wall c).normal) e t ht) walls
        (fun c : B.active (k + 1) => h.continuousRealCharacter (B.wall c).normal)
        (x.val - y.val)
        ((WallEvent.mem_support b walls _).2 (fun c => hmem c))
        ((WallEvent.mem_support _ walls _).2 (fun c =>
          mem_crossingWallEvent _ e t ht c))
        (by
          calc
            SignType.sign (f b (x.val - y.val)) = SignType.sign (f b (vel n)) := by
              rw [hxy]
              exact realFunctional_sign_pos_smul (f b) (vel n) hTpos
            _ = b.2 := by simpa only [f] using hsg)
        (normal_sign_crossingWallEvent _ e t ht)
    rw [hbeq]
    exact ⟨mem_segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h)
      (B := B) (k + 1) e ht,
      (segmentEventParameter_of_mem (d := d) (ℒ := ℒ) (H := H) (h := h)
        (B := B) (k + 1) e T ht).trans htu.symm⟩
  · intro b hb c hc Q hQ
    obtain ⟨t, ht, hb⟩ := ft b hb
    have hmem : AffineMap.lineMap x.val y.val t ∈
        (B.wall b.1.property.choose).support := by
      rw [hpoint ht hb]
      exact (WallEvent.mem_support _ _ _).mp (hinc ht hb) _ |>.mpr
        b.1.property.choose_spec
    have hreg := e.down.regular t (Ioo_subset_Icc_self
      (mem_Ioo_of_mem_orderedCrossingTimes e ht))
    have hc' : AffineMap.lineMap x.val y.val t ∈ walls c := by
      rw [hpoint ht hb]
      exact hc
    have hd : affineSpan ℝ (B.wall b.1.property.choose).support =
        affineSpan ℝ (B.wall c).support := by
      apply affineSpan_eq_of_notMem_singularSupport (W := walls) hreg hmem hc'
    have hzaffine : Q ∈ affineSpan ℝ (B.wall b.1.property.choose).support := by
      rw [hd]
      exact subset_affineSpan ℝ _ hQ
    have hm := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ hmem) hzaffine
    rw [(B.wall b.1.property.choose).direction_support, LinearMap.mem_ker,
      vsub_eq_sub, map_sub, sub_eq_zero] at hm
    rw [WallEvent.normal_def]
    have hm' : h.continuousRealCharacter (B.wall b.1.property.choose).normal
        (AffineMap.lineMap x.val y.val t) =
        h.continuousRealCharacter (B.wall b.1.property.choose).normal Q := by
      simpa only [h.continuousRealCharacter_apply] using hm
    have hzaffine : Q ∈ affineSpan ℝ (B.wall b.1.property.choose).support := by
      rw [hd]
      exact subset_affineSpan ℝ _ hQ
    have hm := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ hmem) hzaffine
    rw [(B.wall b.1.property.choose).direction_support, LinearMap.mem_ker,
      vsub_eq_sub, map_sub, sub_eq_zero] at hm
    have hoff : wallOffset d ℒ H h (B.wall b.1.property.choose) =
        b.offset (fun c : B.active (k + 1) => wallOffset d ℒ H h (B.wall c)) :=
      (WallEvent.offset_def b (fun c : B.active (k + 1) =>
        wallOffset d ℒ H h (B.wall c))).symm
    exact hm'.symm.trans ((wallOffset_apply d ℒ H h
      (B.wall b.1.property.choose) hmem).trans hoff)
  · intro c u hu hmem
    have hu0 : 0 < u := by
      rcases hu.eq_or_lt with rfl | hu
      · exact (y.notMem c (by simpa using hmem)).elim
      · exact hu
    have huT : u < T := by
      by_contra hnT
      exact htail u (le_of_not_gt hnT) c hmem
    let t := 1 - u / T
    have hlt : u / T < 1 := (div_lt_one hTpos).mpr huT
    have htz : 0 < t := by dsimp only [t]; exact sub_pos.mpr hlt
    have ht1 : t < 1 := by
      have hu' : 0 < u / T := div_pos hu0 hTpos
      dsimp only [t]
      linarith
    have htu : u = T * (1 - t) := by dsimp only [t]; field_simp; ring
    have hline : y.val + u • vel n = AffineMap.lineMap x.val y.val t := by
      calc
        y.val + u • vel n = y.val + (1 - t) • (x.val - y.val) := by
          rw [htu, hxy]
          dsimp only [vel]
          module
        _ = AffineMap.lineMap x.val y.val t := by
          rw [AffineMap.lineMap_apply_module']
          module
    have ht : t ∈ orderedCrossingTimes e := by
      rw [mem_orderedCrossingTimes]
      exact ⟨c, (mem_crossings x y c t).mpr
        ⟨⟨htz.le, ht1.le⟩, by rw [← hline]; exact hmem⟩⟩
    refine ⟨crossingWallEvent (fun c : B.active (k + 1) =>
      h.continuousRealCharacter (B.wall c).normal) e t ht,
      mem_segmentWallEvents (d := d) (ℒ := ℒ) (H := H) (h := h)
        (B := B) (k + 1) e ht, ?_⟩
    · change segmentEventParameter (d := d) (ℒ := ℒ) (H := H) (h := h)
        (B := B) (k + 1) e T _ = u
      exact (segmentEventParameter_of_mem (d := d) (ℒ := ℒ) (H := H) (h := h)
        (B := B) (k + 1) e T ht).trans htu.symm
  · intro _ u hu hsing
    by_cases huT : u < T
    · let t := 1 - u / T
      have htz : 0 < t := by
        dsimp only [t]
        exact sub_pos.mpr ((div_lt_one hTpos).mpr huT)
      have ht1 : t < 1 := by
        have hupos : 0 < u := by
          rcases hu.eq_or_lt with rfl | hu
          · exfalso
            obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
              (singularSupport_subset_iUnion walls hclosedW hsing)
            exact y.notMem c (by simpa only [walls, zero_smul, add_zero] using hc)
          · exact hu
        have hu' : 0 < u / T := div_pos hupos hTpos
        dsimp only [t]
        linarith
      have hline : y.val + u • vel n = AffineMap.lineMap x.val y.val t := by
        have htu : u = T * (1 - t) := by dsimp only [t]; field_simp; ring
        calc
          y.val + u • vel n = y.val + (1 - t) • (x.val - y.val) := by
            rw [htu, hxy]
            dsimp only [vel]
            module
          _ = AffineMap.lineMap x.val y.val t := by
            rw [AffineMap.lineMap_apply_module']
            module
      exact e.down.regular t ⟨htz.le, ht1.le⟩ (hline ▸ hsing)
    · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
        (singularSupport_subset_iUnion walls hclosedW hsing)
      exact htail u (le_of_not_gt huT) c hc

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
  simpa [cutoffWallEventEvaluation, wallEventPropagation] using
    (d.transition_cutoffDecoratedEvaluation_shiftedBCHAction ℒ ℳ p
      (fun n => i (ρ (p + n)))
      (fun e : WallEvent (B.active K) =>
        e.normal (fun c : B.active K => h.continuousRealCharacter (B.wall c).normal))
      (fun e : WallEvent (B.active K) =>
        e.offset (fun c : B.active K => wallOffset d ℒ H h (B.wall c)))
      (fun e : WallEvent (B.active K) => e.2)
      (fun e : WallEvent (B.active K) => e.support (fun c : B.active K => (B.wall c).support))
      (fun c : B.active K => (B.wall c).support)
      (fun _ : Unit => singularSupport (fun c : B.active K => (B.wall c).support))
      C Q hk (fun e : WallEvent (B.active K) => B.wallEventLabel K e) a)

end Mei.ModuleProbe
