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
    (fun e => e.normal ((fun c : B.active K =>
        h.continuousRealCharacter (B.wall c).normal)))
    (fun e => e.offset ((fun c : B.active K => (B.wall c).offset)))
    (fun e => e.2) (fun e => e.support ((fun c : B.active K => (B.wall c).support)))
    ((fun c : B.active K => (B.wall c).support))
    (fun _ : Unit => singularSupport ((fun c : B.active K => (B.wall c).support))) C k Q

omit [IsWallAnnihilating H ℳ] in
/-- Defining equation for canonical simultaneous-event weighted evaluation. -/
theorem cutoffWallEventEvaluation_def (k K : ℕ) (hkK : k ≤ K)
    (a : (d.shiftedQuotientGrading ℳ p k).piece 0) (C : Set V) (Q : V) :
    cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a C Q =
      cutoffDecoratedEvaluation d (d.shiftedQuotientGrading ℳ p k).piece
        (fun e : WallEvent (B.active K) => wallEventPropagation d ℳ p ℒ H h B k K hkK e)
        a (fun n => i (ρ (p + n)))
        (fun e => e.normal
          ((fun c : B.active K =>
        h.continuousRealCharacter (B.wall c).normal)))
        (fun e => e.offset ((fun c : B.active K => (B.wall c).offset)))
        (fun e => e.2)
        (fun e => e.support ((fun c : B.active K => (B.wall c).support)))
        ((fun c : B.active K => (B.wall c).support))
        (fun _ : Unit =>
          singularSupport ((fun c : B.active K => (B.wall c).support))) C k Q := (rfl)

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

private theorem lineMap_eq_add_smul {x y w : V} {T t : ℝ} (hxy : x - y = T • w) :
    AffineMap.lineMap x y t = y + (T * (1 - t)) • w := by
  calc
    AffineMap.lineMap x y t = y + (1 - t) • (x - y) := by
      rw [AffineMap.lineMap_apply_module']
      module
    _ = _ := by rw [hxy]; module

private theorem lineMap_eq_add_smul_of_pos_of_lt {x y w : V} {T u : ℝ}
    (hT : 0 < T) (hxy : x - y = T • w) (hu : 0 < u) (huT : u < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      u = T * (1 - t) ∧ y + u • w = AffineMap.lineMap x y t := by
  let t := 1 - u / T
  have ht0 : 0 < t := sub_pos.mpr ((div_lt_one hT).mpr huT)
  have ht1 : t < 1 := by
    have hup : 0 < u / T := div_pos hu hT
    dsimp only [t]
    linarith
  have htu : u = T * (1 - t) := by dsimp only [t]; field_simp; ring
  refine ⟨t, ⟨ht0, ht1⟩, htu, ?_⟩
  calc
    y + u • w = y + (T * (1 - t)) • w := by rw [htu]
    _ = _ := (lineMap_eq_add_smul (t := t) hxy).symm

omit [IsWallAnnihilating H ℳ] in
open Classical in
/-- A complete admissible backward segment decomposes the evaluation of
canonical simultaneous wall events at each nonzero relative degree. The input
at each event is an arbitrarily close incoming germ of the indicated lower
relative degree; unchanged-degree encounters are removed. -/
theorem exists_decompose_cutoffWallEventEvaluation_eq_sum_lastChange (k : ℕ)
    (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V)
    {n : Γ} {x y : WallComplement ((fun c : B.active (k + 1) => (B.wall c).support))}
    (e : x ⟶ y) (T : ℝ) (hTpos : 0 < T)
    (hxy : x.val - y.val = T • i (ρ (p + n)))
    (htail : ∀ s ≥ T, ∀ c : B.active (k + 1),
      y.val + s • i (ρ (p + n)) ∉ (B.wall c).support)
    (hn : n ∈ d.cutoff (k + 1)) (hn0 : n ≠ 0) :
    ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
      (∀ b ∈ segmentWallEvents ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e,
        0 < η b ∧ η b < θ) ∧
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
        (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C y.val) n :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) =
      ∑ b ∈ segmentWallEvents ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e,
        ∑ m ∈ (d.finite_cutoff (k + 1)).toFinset with
          m ≠ n ∧ n - m ∈ d.monoid ∧
            b.normal ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) (i (ρ (p + n))) =
            b.normal ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) (i (ρ (p + m))),
        (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
          (wallEventPropagation d ℳ p ℒ H h B (k + 1) (k + 1)
            (Nat.le_refl (k + 1)) b
            (DirectSum.decompose (d.shiftedQuotientGrading ℳ p (k + 1)).piece
              (cutoffWallEventEvaluation d ℳ p ℒ H h B (k + 1) (k + 1)
          (Nat.le_refl (k + 1)) a C
                (y.val + segmentEventParameter ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e T b • i (ρ (p + n)) +
                  η b • i (ρ (p + m)))) m)) n :
          (d.shiftedLieFiltration ℒ ℳ p).quotient (k + 1)) := by
  classical
  let := h.finiteDimensional
  let E := segmentWallEvents ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e
  let s := segmentEventParameter ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e T
  let f : WallEvent (B.active (k + 1)) → V →L[ℝ] ℝ := fun b =>
    b.normal ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal))
  let off : WallEvent (B.active (k + 1)) → ℝ := fun b =>
    b.offset ((fun c : B.active (k + 1) => (B.wall c).offset))
  let vel : Γ → V := fun m => i (ρ (p + m))
  let walls : B.active (k + 1) → Set V := fun c => (B.wall c).support
  have ft (b : WallEvent (B.active (k + 1))) (hb : b ∈ E) :
      ∃ t, ∃ ht : t ∈ orderedCrossingTimes e,
        b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht :=
    (mem_segmentWallEvents_iff ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e b).mp hb
  have hpoint {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht) :
      AffineMap.lineMap x.val y.val t = y.val + s b • vel n := by
    subst b
    rw [lineMap_eq_add_smul (t := t) hxy]
    simp only [s, vel, segmentEventParameter_of_mem]
  have hpos {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht) :
      0 < s b := by
    subst b
    exact segmentEventParameter_pos ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e T hTpos ht
  have hinc {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht) :
      y.val + s b • vel n ∈ b.support walls := by
    subst b
    rw [← hpoint ht rfl]
    exact (WallEvent.mem_support _ _ _).2 (fun j => by
      simpa only [walls] using mem_crossingWallEvent _ e t ht j)
  have hplane' {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht) :
      f b (y.val + s b • vel n) = off b :=
    WallEvent.normal_apply_of_mem_support b walls
      ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal))
      ((fun c : B.active (k + 1) => (B.wall c).offset))
      (fun c z hz => (B.wall c).offset_eq hz) (hinc ht hb)
  have htrans {b : WallEvent (B.active (k + 1))} {t : ℝ}
      (ht : t ∈ orderedCrossingTimes e)
      (hb : b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht) :
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
      (hb : b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht) :
      SignType.sign (f b (vel n)) = b.2 := by
    have hs := normal_sign_crossingWallEvent
      ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht
    rw [← hb] at hs
    calc
      SignType.sign (f b (vel n)) = SignType.sign (f b (x.val - y.val)) := by
        rw [hxy]
        have hs : SignType.sign (f b (T • vel n)) = SignType.sign (f b (vel n)) := by
          simp [sign_mul, sign_pos hTpos]
        exact hs.symm
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
  -- The remaining obligations reduce to genuine event parameters, wall geometry,
  -- and the shifted component-preservation lemma for simultaneous actions.
  refine CutoffDecoratedRay.exists_decompose_cutoffDecoratedEvaluation_eq_sum_lastChange
    hn hn0 E (fun b _ => decompose_wallEventPropagation_self d ℳ p ℒ H h B (k + 1) b)
      hP hclosedW hclosedS s ?_ ?_ ?_ ?_ ?_ ?_
  · exact segmentEventParameter_injective ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e T hTpos
  · intro b hb
    obtain ⟨t, ht, rfl⟩ := ft b hb
    exact ⟨hpos ht rfl, htrans ht rfl, hsign ht rfl, hplane' ht rfl, hinc ht rfl⟩
  · intro b u hu htr hsg hh hm
    have huT : u < T := by
      by_contra hnT
      apply htail u (le_of_not_gt hnT) b.1.property.choose
      exact b.support_subset walls b.1.property.choose_spec hm
    obtain ⟨t, hti, htu, hline⟩ :=
      lineMap_eq_add_smul_of_pos_of_lt (w := vel n) hTpos hxy hu huT
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hti
    have hmem : ∀ c : B.active (k + 1),
        AffineMap.lineMap x.val y.val t ∈ walls c ↔ c ∈ b.1.val := by
      intro c
      rw [← hline]
      exact (WallEvent.mem_support b walls _).mp hm c
    obtain ⟨c, hc⟩ := b.1.property
    have ht : t ∈ orderedCrossingTimes e := by
      rw [mem_orderedCrossingTimes]
      exact ⟨c, (mem_crossings x y c t).mpr ⟨htIcc, (hmem c).mpr hc⟩⟩
    have hbeq : b = crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht :=
      WallEvent.eq_of_mem_support_of_normal_sign_eq
        (x := AffineMap.lineMap x.val y.val t)
        b (crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht) walls
        ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal))
        (x.val - y.val)
        ((WallEvent.mem_support b walls _).2 (fun c => hmem c))
        ((WallEvent.mem_support _ walls _).2 (fun c =>
          mem_crossingWallEvent _ e t ht c))
        (by
          calc
            SignType.sign (f b (x.val - y.val)) = SignType.sign (f b (vel n)) := by
              rw [hxy]
              exact (by
                simp [sign_mul, sign_pos hTpos] :
                SignType.sign (f b (T • vel n)) = SignType.sign (f b (vel n)))
            _ = b.2 := by simpa only [f] using hsg)
        (normal_sign_crossingWallEvent _ e t ht)
    rw [hbeq]
    exact ⟨crossingWallEvent_mem_segmentWallEvents ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e ht,
      (segmentEventParameter_of_mem ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e T ht).trans htu.symm⟩
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
        affineSpan ℝ (B.wall c).support :=
      affineSpan_eq_of_notMem_singularSupport (W := walls) hreg hmem hc'
    have hQspan : Q ∈ affineSpan ℝ (B.wall b.1.property.choose).support := by
      rw [hd]
      exact subset_affineSpan ℝ _ hQ
    have hm := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ hmem) hQspan
    rw [(B.wall b.1.property.choose).direction_support, LinearMap.mem_ker,
      vsub_eq_sub, map_sub, sub_eq_zero] at hm
    rw [WallEvent.normal_def]
    have hoff : (B.wall b.1.property.choose).offset =
        b.offset ((fun c : B.active (k + 1) => (B.wall c).offset)) :=
      (WallEvent.offset_def b ((fun c : B.active (k + 1) => (B.wall c).offset))).symm
    have hm' : h.continuousRealCharacter (B.wall b.1.property.choose).normal
        (AffineMap.lineMap x.val y.val t) =
        h.continuousRealCharacter (B.wall b.1.property.choose).normal Q := by
      simpa only [h.continuousRealCharacter_apply] using hm
    exact hm'.symm.trans (((B.wall b.1.property.choose).offset_eq hmem).trans hoff)
  · intro c u hu hmem
    have hu0 : 0 < u := by
      rcases hu.eq_or_lt with rfl | hu
      · exact (y.notMem c (by simpa using hmem)).elim
      · exact hu
    have huT : u < T := by
      by_contra hnT
      exact htail u (le_of_not_gt hnT) c hmem
    obtain ⟨t, hti, htu, hline⟩ :=
      lineMap_eq_add_smul_of_pos_of_lt (w := vel n) hTpos hxy hu0 huT
    have ht : t ∈ orderedCrossingTimes e := by
      rw [mem_orderedCrossingTimes]
      exact ⟨c, (mem_crossings x y c t).mpr
        ⟨Set.Ioo_subset_Icc_self hti, by rw [← hline]; exact hmem⟩⟩
    refine ⟨crossingWallEvent ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e t ht,
      crossingWallEvent_mem_segmentWallEvents ((fun c : B.active (k + 1) =>
        h.continuousRealCharacter (B.wall c).normal)) e ht, ?_⟩
    exact (segmentEventParameter_of_mem ((fun c : B.active (k + 1) =>
      h.continuousRealCharacter (B.wall c).normal)) e T ht).trans htu.symm
  · intro _ u hu hsing
    by_cases huT : u < T
    · have hu0 : 0 < u := by
        rcases hu.eq_or_lt with rfl | hu0
        · exfalso
          obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
            (singularSupport_subset_iUnion walls hclosedW hsing)
          exact y.notMem c (by simpa only [walls, zero_smul, add_zero] using hc)
        · exact hu0
      obtain ⟨t, hti, htu, hline⟩ :=
        lineMap_eq_add_smul_of_pos_of_lt (w := vel n) hTpos hxy hu0 huT
      exact e.down.regular t (Set.Ioo_subset_Icc_self hti) (hline ▸ hsing)
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
  simp only [cutoffWallEventEvaluation_def, wallEventPropagation_def,
    d.truncationMap_refl, LieHom.bchGroupMap_id, MonoidHom.id_apply]
  exact
    (d.transition_cutoffDecoratedEvaluation_shiftedBCHAction ℒ ℳ p
      (fun n => i (ρ (p + n)))
      (fun e : WallEvent (B.active K) =>
        e.normal ((fun c : B.active K =>
        h.continuousRealCharacter (B.wall c).normal)))
      (fun e : WallEvent (B.active K) =>
        e.offset ((fun c : B.active K => (B.wall c).offset)))
      (fun e : WallEvent (B.active K) => e.2)
      (fun e : WallEvent (B.active K) => e.support ((fun c : B.active K => (B.wall c).support)))
      ((fun c : B.active K => (B.wall c).support))
      (fun _ : Unit => singularSupport ((fun c : B.active K => (B.wall c).support)))
      C Q hk (fun e : WallEvent (B.active K) => B.wallEventLabel K e) a)

end Mei.ModuleProbe
