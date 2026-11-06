/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Terminal
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family.Theta

/-!
# Incident resolutions of the complete focus-focus endpoint family

At a regular slab point, a complete chart is incident exactly when its closed
endpoint domain contains that point. Selecting the side of the endpoint then
exhausts the actual common-family fiber throughout the uniform terminal
neighborhood. This is a geometric selection of histories, rather than an
equality of unrestricted transfer words. Incoming, crossing and constant sectors
retain their original labels and whole weights.

The surviving history set may change with the input coefficient. Thus the
expansion is pointwise in that coefficient; linearity of the total resolution
comes from its common theta lift, not a claim of uniform surviving support.

All outgoing binomial branches in an incident crossing resolution collapse to
the same incoming half-line. Its developed vertical exponent is `b` below the
origin and `b + |n|` above it; these incoming records are not identified. The
incidence-selected weighted sum has the existing total theta lift. This supplies
the regular terminal resolutions consumed by matching, not a singular-origin
resolution or a global sheaf section. The geometric interpretation follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

namespace Mei.FocusFocus

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ)

/-- The chamber side selected by a complete chart; constant histories occur on
both sides. This retains the chart's original developed incoming record. -/
def slabThetaChartOnSide (α : SlabThetaChartIndex t c n b) (right : Bool) : Prop :=
  match α with
  | .inl j => j.val = right
  | .inr (.inl _) => if right then n < 0 else 0 < n
  | .inr (.inr _) => True

@[simp]
theorem slabThetaChartOnSide_incoming (j : IncomingSlabChartIndex c n b) (right : Bool) :
    slabThetaChartOnSide t c n b (.inl j) right ↔ j.val = right := Iff.rfl

@[simp]
theorem slabThetaChartOnSide_crossing (j : SlabChartIndex t c n) (right : Bool) :
    slabThetaChartOnSide t c n b (.inr (.inl j)) right ↔
      if right then n < 0 else 0 < n := Iff.rfl

@[simp]
theorem slabThetaChartOnSide_constant (u : Unit) (right : Bool) :
    slabThetaChartOnSide t c n b (.inr (.inr u)) right := trivial

/-- Complete histories in one adjacent resolution at a slab point. Incidence
uses the actual closed chart domain; a zero decoration creates no extra ray. -/
abbrev SlabThetaTerminalResolution (v : ℝ) (right : Bool) :=
  {α : SlabThetaChartIndex t c n b //
    (0, v) ∈ closure (slabThetaChartDomain t c n b α) ∧
      slabThetaChartOnSide t c n b α right}

/-- At a regular slab point exactly one of the upper/lower crossing charts is
incident, and a zero horizontal degree supplies no crossing chart. -/
theorem slabThetaChart_incident_crossing (j : SlabChartIndex t c n)
    {v : ℝ} (hv : v ≠ 0) :
    (0, v) ∈ closure (slabThetaChartDomain t c n b (.inr (.inl j))) ↔
      n ≠ 0 ∧ j.2 = decide (0 < v) := by
  rw [slabThetaChartDomain_crossing]
  by_cases hn : n = 0
  · have hd : slabBranchDomain n (b + j.1.val.val) j.2 = ∅ := by
      ext Q
      simp [hn]
    rw [hd]
    simp [hn]
  · rw [mem_closure_slabBranchDomain hn]
    simp only [zero_div, le_refl, mul_zero, sub_zero, true_and]
    cases hj : j.2
    · simp only [Bool.false_eq_true, ↓reduceIte, false_eq_decide_iff, not_lt]
      exact ⟨fun h => ⟨hn, h⟩, fun h => h.2⟩
    · simp only [↓reduceIte, true_eq_decide_iff]
      exact ⟨fun h => ⟨hn, lt_of_le_of_ne h (Ne.symm hv)⟩, fun h => h.2.le⟩

/-- Constant histories meet the terminal point exactly when their original
domain is nonempty. -/
@[simp]
theorem slabThetaChart_incident_constant (u : Unit) (v : ℝ) :
    (0, v) ∈ closure (slabThetaChartDomain t c n b (.inr (.inr u))) ↔
      (n, b) = 0 ∧ c ≠ 0 := by
  classical
  by_cases hz : (n, b) = 0 ∧ c ≠ 0
  · have hd : slabThetaChartDomain t c n b (.inr (.inr u)) = univ := by
      ext Q
      simp only [mem_slabThetaChartDomain_constant, mem_univ, iff_true]
      exact hz
    rw [hd]
    simp [hz]
  · have hd : slabThetaChartDomain t c n b (.inr (.inr u)) = ∅ := by
      ext Q
      simp only [mem_slabThetaChartDomain_constant, mem_empty_iff_false, iff_false]
      exact hz
    rw [hd]
    simp only [closure_empty, mem_empty_iff_false, false_iff]
    exact hz

/-- The uniform terminal neighborhood gives an exact adjacent resolution:
membership is closed-chart incidence together with the chosen chamber side.
No genericity, noncancellation or branchwise face lift is assumed. -/
theorem mem_slabThetaChartDomain_iff_terminal_resolution
    (α : SlabThetaChartIndex t c n b) {v : ℝ}
    {Q : ℝ × ℝ} (hQ : Q ∈ slabTerminalDomain n b v)
    (right : Bool) (hside : Q ∈ incomingSlabDomain right) :
    Q ∈ slabThetaChartDomain t c n b α ↔
      (0, v) ∈ closure (slabThetaChartDomain t c n b α) ∧
        slabThetaChartOnSide t c n b α right := by
  have hp := (mem_slabTerminalDomain n b v Q).mp hQ ⟨0, by omega⟩
  have hv : v ≠ 0 := left_ne_zero_of_mul hp.ne'
  rcases α with j | j | u
  · rw [and_iff_right (by simp :
      (0, v) ∈ closure (slabThetaChartDomain t c n b (.inl j)))]
    simp only [slabThetaChartDomain_incoming, slabThetaChartOnSide,
      mem_incomingSlabDomain] at hside ⊢
    cases hj : j.val <;> cases right <;> simp_all <;> linarith
  · rw [slabThetaChart_incident_crossing t c n b j hv,
      slabThetaChartDomain_crossing,
      mem_slabBranchDomain_iff_of_mem_slabTerminalDomain hQ j.1.val j.2]
    simp only [slabThetaChartOnSide, mem_incomingSlabDomain] at hside ⊢
    have he : Q.1 / (n : ℝ) < 0 ↔ if right then n < 0 else 0 < n := by
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hside ⊢
      · rw [div_neg_iff]
        constructor
        · intro h
          rcases h with h | h
          · linarith [h.1]
          · exact_mod_cast h.2
        · intro h
          exact Or.inr ⟨hside, by exact_mod_cast h⟩
      · rw [div_neg_iff]
        constructor
        · intro h
          rcases h with h | h
          · exact_mod_cast h.2
          · linarith [h.1]
        · intro h
          exact Or.inl ⟨hside, by exact_mod_cast h⟩
    rw [he]
    constructor
    · rintro ⟨hs, hj⟩
      refine ⟨⟨?_, hj⟩, hs⟩
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hs <;> omega
    · rintro ⟨⟨_, hj⟩, hs⟩
      exact ⟨hs, hj⟩
  · simp only [mem_slabThetaChartDomain_constant, slabThetaChart_incident_constant,
      slabThetaChartOnSide, and_true]

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The actual common-family fiber is precisely the incident resolution on
the chosen side, retaining the complete chart label rather than its image. -/
def slabThetaTerminalResolutionEquiv {v : ℝ}
    {Q : ℝ × ℝ} (hQ : Q ∈ slabTerminalDomain n b v)
    (right : Bool) (hside : Q ∈ incomingSlabDomain right) :
    (slabThetaFamily t c n b h).fiber Q ≃
      SlabThetaTerminalResolution t c n b v right :=
  (Equiv.cast (congrArg (fun F => F.fiber Q) (slabThetaFamily_def t c n b h))).trans
    ((FiniteSemilinearFamily.fiberOfDomainsEquiv _ _ Q).trans
      (Equiv.subtypeEquivRight fun α =>
        mem_slabThetaChartDomain_iff_terminal_resolution t c n b α hQ right hside))

/-- The forward resolution comparison preserves the complete label. -/
@[simp]
theorem slabThetaTerminalResolutionEquiv_apply_val {v : ℝ}
    {Q : ℝ × ℝ} (hQ : Q ∈ slabTerminalDomain n b v)
    (right : Bool) (hside : Q ∈ incomingSlabDomain right)
    (z : (slabThetaFamily t c n b h).fiber Q) :
    (slabThetaTerminalResolutionEquiv t c n b h hQ right hside z).val = z.1 := by
  simp only [slabThetaTerminalResolutionEquiv, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply, FiniteSemilinearFamily.fiberOfDomainsEquiv_apply_val,
    Equiv.cast_apply]
  exact FiniteSemilinearFamily.fiber_cast_fst (slabThetaFamily_def t c n b h) Q z

/-- Reconstructing an actual fiber from its incident history retains its label. -/
@[simp]
theorem slabThetaTerminalResolutionEquiv_symm_apply_fst {v : ℝ}
    {Q : ℝ × ℝ} (hQ : Q ∈ slabTerminalDomain n b v)
    (right : Bool) (hside : Q ∈ incomingSlabDomain right)
    (z : SlabThetaTerminalResolution t c n b v right) :
    ((slabThetaTerminalResolutionEquiv t c n b h hQ right hside).symm z).1 =
      z.val := by
  simp only [slabThetaTerminalResolutionEquiv, Equiv.symm_trans_apply,
    ← Equiv.cast_symm, Equiv.cast_apply]
  rw [FiniteSemilinearFamily.fiber_cast_fst (slabThetaFamily_def t c n b h).symm]
  simp only [FiniteSemilinearFamily.fiberOfDomainsEquiv_symm_apply_fst,
    Equiv.subtypeEquivRight_symm_apply]

/-- The exact local-resolution expansion sums whole weights of geometrically
incident histories. The index set is independent of the endpoint inside the
chosen side of the uniform terminal neighborhood. -/
theorem slabThetaFamily_weightedEvaluation_eq_terminal_resolution
    {v : ℝ} {Q : ℝ × ℝ} (hQ : Q ∈ slabTerminalDomain n b v)
    (right : Bool) (hside : Q ∈ incomingSlabDomain right) :
    (slabThetaFamily t c n b h).weightedEvaluation (slabThetaChartWeight t c n b) Q =
      let := Fintype.ofFinite (SlabThetaTerminalResolution t c n b v right)
      ∑ z : SlabThetaTerminalResolution t c n b v right,
        slabThetaChartWeight t c n b z.val := by
  classical
  let := Fintype.ofFinite ((slabThetaFamily t c n b h).fiber Q)
  let := Fintype.ofFinite (SlabThetaTerminalResolution t c n b v right)
  rw [FiniteSemilinearFamily.weightedEvaluation_def]
  exact Fintype.sum_equiv
    (slabThetaTerminalResolutionEquiv t c n b h hQ right hside) _ _
    (fun z => by rw [slabThetaTerminalResolutionEquiv_apply_val])

/-- The incident weighted resolution on each side is the corresponding chamber
image of the common theta lift. This is a statement about the geometrically
selected histories, not the unrestricted binomial expansion. -/
theorem slabThetaTerminalResolution_weightedSum {v : ℝ} (hv : v ≠ 0)
    (right : Bool) :
    (let := Fintype.ofFinite (SlabThetaTerminalResolution t c n b v right)
     ∑ z : SlabThetaTerminalResolution t c n b v right,
       slabThetaChartWeight t c n b z.val) =
      (if right then Mei.NodeAlgebra.exponentRightMap
        (_root_.LaurentPolynomial.C t * (1 + _root_.LaurentPolynomial.T 1)) else
        Mei.NodeAlgebra.exponentLeftMap
          (_root_.LaurentPolynomial.C t * (1 + _root_.LaurentPolynomial.T 1)))
        (c • theta t n b) := by
  classical
  have expand (Q : ℝ × ℝ) (hQ : Q ∈ slabTerminalDomain n b v)
      (side : Bool) (hs : Q ∈ incomingSlabDomain side) :
      (let := Fintype.ofFinite (SlabThetaTerminalResolution t c n b v side)
       ∑ z : SlabThetaTerminalResolution t c n b v side,
         slabThetaChartWeight t c n b z.val) = slabThetaEvaluation t c n b Q := by
    let := Fintype.ofFinite (SlabThetaTerminalResolution t c n b v side)
    let := Fintype.ofFinite
      {α : SlabThetaChartIndex t c n b // Q ∈ slabThetaChartDomain t c n b α}
    rw [slabThetaEvaluation_eq_sum_charts]
    exact (Fintype.sum_equiv
      (Equiv.subtypeEquivRight fun α =>
        mem_slabThetaChartDomain_iff_terminal_resolution t c n b α hQ side hs)
      (fun α => slabThetaChartWeight t c n b α.val)
      (fun α => slabThetaChartWeight t c n b α.val) (fun _ => rfl)).symm
  obtain ⟨L, U, hL, hU, hsL, hsU⟩ :=
    slabTerminalFiniteDomain_meets_chambers ({()} : Finset Unit)
      (fun _ => n) (fun _ => b) hv
  have hL' : L ∈ slabTerminalDomain n b v :=
    (mem_slabTerminalFiniteDomain _ _ _ v L).mp hL () (by simp)
  have hU' : U ∈ slabTerminalDomain n b v :=
    (mem_slabTerminalFiniteDomain _ _ _ v U).mp hU () (by simp)
  cases right
  · rw [expand L hL' false (by simpa using hsL)]
    exact slabThetaEvaluation_eq_exponentLeftMap t c n b L hsL
      (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero hL' j)
  · rw [expand U hU' true (by simpa using hsU)]
    exact slabThetaEvaluation_eq_exponentRightMap t c n b U hsU
      (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero hU' j)

/-- Incident crossing histories above or below a regular slab point all have
the same developed incoming exponent, even when their outgoing degrees differ. -/
theorem slabThetaChartIncomingExponent_of_incident_crossing
    (j : SlabChartIndex t c n) {v : ℝ} (hv : v ≠ 0)
    (hj : (0, v) ∈ closure (slabThetaChartDomain t c n b (.inr (.inl j)))) :
    slabThetaChartIncomingExponent t c n b (.inr (.inl j)) =
      (n, if 0 < v then b + n.natAbs else b) := by
  rw [slabThetaChartIncomingExponent_crossing,
    (slabThetaChart_incident_crossing t c n b j hv).mp hj |>.2]
  simp

end Mei.FocusFocus
