/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Singular
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family.Theta

/-!
# Singular resolutions of the common focus-focus family

At a singular-height event away from the slab, the closed theta charts incident
to the endpoint determine two local resolutions. The chart of the singular
binomial index is selected by the side of a transverse vertical interval;
all other incident charts keep their encounter sign. These selections exhaust
the actual common-family fibers throughout one coefficient-independent interval.
Their weighted sums agree, including when torsion or nilpotents remove branches.

The comparison retains complete chart labels, weights and incoming paths. The
closed paths of the changing charts encounter the singular origin; no
admissibility is asserted for these boundary paths. The comparison uses
`slabSingular_height_sign` and `slabThetaFamily`, with their existing
whole-component decorations and closed path extensions.

The local-resolution interpretation follows Gross–Siebert, *An Invitation to
Toric Degenerations*, §§2.2–2.3 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set

namespace Mei.FocusFocus

variable {Q : ℝ × ℝ} {j : ℕ}

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ)

/-- The incident complete charts selected on one side of a singular-height
event. Only the singular index changes its upper/lower chart. Incoming and
constant charts do not occur in the opposite chamber. -/
def slabSingularResolutionCharts (Q : ℝ × ℝ) (j : ℕ) (positive : Bool) :
    Set (SlabThetaChartIndex t c n b) := {α | match α with
  | .inl _ => False
  | .inr (.inl α) =>
      Q ∈ closure (slabThetaChartDomain t c n b (.inr (.inl α))) ∧
        (α.1.val.val = j → α.2 = positive)
  | .inr (.inr _) => False}

@[simp]
theorem notMem_slabSingularResolutionCharts_incoming (Q : ℝ × ℝ) (j : ℕ)
    (positive : Bool) (α : IncomingSlabChartIndex c n b) :
    .inl α ∉ slabSingularResolutionCharts t c n b Q j positive := by
  simp [slabSingularResolutionCharts]

@[simp]
theorem mem_slabSingularResolutionCharts_crossing (Q : ℝ × ℝ) (j : ℕ)
    (positive : Bool) (α : SlabChartIndex t c n) :
    .inr (.inl α) ∈ slabSingularResolutionCharts t c n b Q j positive ↔
      Q ∈ closure (slabBranchDomain n (b + α.1.val.val) α.2) ∧
        (α.1.val.val = j → α.2 = positive) := by
  simp [slabSingularResolutionCharts]

@[simp]
theorem notMem_slabSingularResolutionCharts_constant (Q : ℝ × ℝ) (j : ℕ)
    (positive : Bool) (u : Unit) :
    .inr (.inr u) ∉ slabSingularResolutionCharts t c n b Q j positive := by
  simp [slabSingularResolutionCharts]

/-- Every selected complete chart is geometrically incident to the event center. -/
theorem mem_closure_slabThetaChartDomain_of_mem_slabSingularResolutionCharts
    (Q : ℝ × ℝ) (j : ℕ) (positive : Bool) {α : SlabThetaChartIndex t c n b}
    (hα : α ∈ slabSingularResolutionCharts t c n b Q j positive) :
    Q ∈ closure (slabThetaChartDomain t c n b α) := by
  rcases α with α | α | α
  · exact hα.elim
  · exact hα.1
  · exact hα.elim

variable {n b}

/-- A short punctured transverse interval selects exactly the complete incident
charts of the corresponding resolution. The bound works for every coefficient
and every surviving binomial branch at once. -/
theorem mem_slabThetaChartDomain_singular_iff
    (hQ : Q.1 / (n : ℝ) < 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    {s : ℝ} (hs : |s| < -(Q.1 / (n : ℝ))) (hs₀ : s ≠ 0)
    (α : SlabThetaChartIndex t c n b) :
    (Q.1, Q.2 + s) ∈ slabThetaChartDomain t c n b α ↔
      α ∈ slabSingularResolutionCharts t c n b Q j (decide (0 < s)) := by
  have hn : n ≠ 0 := by
    intro hn
    simp [hn] at hQ
  rcases α with α | α | α
  · simp only [slabThetaChartDomain_incoming, mem_incomingSlabDomain,
      notMem_slabSingularResolutionCharts_incoming, iff_false]
    have ha := α.property.2.2
    have hm : Q.1 * (n : ℝ) < 0 := (div_neg_iff.mp hQ).elim
      (fun h => mul_neg_of_pos_of_neg h.1 h.2)
      (fun h => mul_neg_of_neg_of_pos h.1 h.2)
    cases he : α.val <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at ha ⊢
    · have ha' : (n : ℝ) ≤ 0 := by exact_mod_cast ha
      intro hx
      exact (not_le_of_gt hm) (mul_nonneg_of_nonpos_of_nonpos hx.le ha')
    · have ha' : 0 ≤ (n : ℝ) := by exact_mod_cast ha
      intro hx
      exact (not_le_of_gt hm) (mul_nonneg hx.le ha')
  · rw [slabThetaChartDomain_crossing, mem_slabBranchDomain_singular hQ hj hs,
      mem_slabSingularResolutionCharts_crossing,
      mem_closure_slabBranchDomain_singular hQ hj]
    cases α.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      by_cases hp : 0 < s
      · have hm : ¬s < 0 := not_lt_of_ge hp.le
        simp [hp, hm]; omega
      · have hm : s < 0 := lt_of_le_of_ne (le_of_not_gt hp) hs₀
        simp [hp, hm]; omega
  · simp [hn]

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The selected incident charts are precisely the common-family fiber at a
nearby endpoint. Thus selection retains all global incoming records, rather
than constructing a new local incoming problem. -/
def slabSingularFamilyFiberEquiv
    (hQ : Q.1 / (n : ℝ) < 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    {s : ℝ} (hs : |s| < -(Q.1 / (n : ℝ))) (hs₀ : s ≠ 0) :
    slabSingularResolutionCharts t c n b Q j (decide (0 < s)) ≃
      (slabThetaFamily t c n b h).fiber (Q.1, Q.2 + s) :=
  (Equiv.subtypeEquivRight fun α =>
    (mem_slabThetaChartDomain_singular_iff t c hQ hj hs hs₀ α).symm).trans
    (slabThetaFamilyChartFiberEquiv t c n b h (Q.1, Q.2 + s))

/-- The exact fiber comparison preserves the entire complete chart label. -/
@[simp]
theorem slabSingularFamilyFiberEquiv_fst
    (hQ : Q.1 / (n : ℝ) < 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    {s : ℝ} (hs : |s| < -(Q.1 / (n : ℝ))) (hs₀ : s ≠ 0)
    (α : slabSingularResolutionCharts t c n b Q j (decide (0 < s))) :
    (slabSingularFamilyFiberEquiv t c h hQ hj hs hs₀ α).1 = α.val := by
  simp [slabSingularFamilyFiberEquiv]

open Classical in
/-- The finite sum of the selected incident weights is the actual common-family
evaluation throughout the punctured transverse interval. -/
theorem sum_slabSingularResolutionCharts_eq_weightedEvaluation
    (hQ : Q.1 / (n : ℝ) < 0)
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0)
    {s : ℝ} (hs : |s| < -(Q.1 / (n : ℝ))) (hs₀ : s ≠ 0) :
    (∑ α : SlabThetaChartIndex t c n b,
        if α ∈ slabSingularResolutionCharts t c n b Q j (decide (0 < s))
        then slabThetaChartWeight t c n b α else 0) =
      (slabThetaFamily t c n b h).weightedEvaluation (slabThetaChartWeight t c n b)
        (Q.1, Q.2 + s) := by
  simp only [slabThetaFamily_def, FiniteSemilinearFamily.weightedEvaluation_ofDomains]
  apply Finset.sum_congr (by ext; simp)
  intro α _
  rw [mem_slabThetaChartDomain_singular_iff t c hQ hj hs hs₀]

open Classical in
/-- The two geometrically selected local resolutions of the common theta
family have equal total weights at a singular-height event. This is an equality
of whole decorations, with all binomial multiplicities retained. -/
theorem sum_slabSingularResolutionCharts_false_eq_true
    (hj : Q.2 - ((b + j : ℤ) : ℝ) * Q.1 / n = 0) :
    (∑ α : SlabThetaChartIndex t c n b,
        if α ∈ slabSingularResolutionCharts t c n b Q j false
        then slabThetaChartWeight t c n b α else 0) =
    (∑ α : SlabThetaChartIndex t c n b,
        if α ∈ slabSingularResolutionCharts t c n b Q j true
        then slabThetaChartWeight t c n b α else 0) := by
  classical
  have hP : Q ∈ closure (slabBranchDomain n (b + j) false) ↔
      Q ∈ closure (slabBranchDomain n (b + j) true) := by
    by_cases hn : n = 0
    · have h0 : ∀ u, slabBranchDomain n (b + j) u = ∅ := fun u => by
        ext; simp [hn]
      simp [h0]
    · rw [mem_closure_slabBranchDomain hn, mem_closure_slabBranchDomain hn]
      simp only [Bool.false_eq_true, ↓reduceIte, hj, le_refl, and_true]
  simp only [Fintype.sum_sum_type,
    notMem_slabSingularResolutionCharts_incoming, notMem_slabSingularResolutionCharts_constant,
    ite_false, Finset.sum_const_zero, add_zero, zero_add]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fintype.sum_bool, mem_slabSingularResolutionCharts_crossing,
    slabThetaChartWeight_crossing, Bool.false_eq_true]
  by_cases hl : l.val.val = j
  · simp [hl, hP]
  · simp [hl]

end Mei.FocusFocus
