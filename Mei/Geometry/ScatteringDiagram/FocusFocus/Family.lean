/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Decorated
public import Mei.Analysis.Convex.Sign
public import Mei.Geometry.Convex.Sweep.Degeneration

/-!
# Closed endpoint charts for decorated slab rays

Each surviving binomial index has two endpoint charts, distinguished by whether
its slab encounter is below or above the singular origin. These are disjoint
open rational polyhedra. Their closures have proper endpoint inclusions and
retain continuous paths in the compact-open topology, including terminal slab
crossings and encounters with the singular origin. On each chart the incoming
chart transition and the entire outgoing decoration are fixed.

The evaluation fibers are the actual `SlabBrokenLine`s, via
`slabBrokenLineEquiv`; overlapping endpoint charts of different binomial indices
retain their multiplicities. Closed charts use the existing sign-cell closure
and relative-interior theorems, and `Convex.backwardPath` supplies the continuous
path extension. The geometric conventions follow Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.FocusFocus

private def slabRows (n q : ℤ) : Bool → (ℝ × ℝ) →ᴬ[ℝ] ℝ :=
  fun a => if a then
    (ContinuousLinearMap.snd ℝ ℝ ℝ -
      ((q : ℝ) / n) • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
    else ((n : ℝ)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

private def slabSigns (upper : Bool) : Bool → SignType :=
  fun a => if a && upper then .pos else .neg

/-- Endpoints of a slab branch with horizontal exponent `n` and outgoing vertical
exponent `q`. The Boolean selects the upper (`true`) or lower (`false`) encounter. -/
def slabBranchDomain (n q : ℤ) (upper : Bool) : Set (ℝ × ℝ) :=
  Convex.signCell (slabRows n q) (slabSigns upper)

/-- A chart fixes the outgoing chamber and the strict sign of the crossing height. -/
@[simp]
theorem mem_slabBranchDomain (n q : ℤ) (upper : Bool) (Q : ℝ × ℝ) :
    Q ∈ slabBranchDomain n q upper ↔
      Q.1 / (n : ℝ) < 0 ∧
        if upper then 0 < Q.2 - (q : ℝ) * Q.1 / n
        else Q.2 - (q : ℝ) * Q.1 / n < 0 := by
  cases upper <;>
    simp [slabBranchDomain, Convex.mem_signCell, Bool.forall_bool, slabRows, slabSigns,
      sign_eq_neg_one_iff, sign_eq_one_iff, smul_eq_mul, div_eq_mul_inv, mul_comm,
      mul_assoc]

/-- Valid endpoints form an open subset of the endpoint plane. -/
theorem isOpen_slabBranchDomain (n q : ℤ) (upper : Bool) :
    IsOpen (slabBranchDomain n q upper) := by
  have he : slabBranchDomain n q upper =
      ⋂ a, {Q | SignType.sign (slabRows n q a Q) = slabSigns upper a} := by
    ext Q
    simp [slabBranchDomain]
  rw [he]
  apply isOpen_iInter_of_finite
  intro a
  exact (isOpen_setOf_sign_eq (by cases a <;> cases upper <;> decide)).preimage
    (slabRows n q a).continuous

/-- Every upper and lower branch chart is inhabited when the horizontal exponent
is nonzero; no coefficient assumption is involved in its geometry. -/
theorem slabBranchDomain_nonempty {n : ℤ} (hn : n ≠ 0) (q : ℤ) (upper : Bool) :
    (slabBranchDomain n q upper).Nonempty := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨(-(n : ℝ), (if upper then 1 else -1) - q), ?_⟩
  rw [mem_slabBranchDomain]
  cases upper <;> simp [hn', neg_div]

/-- The two encounter charts are disjoint, even when the outgoing exponents coincide. -/
theorem disjoint_slabBranchDomain (n q : ℤ) :
    Disjoint (slabBranchDomain n q false) (slabBranchDomain n q true) := by
  apply Set.disjoint_left.mpr
  intro Q h₀ h₁
  have h₀ := (mem_slabBranchDomain n q false Q).mp h₀
  have h₁ := (mem_slabBranchDomain n q true Q).mp h₁
  exact (not_lt_of_ge (le_of_lt h₁.2)) h₀.2

/-- The closed chart is obtained by permitting zero crossing time and zero height. -/
theorem mem_closure_slabBranchDomain {n : ℤ} (hn : n ≠ 0) (q : ℤ)
    (upper : Bool) (Q : ℝ × ℝ) :
    Q ∈ closure (slabBranchDomain n q upper) ↔
      Q.1 / (n : ℝ) ≤ 0 ∧
        if upper then 0 ≤ Q.2 - (q : ℝ) * Q.1 / n
        else Q.2 - (q : ℝ) * Q.1 / n ≤ 0 := by
  rw [slabBranchDomain, Convex.closure_signCell (slabBranchDomain_nonempty hn q upper)]
  cases upper <;>
    simp [Convex.mem_weakSignCell, Bool.forall_bool, slabRows, slabSigns,
      smul_eq_mul, div_eq_mul_inv, mul_comm, mul_assoc]

/-- The relative interior of each closed chart is exactly its valid endpoint domain. -/
@[simp]
theorem intrinsicInterior_closure_slabBranchDomain (n q : ℤ) (upper : Bool) :
    intrinsicInterior ℝ (closure (slabBranchDomain n q upper)) =
      slabBranchDomain n q upper :=
  Convex.intrinsicInterior_closure_signCell

/-- Boundary points represent terminal face crossings or singular-origin encounters. -/
theorem slabBranchDomain_boundary {n : ℤ} (hn : n ≠ 0) (q : ℤ)
    (upper : Bool) {Q : ℝ × ℝ} (hQ : Q ∈ closure (slabBranchDomain n q upper))
    (hnot : Q ∉ slabBranchDomain n q upper) :
    Q.1 = 0 ∨ Q.2 - (q : ℝ) * Q.1 / n = 0 := by
  have hw := (mem_closure_slabBranchDomain hn q upper Q).mp hQ
  have hs := (mem_slabBranchDomain n q upper Q).not.mp hnot
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw hs
  all_goals
    by_cases ht : Q.1 / (n : ℝ) = 0
    · exact Or.inl ((div_eq_zero_iff.mp ht).resolve_right hn')
    · right
      have ht' : Q.1 / (n : ℝ) < 0 := lt_of_le_of_ne hw.1 ht
      exact le_antisymm (by grind) (by grind)

section Rational

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

private theorem rational_slabRows (n q : ℤ) (a : Bool) :
    Toric.IsRationalFunctional h (slabRows n q a).toAffineMap.linear := by
  have hf : Toric.IsRationalFunctional h (LinearMap.fst ℝ ℝ ℝ) := by
    convert Toric.IsRationalFunctional.realCharacter h (LinearMap.fst ℤ ℤ ℤ) using 1
    exact h.eq_realCharacter (by intro x; simp)
  have hg : Toric.IsRationalFunctional h (LinearMap.snd ℝ ℝ ℝ) := by
    convert Toric.IsRationalFunctional.realCharacter h (LinearMap.snd ℤ ℤ ℤ) using 1
    exact h.eq_realCharacter (by intro x; simp)
  cases a
  · exact hf.smul ⟨(n : ℚ)⁻¹, by simp⟩
  · exact hg.sub (hf.smul ⟨(q : ℚ) / n, by simp⟩)

/-- Branch endpoint charts are locally closed rational-normal polyhedra for the
standard integral lattice, so they are legitimate finite semilinear charts. -/
theorem isLocallyClosedPolyhedron_slabBranchDomain (n q : ℤ) (upper : Bool) :
    IsLocallyClosedPolyhedron h (slabBranchDomain n q upper) :=
  isLocallyClosedPolyhedron_signCell _ (rational_slabRows h n q) _

end Rational

/-- The hinge extension of a branch, defined continuously for all endpoints.
It allows zero encounter time and singular encounters on the closed charts. -/
def slabBranchPath (n b q : ℤ) : C(ℝ × ℝ, C(ℝ, ℝ × ℝ)) :=
  Convex.backwardPath (fun _ : Fin 1 => ContinuousLinearMap.fst ℝ ℝ ℝ) (fun _ => 0)
    ![((n : ℝ), (q : ℝ)), ((n : ℝ), (b : ℝ))]

/-- The extended path retains the branch's two affine segments and encounter formula. -/
@[simp]
theorem slabBranchPath_apply (n b q : ℤ) (Q : ℝ × ℝ) (s : ℝ) :
    slabBranchPath n b q Q s =
      (Q.1 - s * n, Q.2 - s * q + max (Q.1 / (n : ℝ) - s) 0 * (b - q)) := by
  simp only [slabBranchPath, Convex.backwardPath_apply, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Convex.backwardParameter_succ, Convex.backwardTime_apply,
    ContinuousLinearMap.coe_fst', zero_sub, neg_div, sub_neg_eq_add, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Finset.sum_singleton, Fin.castSucc_zero,
    Convex.backwardParameter_zero, Convex.backwardPoint_zero, ContinuousAffineMap.coe_id,
    id_eq, Matrix.cons_val_zero, zero_add, Prod.mk_sub_mk, sub_self, Prod.smul_mk,
    smul_eq_mul, mul_comm, zero_mul]
  apply Prod.ext <;> dsimp <;> ring

/-- The closed crossing path at a terminal slab point is the incoming affine
half-line. Its outgoing degree has disappeared because the final segment has
length zero. This includes unchanged-direction crossings. -/
@[simp↓]
theorem slabBranchPath_terminal (n b q : ℤ) (v s : ℝ) (hs : s ≤ 0) :
    slabBranchPath n b q (0, v) s = (-(s * n), v - s * b) := by
  rw [slabBranchPath_apply]
  simp only [zero_div, zero_sub, max_eq_left (neg_nonneg.mpr hs)]
  congr 1
  ring

/-- On its valid endpoint domain the extended path is the existing finite affine ray. -/
theorem slabBranchPath_eq_slabBranch (n b q : ℤ) (Q : ℝ × ℝ)
    (hQ : Q.1 / (n : ℝ) < 0) :
    slabBranchPath n b q Q = (slabBranch n b q Q hQ).toContinuousMap := by
  apply ContinuousMap.ext
  intro s
  rw [slabBranchPath_apply, FiniteAffineRay.toContinuousMap_apply, slabBranch_apply]

/-- Converging endpoints give compact-open convergence of branch paths, including
limits on the terminal-face and singular-height boundaries of the endpoint charts. -/
theorem tendsto_slabBranch {A : Type*} {l : Filter A} (n b q : ℤ)
    {Q : A → ℝ × ℝ} {Q₀ : ℝ × ℝ} (hQ : Tendsto Q l (𝓝 Q₀))
    (hopp : ∀ a, (Q a).1 / (n : ℝ) < 0) :
    Tendsto (fun a => (slabBranch n b q (Q a) (hopp a)).toContinuousMap) l
      (𝓝 (slabBranchPath n b q Q₀)) := by
  simpa only [← slabBranchPath_eq_slabBranch, Function.comp_def] using
    (slabBranchPath n b q).continuous.continuousAt.tendsto.comp hQ

/-- Nonpositive encounter time suffices for the closed-chart path to end at `Q`. -/
theorem slabBranchPath_apply_zero (n b q : ℤ) (Q : ℝ × ℝ)
    (hQ : Q.1 / (n : ℝ) ≤ 0) : slabBranchPath n b q Q 0 = Q := by
  simp [slabBranchPath_apply, max_eq_right hQ]

/-- Every closed-chart path still meets the slab at its affine encounter time;
when that time is zero this is the terminal-face degeneration. -/
theorem slabBranchPath_crossing {n : ℤ} (hn : n ≠ 0) (b q : ℤ) (Q : ℝ × ℝ) :
    slabBranchPath n b q Q (Q.1 / (n : ℝ)) =
      (0, Q.2 - (q : ℝ) * Q.1 / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [slabBranchPath_apply, sub_self, max_self, zero_mul, add_zero]
  apply Prod.ext
  · simp [hn']
  · dsimp
    ring

section Decorated

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ)

/-- The finite chart labels: a surviving binomial coefficient and an upper/lower
encounter choice. Distinct binomial indices remain distinct even on overlapping domains. -/
abbrev SlabChartIndex :=
  {j : Fin (n.natAbs + 1) // c * t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0} × Bool

open Classical in
/-- Chart membership selects exactly the surviving nonsingular binomial indices.
For each such index there is precisely one choice of upper or lower chart. -/
def slabChartIndexEquiv (Q : ℝ × ℝ) (hQ : Q.1 / (n : ℝ) < 0) :
    {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2} ≃
      SlabBranchIndex t c n b Q where
  toFun α := ⟨α.val.1.val, α.val.1.property, by
    have hs := (mem_slabBranchDomain _ _ _ _).mp α.property
    cases h : α.val.2 <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hs
    · exact hs.2.ne
    · exact hs.2.ne'⟩
  invFun j := ⟨(⟨j.val, j.property.1⟩,
    decide (0 < Q.2 - ((b + j.val.val : ℤ) : ℝ) * Q.1 / n)), by
      rw [mem_slabBranchDomain]
      refine ⟨hQ, ?_⟩
      split_ifs with hpos
      · exact of_decide_eq_true hpos
      · exact lt_of_le_of_ne (le_of_not_gt (by simpa using hpos)) j.property.2⟩
  left_inv α := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hs := (mem_slabBranchDomain _ _ _ _).mp α.property
      cases h : α.val.2 <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      · exact decide_eq_false (not_lt_of_ge hs.2.le)
      · exact decide_eq_true hs.2
  right_inv _ := rfl

/-- The chart index recovers the original binomial index. -/
@[simp]
theorem slabChartIndexEquiv_apply_val (Q : ℝ × ℝ) (hQ : Q.1 / (n : ℝ) < 0)
    (α : {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2}) :
    (slabChartIndexEquiv t c n b Q hQ α).val = α.val.1.val := (rfl)

open Classical in
/-- The inverse chart enumeration selects the upper chart exactly for positive
crossing height, retaining the original surviving binomial index. -/
@[simp]
theorem slabChartIndexEquiv_symm_apply (Q : ℝ × ℝ) (hQ : Q.1 / (n : ℝ) < 0)
    (j : SlabBranchIndex t c n b Q) :
    ((slabChartIndexEquiv t c n b Q hQ).symm j).val =
      (⟨j.val, j.property.1⟩,
        decide (0 < Q.2 - ((b + j.val.val : ℤ) : ℝ) * Q.1 / n)) := (rfl)

/-- The endpoint fiber of the finite chart family is precisely the actual decorated
slab-ray fiber, preserving the binomial index and its whole homogeneous decoration. -/
def slabChartEquiv (Q : ℝ × ℝ) :
    {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2} ≃
      SlabBrokenLine t c n b Q where
  toFun α :=
    let hQ := ((mem_slabBranchDomain _ _ _ _).mp α.property).1
    slabBrokenLineEquiv t c n b Q hQ (slabChartIndexEquiv t c n b Q hQ α)
  invFun β := (slabChartIndexEquiv t c n b Q β.opposite).symm
    ((slabBrokenLineEquiv t c n b Q β.opposite).symm β)
  left_inv α :=
    let hQ := ((mem_slabBranchDomain _ _ _ _).mp α.property).1
    ((slabChartIndexEquiv t c n b Q hQ).trans
      (slabBrokenLineEquiv t c n b Q hQ)).symm_apply_apply α
  right_inv β :=
    ((slabChartIndexEquiv t c n b Q β.opposite).trans
      (slabBrokenLineEquiv t c n b Q β.opposite)).apply_symm_apply β

/-- The fiber equivalence preserves the binomial index in its outgoing degree. -/
@[simp]
theorem degree_slabChartEquiv (Q : ℝ × ℝ)
    (α : {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2}) :
    (slabChartEquiv t c n b Q α).degree =
      (-(n.natAbs : ℤ), b + α.val.1.val.val) := by
  simp only [slabChartEquiv, Equiv.coe_fn_mk, slabBrokenLineEquiv_apply,
    degree_slabBrokenLine, slabChartIndexEquiv_apply_val]

/-- The inverse fiber equivalence recovers the binomial index and its encounter
sign using the decorated ray's opposite-chamber condition. -/
@[simp]
theorem slabChartEquiv_symm_apply (Q : ℝ × ℝ) (β : SlabBrokenLine t c n b Q) :
    (slabChartEquiv t c n b Q).symm β =
      (slabChartIndexEquiv t c n b Q β.opposite).symm
        ((slabBrokenLineEquiv t c n b Q β.opposite).symm β) := (rfl)

/-- Decorations are constant throughout each chart, over arbitrary coefficient rings. -/
@[simp]
theorem decoration_slabChartEquiv (Q : ℝ × ℝ)
    (α : {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2}) :
    (slabChartEquiv t c n b Q α).decoration =
      AddMonoidAlgebra.single (-(n.natAbs : ℤ), b + α.val.1.val.val)
        (c * t ^ n.natAbs * (n.natAbs.choose α.val.1.val.val : R)) := by
  simp only [slabChartEquiv, Equiv.coe_fn_mk, slabBrokenLineEquiv_apply,
    decoration_slabBrokenLine, slabChartIndexEquiv_apply_val]

/-- Throughout an upper or lower chart, one fixed incoming exponent gives the
continuous closed-chart path. Thus the chart transition does not change in a limit. -/
theorem ray_slabChartEquiv (Q : ℝ × ℝ)
    (α : {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2}) :
    (slabChartEquiv t c n b Q α).ray.toContinuousMap =
      slabBranchPath n (if α.val.2 then b + n.natAbs else b)
        (b + α.val.1.val.val) Q := by
  simp only [slabChartEquiv, Equiv.coe_fn_mk, slabBrokenLineEquiv_apply,
    ray_slabBrokenLine, slabChartIndexEquiv_apply_val]
  rw [← slabBranchPath_eq_slabBranch]
  congr 2
  have hs := (mem_slabBranchDomain _ _ _ _).mp α.property
  cases h : α.val.2 <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hs ⊢
  · exact slabIncomingExponent_of_neg _ _ _ _ hs.2
  · exact slabIncomingExponent_of_pos _ _ _ _ hs.2

open Classical in
/-- Weighted evaluation is the sum of the fixed decorations on the admitted charts.
No genericity assumption is required; singular branches are absent from the fiber. -/
theorem slabWeightedEvaluation_eq_sum_charts (Q : ℝ × ℝ) :
    slabWeightedEvaluation t c n b Q =
      ∑ α : {α : SlabChartIndex t c n // Q ∈ slabBranchDomain n (b + α.1.val.val) α.2},
        AddMonoidAlgebra.single (-(n.natAbs : ℤ), b + α.val.1.val.val)
          (c * t ^ n.natAbs * (n.natAbs.choose α.val.1.val.val : R)) := by
  classical
  rw [slabWeightedEvaluation_def]
  exact (Fintype.sum_equiv (slabChartEquiv t c n b Q) _ _
    (fun α => (decoration_slabChartEquiv t c n b Q α).symm)).symm

end Decorated

end Mei.FocusFocus
