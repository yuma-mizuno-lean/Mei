/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Incoming.Basic
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family

/-!
# Closed charts for incoming focus-focus rays

The incoming-chamber evaluation fibers have finite closed endpoint charts.
For a nonzero horizontal exponent there is one chart, in its incoming chamber;
for an invariant vertical exponent there are two, one in each chamber. Zero
coefficients and zero spatial degree admit no charts. Each chart carries the
unique actual `IncomingSlabBrokenLine`, with unchanged monomial decoration.

The valid domains are open rational half-planes, the relative interiors of their
closed half-planes. Endpoint inclusion on each closure is proper. The continuous
path extension is the straight specialization of `slabBranchPath`; limits at the
slab retain the whole incoming half-line, including its direction and endpoint.
Boundary paths may meet the singular origin or lie on the slab in the vertical
case. They are not asserted to be nonsingular broken lines.

We use the incoming-ray classification, sign-cell closure and rationality, and
the compact-open continuous family `slabBranchPath`. The geometric conventions
follow Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties
with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.FocusFocus

/-- The endpoint chart in the right (`true`) or left (`false`) chamber. -/
def incomingSlabDomain (right : Bool) : Set (ℝ × ℝ) :=
  Convex.signCell (fun _ : Unit =>
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)
    (fun _ => if right then .pos else .neg)

/-- Valid incoming endpoints lie strictly on the selected side of the slab. -/
@[simp]
theorem mem_incomingSlabDomain (right : Bool) (Q : ℝ × ℝ) :
    Q ∈ incomingSlabDomain right ↔ if right then 0 < Q.1 else Q.1 < 0 := by
  cases right <;> simp [incomingSlabDomain, Convex.mem_signCell,
    sign_eq_neg_one_iff, sign_eq_one_iff]

/-- Both geometric chamber charts are inhabited, independently of decorations. -/
theorem incomingSlabDomain_nonempty (right : Bool) :
    (incomingSlabDomain right).Nonempty := by
  cases right
  · exact ⟨(-1, 0), by simp⟩
  · exact ⟨(1, 0), by simp⟩

/-- The incoming chart has no endpoint boundary away from the slab. -/
theorem isOpen_incomingSlabDomain (right : Bool) : IsOpen (incomingSlabDomain right) := by
  have he : incomingSlabDomain right =
      {Q : ℝ × ℝ | if right then 0 < Q.1 else Q.1 < 0} := by
    ext Q
    exact mem_incomingSlabDomain right Q
  rw [he]
  cases right
  · exact isOpen_lt continuous_fst continuous_const
  · exact isOpen_lt continuous_const continuous_fst

/-- The closed endpoint chart permits the terminal point to reach the slab. -/
@[simp]
theorem mem_closure_incomingSlabDomain (right : Bool) (Q : ℝ × ℝ) :
    Q ∈ closure (incomingSlabDomain right) ↔ if right then 0 ≤ Q.1 else Q.1 ≤ 0 := by
  rw [incomingSlabDomain, Convex.closure_signCell (incomingSlabDomain_nonempty right)]
  cases right <;> simp [Convex.mem_weakSignCell]

/-- Valid endpoints are precisely the relative interior of each closed chart. -/
@[simp]
theorem intrinsicInterior_closure_incomingSlabDomain (right : Bool) :
    intrinsicInterior ℝ (closure (incomingSlabDomain right)) = incomingSlabDomain right :=
  Convex.intrinsicInterior_closure_signCell

/-- All endpoint degenerations of incoming charts occur on the slab. -/
theorem incomingSlabDomain_boundary (right : Bool) {Q : ℝ × ℝ}
    (hQ : Q ∈ closure (incomingSlabDomain right)) (hnot : Q ∉ incomingSlabDomain right) :
    Q.1 = 0 := by
  cases right <;> simp only [mem_closure_incomingSlabDomain, mem_incomingSlabDomain,
    Bool.false_eq_true, ↓reduceIte, not_lt] at hQ hnot
  · exact le_antisymm hQ hnot
  · exact le_antisymm hnot hQ

section Rational

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- Incoming chamber charts have rational normals for the standard plane lattice. -/
theorem isLocallyClosedPolyhedron_incomingSlabDomain (right : Bool) :
    IsLocallyClosedPolyhedron h (incomingSlabDomain right) := by
  have hf : Toric.IsRationalFunctional h (LinearMap.fst ℝ ℝ ℝ) := by
    convert Toric.IsRationalFunctional.realCharacter h (LinearMap.fst ℤ ℤ ℤ) using 1
    exact h.eq_realCharacter (by intro x; simp)
  exact isLocallyClosedPolyhedron_signCell _ (fun _ => hf) _

end Rational

section Fibers

variable {R : Type*} [Zero R] (c : R) (n b : ℤ)

/-- The admitted incoming chart labels. Nonzero horizontal degree selects its
incoming side; nonzero vertical invariant degree admits both sides. -/
abbrev IncomingSlabChartIndex :=
  {right : Bool // c ≠ 0 ∧ (n, b) ≠ 0 ∧ if right then 0 ≤ n else n ≤ 0}

/-- The chart fibers are exactly the incoming-chamber broken lines, including
vertical invariant rays. There are no charts for zero decorations or direction. -/
def incomingSlabChartEquiv (Q : ℝ × ℝ) :
    {α : IncomingSlabChartIndex c n b // Q ∈ incomingSlabDomain α.val} ≃
      IncomingSlabBrokenLine c n b Q where
  toFun α := incomingSlabBrokenLine c n b Q α.val.property.1 α.val.property.2.1
    (by
      have hs := (mem_incomingSlabDomain α.val.val Q).mp α.property
      cases he : α.val.val <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hs
      · exact hs.ne
      · exact hs.ne')
    (by
      have hs := (mem_incomingSlabDomain α.val.val Q).mp α.property
      have hn := α.val.property.2.2
      cases he : α.val.val <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hs hn
      · exact mul_nonneg_of_nonpos_of_nonpos hs.le (by exact_mod_cast hn)
      · exact mul_nonneg hs.le (by exact_mod_cast hn))
  invFun β := ⟨⟨decide (0 < Q.1), β.coefficient_ne_zero, β.exponent_ne_zero, by
    split_ifs with hs
    · have hq : 0 < Q.1 := of_decide_eq_true hs
      have hn : 0 ≤ (n : ℝ) := nonneg_of_mul_nonneg_right β.incoming_side hq
      exact_mod_cast hn
    · have hq : Q.1 < 0 := lt_of_le_of_ne (by simpa using hs) β.off_slab
      have hn : (n : ℝ) ≤ 0 := nonpos_of_mul_nonneg_right β.incoming_side hq
      exact_mod_cast hn⟩, by
    rw [mem_incomingSlabDomain]
    split_ifs with hs
    · exact of_decide_eq_true hs
    · exact lt_of_le_of_ne (by simpa using hs) β.off_slab⟩
  left_inv α := by
    apply Subtype.ext
    apply Subtype.ext
    have hs := (mem_incomingSlabDomain α.val.val Q).mp α.property
    cases he : α.val.val <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    · exact decide_eq_false (not_lt_of_ge hs.le)
    · exact decide_eq_true hs
  right_inv _ := Subsingleton.elim _ _

/-- The inverse chart enumeration selects the side of the endpoint. -/
@[simp]
theorem incomingSlabChartEquiv_symm_apply_val (Q : ℝ × ℝ)
    (β : IncomingSlabBrokenLine c n b Q) :
    ((incomingSlabChartEquiv c n b Q).symm β).val.val = decide (0 < Q.1) := (rfl)

end Fibers

/-- Incoming rays have a continuous extension over their closed charts. This
uses the straight specialization of the existing branch path family. -/
theorem IncomingSlabBrokenLine.toContinuousMap_eq_slabBranchPath
    {R : Type*} [Zero R] {c : R} {n b : ℤ}
    {Q : ℝ × ℝ} (β : IncomingSlabBrokenLine c n b Q) :
    β.ray.toContinuousMap = slabBranchPath n b b Q := by
  apply ContinuousMap.ext
  intro s
  rw [FiniteAffineRay.toContinuousMap_apply, β.ray_eq_straight,
    FiniteAffineRay.straight_apply, slabBranchPath_apply]
  apply Prod.ext <;> simp [sub_eq_add_neg, add_comm, mul_comm]

/-- Every net of incoming rays with converging endpoints converges in the
compact-open topology, even when the limit lies on the slab or at the origin. -/
theorem tendsto_incomingSlabBrokenLine {R A : Type*} [Zero R] {c : R} {n b : ℤ}
    {l : Filter A} {Q : A → ℝ × ℝ} {Q₀ : ℝ × ℝ}
    (β : ∀ a, IncomingSlabBrokenLine c n b (Q a)) (hQ : Tendsto Q l (𝓝 Q₀)) :
    Tendsto (fun a => (β a).ray.toContinuousMap) l (𝓝 (slabBranchPath n b b Q₀)) := by
  simpa only [IncomingSlabBrokenLine.toContinuousMap_eq_slabBranchPath, Function.comp_def] using
    (slabBranchPath n b b).continuous.continuousAt.tendsto.comp hQ

open AddMonoidAlgebra Classical in
/-- Weighted evaluation over the finite incoming chart fiber is the actual
incoming-ray sum. Every chart retains the whole original monomial decoration. -/
theorem incomingSlabWeightedEvaluation_eq_sum_charts {R : Type*} [Semiring R]
    (c : R) (n b : ℤ) (Q : ℝ × ℝ)
    [Fintype {α : IncomingSlabChartIndex c n b // Q ∈ incomingSlabDomain α.val}] :
    incomingSlabWeightedEvaluation c n b Q =
      ∑ _α : {α : IncomingSlabChartIndex c n b // Q ∈ incomingSlabDomain α.val},
        single ((n.natAbs : ℤ), b) c := by
  rw [incomingSlabWeightedEvaluation_def]
  exact (Fintype.sum_equiv (incomingSlabChartEquiv c n b Q) _ _ (fun _ => rfl)).symm

end Mei.FocusFocus
