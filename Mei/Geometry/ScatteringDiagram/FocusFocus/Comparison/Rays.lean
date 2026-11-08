/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.SingleFace
public import Mei.Geometry.Convex.Sweep.Admissible.Limit

/-!
# Focus-focus rays as single-face decorated rays

The lower and upper slab presentations specialize the shared `PathDecoratedRay`
construction along the one-arrow path of the one-object quiver on `Unit`. Their
propagation is the total transfer
of the slab correspondence, their source is the full incoming half-plane, and
their singular obstacle is the origin. Restricting to the corresponding sign
of the crossing height distinguishes the two coordinate presentations.

The explicit `SlabBrokenLine` fiber is equivalent to the disjoint union of these
two shared fibers. The comparison retains whole decorations, the actual path
and its incoming tail, and the recorded slab encounter even when it is not a
bend. Reindexing the finite weighted sum therefore computes the explicit slab
evaluation through the common decorated-ray construction. This comparison does
not construct a global section or a local-resolution certificate.

The slab coordinates and upper/lower transition follow Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4). The formal suppliers are
`pathSingleFaceComponentFiberEquiv` and `slab_transfer_eq_upper`.
-/

public noncomputable section

namespace Mei.FocusFocus

open Set TauCeti AddMonoidAlgebra Mei.NodeAlgebra Mei.Convex Quiver

variable {R : Type*} [CommRing R] (t c : R) (n b : ℤ)

local notation "ν" => ContinuousLinearMap.fst ℝ ℝ ℝ
local notation "B" upper:arg => cond upper (b + (Int.natAbs n : ℤ)) b
local notation "C" upper:arg =>
  exponentCorrespondence (single 0 t + single (cond upper (-1 : ℤ) 1) t)
local notation "p" upper:arg => ((Int.natAbs n : ℤ), B upper)
local notation "a" upper:arg =>
  (Subtype.mk (single (p upper) c) (single_mem_grade _ _) : grade R (p upper))
local notation "v" => fun q : ℤ × ℤ => ((n : ℝ), ((Prod.snd q : ℤ) : ℝ))
local notation "arrow" => SingleObj.toHom ()
local notation "path₁" => Path.cons (Path.nil : Path (SingleObj.star Unit) (SingleObj.star Unit))
  (SingleObj.toHom ())
local notation "D" upper:arg Q:arg =>
  PathDecoratedRay (Q := SingleObj Unit) (M := fun _ => R[ℤ × ℤ]) (ι := fun _ => ℤ × ℤ)
    (fun _ => GradedCorrespondence.totalTransfer (C upper))
    (fun _ => (grade R : ℤ × ℤ → Submodule R R[ℤ × ℤ])) (p upper) (a upper) (fun _ => v)
    (fun _ => ν) (fun _ => SignType.sign (ν (v (p upper)))) (fun _ => 0)
    (fun _ => Set.ofPred (fun x : ℝ × ℝ => ν x = 0))
    (fun _ : Unit => Set.ofPred (fun x : ℝ × ℝ => ν x = 0)) (fun _ : Unit => ({0} : Set (ℝ × ℝ)))
    (Set.ofPred (fun x : ℝ × ℝ => 0 < (ν x - 0) / ν (v (p upper))))
    path₁ Q
private theorem decompose_chart_transfer (upper : Bool) (q : ℤ × ℤ) :
    DirectSum.decompose (grade R : ℤ × ℤ → Submodule R R[ℤ × ℤ])
      ((C upper).totalTransfer (single (p upper) c)) q =
      (exponentCorrespondence (single 0 t + single 1 t)).transfer
        ⟨((n.natAbs : ℤ), b), by simp⟩ q
        ⟨single (n.natAbs, b) c, single_mem_grade _ _⟩ := by
  rw [GradedCorrespondence.totalTransfer_apply,
    GradedCorrespondence.liftLeftTotal_coe (C upper) ⟨p upper, by simp⟩ (a upper)]
  cases upper <;> simp only [Bool.cond_false, Bool.cond_true,
    ← GradedCorrespondence.transfer_apply]
  exact Subtype.ext (slab_transfer_eq_upper t c n.natAbs b q).symm

local notation "Outputs" Q:arg =>
  {q : ℤ × ℤ //
    GradedCorrespondence.transfer (exponentCorrespondence (single 0 t + single 1 t))
      (Subtype.mk ((Int.natAbs n : ℤ), b) (by simp)) q
      (Subtype.mk (single (Int.natAbs n, b) c) (single_mem_grade _ _)) ≠ 0 ∧
    Prod.fst Q / (n : ℝ) < 0 ∧ Prod.snd Q - ((Prod.snd q : ℤ) : ℝ) * Prod.fst Q / n ≠ 0}

private def chartComponentEquiv (upper : Bool) (Q : ℝ × ℝ) :
    D upper Q ≃ Outputs Q := by
  refine (pathSingleFaceComponentFiberEquiv (Q := SingleObj Unit) (M := fun _ => R[ℤ × ℤ])
    (ι := fun _ => ℤ × ℤ) (fun _ => (C upper).totalTransfer)
    (fun _ => (grade R : ℤ × ℤ → Submodule R R[ℤ × ℤ])) arrow (p upper) (a upper) (fun _ => v)
    ν 0 {0} (fun _ _ => rfl) (by simp) Q).trans ?_
  apply Equiv.subtypeEquivRight
  intro q
  rw [decompose_chart_transfer]
  simp only [ContinuousLinearMap.coe_fst', sub_zero]
  by_cases ht : Q.1 / (n : ℝ) < 0
  · have hn : (n : ℝ) ≠ 0 := fun hn => by simp [hn] at ht
    have he : Q - (Q.1 / (n : ℝ)) • ((n : ℝ), (q.2 : ℝ)) =
        (0, Q.2 - (q.2 : ℝ) * Q.1 / n) := by
      apply Prod.ext
      · simp [hn]
      · dsimp
        ring
    rw [he]
    simp only [mem_singleton_iff, Prod.mk_eq_zero, true_and]
  · simp only [ht, false_and, and_false]

private theorem chartComponentEquiv_degree (upper : Bool) (Q : ℝ × ℝ)
    (r : D upper Q) :
    (chartComponentEquiv t c n b upper Q r).val = r.1.val.2 := by
  dsimp only [chartComponentEquiv, Equiv.trans_apply, Equiv.subtypeEquivRight_apply]
  exact pathSingleFaceComponentFiberEquiv_apply_val ..

/-- A shared single-face decorated ray in one slab chart, restricted to the
corresponding strict sign of its crossing height. Its incoming source is the
entire half-plane, and its propagation uses the upper or lower slab span. -/
abbrev SlabChartRay (upper : Bool) (Q : ℝ × ℝ) :=
  {r : D upper Q //
    if upper then 0 < Q.2 - ((r.1.val.2).2 : ℝ) * Q.1 / n
    else Q.2 - ((r.1.val.2).2 : ℝ) * Q.1 / n < 0}

private def outputLineEquiv (Q : ℝ × ℝ) : Outputs Q ≃ SlabBrokenLine t c n b Q where
  toFun q :=
    let j := (slabTransferEquiv t c n.natAbs b).symm ⟨q.val, q.property.1⟩
    slabBrokenLine t c n b Q q.property.2.1 ⟨j.val, j.property, by
      have he := slabTransferEquiv_symm_degree t c n.natAbs b ⟨q.val, q.property.1⟩
      have hs := congrArg Prod.snd he
      dsimp only at hs
      exact hs ▸ q.property.2.2⟩
  invFun β := ⟨β.degree, β.transfer_ne_zero, β.opposite, β.snd_sub_mul_fst_div_ne_zero⟩
  left_inv q := by
    apply Subtype.ext
    dsimp only
    rw [degree_slabBrokenLine]
    exact slabTransferEquiv_symm_degree t c n.natAbs b ⟨q.val, q.property.1⟩
  right_inv β := by
    apply SlabBrokenLine.ext
    dsimp only
    rw [degree_slabBrokenLine]
    exact slabTransferEquiv_symm_degree t c n.natAbs b ⟨β.degree, β.transfer_ne_zero⟩

private theorem outputLineEquiv_degree (Q : ℝ × ℝ) (q : Outputs Q) :
    (outputLineEquiv t c n b Q q).degree = q.val := by
  dsimp only [outputLineEquiv, Equiv.coe_fn_mk]
  rw [degree_slabBrokenLine]
  exact slabTransferEquiv_symm_degree t c n.natAbs b ⟨q.val, q.property.1⟩

private def chartLineEquiv (upper : Bool) (Q : ℝ × ℝ) :
    D upper Q ≃ SlabBrokenLine t c n b Q :=
  (chartComponentEquiv t c n b upper Q).trans (outputLineEquiv t c n b Q)

private theorem chartLineEquiv_degree (upper : Bool) (Q : ℝ × ℝ) (r : D upper Q) :
    (chartLineEquiv t c n b upper Q r).degree = r.1.val.2 :=
  (outputLineEquiv_degree t c n b Q _).trans
    (chartComponentEquiv_degree t c n b upper Q r)

private def linePartitionEquiv (Q : ℝ × ℝ) :
    (Σ upper : Bool, {β : SlabBrokenLine t c n b Q //
      if upper then 0 < Q.2 - (β.degree.2 : ℝ) * Q.1 / n
      else Q.2 - (β.degree.2 : ℝ) * Q.1 / n < 0}) ≃ SlabBrokenLine t c n b Q := by
  classical
  let f := fun β : SlabBrokenLine t c n b Q =>
    decide (0 < Q.2 - (β.degree.2 : ℝ) * Q.1 / n)
  refine (Equiv.sigmaCongrRight fun upper => Equiv.subtypeEquivRight
    (q := fun β => f β = upper) ?_).trans (Equiv.sigmaFiberEquiv f)
  intro β
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, f,
    decide_eq_false_iff_not, decide_eq_true_eq]
  rw [not_lt, lt_iff_le_and_ne, and_iff_left β.snd_sub_mul_fst_div_ne_zero]

/-- The disjoint union of shared decorated rays in the two slab charts is
exactly the explicit focus-focus crossing fiber. Zero transfer components and
singular crossings occur in neither fiber. -/
def slabChartRayEquiv (Q : ℝ × ℝ) :
    (Σ upper : Bool, SlabChartRay t c n b upper Q) ≃ SlabBrokenLine t c n b Q :=
  (Equiv.sigmaCongrRight fun upper =>
    Equiv.subtypeEquiv (chartLineEquiv t c n b upper Q)
      (fun r => by rw [chartLineEquiv_degree])).trans (linePartitionEquiv t c n b Q)

/-- The comparison preserves the entire outgoing degree, including degrees
with equal geometric velocities. -/
@[simp]
theorem slabChartRayEquiv_degree (Q : ℝ × ℝ)
    (z : Σ upper : Bool, SlabChartRay t c n b upper Q) :
    (slabChartRayEquiv t c n b Q z).degree = z.2.val.1.val.2 :=
  chartLineEquiv_degree t c n b z.1 Q z.2.val

/-- The inverse comparison recovers the explicit ray's outgoing degree. -/
@[simp]
theorem slabChartRayEquiv_symm_degree (Q : ℝ × ℝ) (β : SlabBrokenLine t c n b Q) :
    (((slabChartRayEquiv t c n b Q).symm β).2.val.1.val.2) = β.degree := by
  rw [← slabChartRayEquiv_degree, Equiv.apply_symm_apply]

/-- The explicit and shared fibers carry exactly the same whole homogeneous
output component. Vanishing binomial coefficients contribute no rays. -/
@[simp]
theorem slabChartRayEquiv_decoration (Q : ℝ × ℝ)
    (z : Σ upper : Bool, SlabChartRay t c n b upper Q) :
    (slabChartRayEquiv t c n b Q z).decoration = z.2.val.decoration := by
  rw [SlabBrokenLine.decoration_def, slabChartRayEquiv_degree, PathDecoratedRay.decoration_def,
    show z.2.val.1.val = (z.2.val.1.val.1, z.2.val.1.val.2) from rfl,
    Path.homogeneousHistory_cons_apply, Path.homogeneousHistory_nil, LinearMap.id_apply,
    decompose_chart_transfer]

/-- The one-arrow path data of a chart ray are the constant single-face data with the
outgoing and incoming velocities. -/
private theorem chartRay_data (upper : Bool) (q : ℤ × ℤ) :
    (Path.reverseArrowLabels (fun _ => ν) path₁) = (fun _ => ν) ∧
      (Path.reverseArrowLabels (fun _ => (0 : ℝ)) path₁) = (fun _ => 0) ∧
      (Path.reverseArrowLabels (fun _ => Set.ofPred (fun x : ℝ × ℝ => ν x = 0)) path₁) =
        (fun _ => Set.ofPred (fun x : ℝ × ℝ => ν x = 0)) ∧
      Path.Degrees.reverseVertexLabels (fun _ => v) (p upper) path₁
        (PUnit.unit, q) = ![v q, v (p upper)] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    funext j
    first
    | (rw [Path.reverseArrowLabels_cons]; exact Fin.cases rfl (fun j => j.elim0) j)
    | (rw [Path.Degrees.reverseVertexLabels_cons, Path.Degrees.reverseVertexLabels_nil]
       fin_cases j <;> rfl)

/-- The actual shared realization has the same continuous extension as the
explicit branch in its fixed upper or lower chart. In particular the entire
incoming half-line is retained. -/
theorem SlabChartRay.toContinuousMap_eq_slabBranchPath (upper : Bool) (Q : ℝ × ℝ)
    (r : SlabChartRay t c n b upper Q) :
    r.val.2.ray.toContinuousMap =
      slabBranchPath n (B upper) (r.val.1.val.2).2 Q := by
  obtain ⟨hf, hc, hP, hv⟩ := chartRay_data n b upper r.val.1.val.2
  have h := (r.val.2.congrData hf hc hv hP).toContinuousMap_eq_backwardPath
  have hr : (r.val.2.congrData hf hc hv hP).ray = r.val.2.ray :=
    AdmissibleRayRealization.ray_congrData _ _ _ _ _
  rw [hr] at h
  rw [h, slabBranchPath_def]
  rfl

/-- The fiber comparison preserves the whole path, including its incoming
coordinate presentation and every point before the crossing. -/
@[simp]
theorem slabChartRayEquiv_path (Q : ℝ × ℝ)
    (z : Σ upper : Bool, SlabChartRay t c n b upper Q) :
    (slabChartRayEquiv t c n b Q z).ray.toContinuousMap =
      z.2.val.2.ray.toContinuousMap := by
  rcases z with ⟨upper, r⟩
  rw [SlabBrokenLine.ray_eq_slabBranch, ← slabBranchPath_eq_slabBranch,
    slabChartRayEquiv_degree, SlabChartRay.toContinuousMap_eq_slabBranchPath]
  have hsign := r.property
  have hB : slabIncomingExponent n b (r.val.1.val.2).2 Q = B upper := by
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Bool.cond_false, Bool.cond_true] at hsign ⊢
    · exact slabIncomingExponent_of_neg _ _ _ _ hsign
    · exact slabIncomingExponent_of_pos _ _ _ _ hsign
  rw [hB]

/-- The recorded encounter occurs at the explicit slab crossing time. The
record is retained even when the incoming and outgoing directions agree. -/
@[simp]
theorem SlabChartRay.parameter_one (upper : Bool) (Q : ℝ × ℝ)
    (r : SlabChartRay t c n b upper Q) : r.val.2.parameter 1 = Q.1 / (n : ℝ) := by
  obtain ⟨hf, hc, hP, hv⟩ := chartRay_data n b upper r.val.1.val.2
  have h := (r.val.2.congrData hf hc hv hP).parameter_eq_div_singleFace
    (fun j => by fin_cases j; simp) (0 : Fin 1)
  have hp : (r.val.2.congrData hf hc hv hP).parameter = r.val.2.parameter :=
    AdmissibleRayRealization.parameter_congrData _ _ _ _ _
  rw [hp] at h
  simp only [ContinuousLinearMap.coe_fst', sub_zero] at h
  exact h

open Classical in
/-- The explicit slab weighted evaluation is the finite sum over the shared
single-face decorated rays in its two coordinate charts. No genericity is
required; singular branches and zero decorations are absent on both sides. -/
theorem slabWeightedEvaluation_eq_sum_decoratedRays (Q : ℝ × ℝ) :
    slabWeightedEvaluation t c n b Q =
      let := Fintype.ofFinite (Σ upper : Bool, SlabChartRay t c n b upper Q)
      ∑ z : Σ upper : Bool, SlabChartRay t c n b upper Q, z.2.val.decoration := by
  classical
  let := Fintype.ofFinite (Σ upper : Bool, SlabChartRay t c n b upper Q)
  rw [slabWeightedEvaluation_def]
  exact (Fintype.sum_equiv (slabChartRayEquiv t c n b Q) _ _
    (fun z => (slabChartRayEquiv_decoration t c n b Q z).symm)).symm

end Mei.FocusFocus
