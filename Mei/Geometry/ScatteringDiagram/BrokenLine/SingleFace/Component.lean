/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Component fibers at a single face

For a fixed homogeneous input and a linear propagation map preserving normal
velocity, the actual one-crossing decorated rays are indexed by the nonzero
output components whose computed crossing parameter is negative and whose
crossing point misses the singular set. The source is the entire incoming
half-space. The equivalence retains the actual admissible
ray, including its incoming tail, crossing parameter and whole decoration.
It counts unchanged-degree crossings and different degrees with equal velocities.

Reindexing the existing weighted evaluation gives the sum of precisely these
admitted components. If every nonzero component has a nonsingular crossing on
the opposite side, this sum is the propagated input. No positivity, finite
grading, coefficient basis or injectivity of propagation is required. A finite
affine cover of the singular set, none of whose members contains the full face,
supplies one exceptional endpoint arrangement for the opposite-side identity;
the empty itinerary recovers the incoming value.

The geometric construction is `AdmissibleRayRealization.singleFaceOne`; its
uniqueness is the existing admissible-ray uniqueness theorem. Whole-component
propagation across one face follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : Module.End R M) (p : Γ) (a : ℳ p) (v : Γ → V)
  (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)

local notation "D" Q => DecoratedAdmissibleRay ℳ (fun _ : Fin 1 => T) p a v
  (fun _ => ν) (fun _ => b) (fun _ => SignType.sign (ν (v p)))
  (fun _ => Set.ofPred (fun x => ν x = b)) (fun _ : Unit => Set.ofPred (fun x => ν x = b))
  (fun _ : Unit => Z) (Set.ofPred (fun x => 0 < (ν x - b) / ν (v p))) Q

variable (hnormal : ∀ q, DirectSum.decompose ℳ (T a) q ≠ 0 → ν (v q) = ν (v p))
  (hZ : Z ⊆ {x | ν x = b})

include hnormal hZ

omit hnormal [DecidableEq Γ] in
/-- Admission of the one-crossing ray with recorded degree `q 0` requires a negative
crossing parameter and a nonsingular crossing point, by the geometric
characterization of single-face admission. -/
private theorem nonempty_realization_iff_crossing (q : Fin 1 → Γ)
    (hq : ν (v (q 0)) = ν (v p)) (Q : V) :
    Nonempty (AdmissibleRayRealization (fun _ : Fin 1 => ν) (fun _ => b)
      (fun j => v (Fin.snoc (α := fun _ => Γ) q p j))
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν (v p)} Q) ↔
      (ν Q - b) / ν (v (q 0)) < 0 ∧ Q - ((ν Q - b) / ν (v (q 0))) • v (q 0) ∉ Z := by
  have hv : (fun j => v (Fin.snoc (α := fun _ => Γ) q p j)) = ![v (q 0), v p] := by
    funext j
    fin_cases j <;> simp [Fin.snoc]
  rw [hv]
  exact AdmissibleRayRealization.nonempty_singleFace_one_iff hq hZ

/-- Actual one-face rays correspond to the nonzero output components with a
negative crossing parameter and a nonsingular crossing point. This includes
unchanged degrees and equal spatial velocities. -/
def singleFaceComponentFiberEquiv (Q : V) : (D Q) ≃
    {q : Γ // DirectSum.decompose ℳ (T a) q ≠ 0 ∧
      (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z} := by
  let F : (D Q) → {q : Γ // DirectSum.decompose ℳ (T a) q ≠ 0 ∧
      (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z} := fun r => by
    have hne : DirectSum.decompose ℳ (T a) (r.1.val 0) ≠ 0 := by
      have hr := (mem_decoratedHistorySupport ..).mp r.1.property |>.1
      simpa using hr
    have hc := (nonempty_realization_iff_crossing (p := p) (v := v) (ν := ν) (b := b)
      (Z := Z) hZ r.1.val (hnormal _ hne) Q).mp ⟨r.2⟩
    exact ⟨r.1.val 0, hne, hc.1, hc.2⟩
  apply Equiv.ofBijective F
  constructor
  · intro r s hrs
    apply DecoratedAdmissibleRay.ext_history
    funext j
    have he := congrArg Subtype.val hrs
    simpa only [Fin.fin_one_eq_zero j] using he
  · rintro ⟨q, hq, ht, hx⟩
    have hp : (fun _ : Fin 1 => q) ∈ decoratedHistorySupport ℳ (fun _ => T) p a v
        (fun _ => ν) (fun _ => SignType.sign (ν (v p))) := by
      simp [Fin.snoc, hnormal q hq, hq]
    obtain ⟨hg⟩ := (nonempty_realization_iff_crossing (p := p) (v := v) (ν := ν) (b := b)
      (Z := Z) hZ (fun _ : Fin 1 => q) (hnormal q hq) Q).mpr ⟨ht, hx⟩
    exact ⟨⟨⟨fun _ => q, hp⟩, hg⟩, Subtype.ext rfl⟩

/-- The component index is exactly the degree recorded at the crossing. -/
@[simp]
theorem singleFaceComponentFiberEquiv_apply_val (Q : V) (r : (D Q)) :
    (singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q r).val = r.1.val 0 :=
  (rfl)

/-- The inverse fiber comparison records the component as the degree of the ray. -/
@[simp]
theorem singleFaceComponentFiberEquiv_symm_val (Q : V)
    (q : {q : Γ // DirectSum.decompose ℳ (T a) q ≠ 0 ∧
      (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z}) (j : Fin 1) :
    ((singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q).symm q).1.val j = q.val := by
  have he := congrArg Subtype.val
    ((singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q).apply_symm_apply q)
  rw [singleFaceComponentFiberEquiv_apply_val] at he
  simpa only [Fin.fin_one_eq_zero j] using he

/-- The ray indexed by a component carries that entire component as its final
decoration, rather than a choice of monomial or a scalar summand. -/
@[simp↓]
theorem singleFaceComponentFiberEquiv_symm_decoration (Q : V)
    (q : {q : Γ // DirectSum.decompose ℳ (T a) q ≠ 0 ∧
      (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z}) :
    ((singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q).symm q).decoration 0 =
      (DirectSum.decompose ℳ (T a) q.val : M) := by
  have he := congrArg Subtype.val
    ((singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q).apply_symm_apply q)
  rw [singleFaceComponentFiberEquiv_apply_val] at he
  simpa using congrArg (fun q => (DirectSum.decompose ℳ (T a) q : M)) he

/-- The inverse fiber comparison records the computed crossing time. -/
@[simp]
theorem singleFaceComponentFiberEquiv_symm_parameter (Q : V)
    (q : {q : Γ // DirectSum.decompose ℳ (T a) q ≠ 0 ∧
      (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z}) :
    ((singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q).symm q).2.parameter 1 =
      (ν Q - b) / ν (v q.val) := by
  let r := (singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q).symm q
  have he := congrArg Subtype.val
    ((singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q).apply_symm_apply q)
  rw [singleFaceComponentFiberEquiv_apply_val] at he
  have ht := r.2.parameter_eq_div_singleFace
    (fun j => by simpa only [Fin.snoc_castSucc] using r.normal_velocity_eq j) 0
  have hdeg : r.1.val 0 = q.val := he
  rw [Fin.snoc_apply_zero, hdeg] at ht
  exact ht

open Classical in
/-- Weighted evaluation at one face is the sum of the nonzero output components
whose computed crossings are admitted. Singular and terminal crossings contribute
no rays. The formula applies at every endpoint, without a genericity assumption. -/
theorem decoratedRayEvaluation_singleFace_one_eq_sum (Q : V) :
    decoratedRayEvaluation ℳ (fun _ : Fin 1 => T) p a v
      (fun _ => ν) (fun _ => b) (fun _ => SignType.sign (ν (v p)))
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν (v p)} Q =
        ∑ q ∈ (DirectSum.decompose ℳ (T a)).support,
          if (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z
          then (DirectSum.decompose ℳ (T a) q : M) else 0 := by
  classical
  let A := {q : Γ // DirectSum.decompose ℳ (T a) q ≠ 0 ∧
    (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z}
  let e := singleFaceComponentFiberEquiv ℳ T p a v ν b Z hnormal hZ Q
  let s := (DirectSum.decompose ℳ (T a)).support.filter fun q =>
    (ν Q - b) / ν (v q) < 0 ∧ Q - ((ν Q - b) / ν (v q)) • v q ∉ Z
  let e' : A ≃ (s : Type _) := Equiv.subtypeEquivRight fun q => by simp [s]
  let := Fintype.ofFinite (D Q)
  let := Fintype.ofEquiv (s : Type _) e'.symm
  rw [decoratedRayEvaluation_def]
  calc
    ∑ r : (D Q), r.decoration 0 = ∑ q : A, (DirectSum.decompose ℳ (T a) q.val : M) := by
      apply Fintype.sum_equiv e
      intro r
      have hw := singleFaceComponentFiberEquiv_symm_decoration
        ℳ T p a v ν b Z hnormal hZ Q (e r)
      simpa only [e, Equiv.symm_apply_apply] using hw
    _ = ∑ q : (s : Type _), (DirectSum.decompose ℳ (T a) q.val : M) := by
      exact Fintype.sum_equiv e' _ _ fun _ => rfl
    _ = _ := (Finset.sum_coe_sort s
      (fun q => (DirectSum.decompose ℳ (T a) q : M))).trans
        (by simp only [s, Finset.sum_filter])

/-- If all nonzero components cross nonsingularly at an opposite-side endpoint,
the actual one-crossing weighted evaluation is the full propagated coefficient.
Zero input and cancellation among output coefficients are allowed. -/
theorem decoratedRayEvaluation_singleFace_one_eq (Q : V)
    (ht : (ν Q - b) / ν (v p) < 0)
    (hx : ∀ q, DirectSum.decompose ℳ (T a) q ≠ 0 →
      Q - ((ν Q - b) / ν (v q)) • v q ∉ Z) :
    decoratedRayEvaluation ℳ (fun _ : Fin 1 => T) p a v
      (fun _ => ν) (fun _ => b) (fun _ => SignType.sign (ν (v p)))
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν (v p)} Q = T a := by
  classical
  rw [decoratedRayEvaluation_singleFace_one_eq_sum ℳ T p a v ν b Z hnormal hZ]
  trans ∑ q ∈ (DirectSum.decompose ℳ (T a)).support,
    (DirectSum.decompose ℳ (T a) q : M)
  · apply Finset.sum_congr rfl
    intro q hq
    have hne := DFinsupp.mem_support_iff.mp hq
    rw [ite_eq_left ⟨by rwa [hnormal q hne], hx q hne⟩]
  · exact DirectSum.sum_support_decompose ℳ (T a)

omit hnormal in
open Classical in
/-- The empty one-face itinerary has the incoming coefficient on the incoming
half-space and zero elsewhere. Its source contains every tail in that half-space. -/
theorem decoratedRayEvaluation_singleFace_empty (Q : V) :
    decoratedRayEvaluation ℳ (fun _ : Fin 0 => T) p a v
      (fun _ => ν) (fun _ => b) (fun _ => SignType.sign (ν (v p)))
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν (v p)} Q =
        if 0 < (ν Q - b) / ν (v p) then (a : M) else 0 := by
  classical
  have hdom (q : Fin 0 → Γ) :
      Q ∈ admissibleBackwardDomain (fun _ : Fin 0 => ν) (fun _ => b)
        (fun j => v (Fin.snoc (α := fun _ => Γ) q p j))
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
        (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν (v p)} ↔
          0 < (ν Q - b) / ν (v p) := by
    simp only [Fin.snoc_zero]
    exact (nonempty_admissibleRayRealization_iff ..).symm.trans
      (AdmissibleRayRealization.nonempty_singleFace_empty_iff hZ)
  rw [decoratedRayEvaluation_eq_sum_homogeneousHistory]
  simp only [Fin.forall_fin_zero, true_and, hdom]
  split_ifs
  · simp only [sum_homogeneousHistory, List.ofFn_zero, List.prod_nil,
      Module.End.one_apply]
  · simp

/-- If finitely many affine subspaces cover the singular set and none contains
the full face, one finite exceptional arrangement makes the actual opposite-side
weighted evaluation equal the propagated coefficient. The arrangement is built
from the finite output support, even when the grading is infinite. -/
theorem exists_decoratedRayEvaluation_singleFace_arrangement {κ : Type*} [Finite κ]
    (A : κ → AffineSubspace ℝ V) (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ E : ExceptionalArrangement V, ∀ Q, E.IsGeneric Q →
      (ν Q - b) / ν (v p) < 0 →
        decoratedRayEvaluation ℳ (fun _ : Fin 1 => T) p a v
          (fun _ => ν) (fun _ => b) (fun _ => SignType.sign (ν (v p)))
          (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
          (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν (v p)} Q = T a := by
  classical
  let s := (DirectSum.decompose ℳ (T a)).support
  obtain ⟨E, hE⟩ := exists_forall_notMem_sweepProjection
    (fun _ : (s : Type _) => ν) (fun _ => b)
    (fun q => (ν (v q.val))⁻¹ • v q.val) A (fun _ j => hA j)
  refine ⟨E, fun Q hQ ht =>
    decoratedRayEvaluation_singleFace_one_eq ℳ T p a v ν b Z hnormal hZ Q ht ?_⟩
  intro q hq hmem
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hmem)
  have he : sweepProjection ν b ((ν (v q))⁻¹ • v q) Q =
      Q - ((ν Q - b) / ν (v q)) • v q := by
    simp only [sweepProjection_apply, smul_smul, div_eq_mul_inv]
    module
  exact hE Q hQ ⟨q, DFinsupp.mem_support_iff.mpr hq⟩ j (he ▸ hj)

end Mei
