/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Component fibers of path rays at a single face

Consider decorated rays along the one-arrow path `Path.nil.cons e` of an arbitrary
quiver, crossing one face `{x | ν x = β}` of the source chamber module into the target
chamber module, with the face as obstacle, a singular set `Z` inside the face and the
entire incoming half-space as source. For a fixed homogeneous input whose propagated
components preserve normal velocity, the actual rays are indexed by the nonzero output
components whose computed crossing parameter is negative and whose crossing point misses
`Z`. The equivalence retains the actual admissible ray, including its incoming tail,
crossing parameter and whole decoration, and counts unchanged-degree crossings and
different degrees with equal velocities.

Reindexing the weighted evaluation gives the sum of precisely these admitted components.
If every nonzero component has a nonsingular crossing on the opposite side, this sum is
the propagated input; along the empty path the evaluation is the input on the incoming
half-space and zero elsewhere. A finite affine cover of `Z`, none of whose members
contains the full face, supplies one exceptional arrangement for the opposite-side
identity, uniformly over any family of inputs with uniform finite output support.

The geometric inputs are `AdmissibleRayRealization.nonempty_singleFace_one_iff` and
`AdmissibleRayRealization.nonempty_singleFace_empty_iff`. Whole-component propagation
across one face follows Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open TauCeti (ExceptionalArrangement)

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (e : a ⟶ b) (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V) (ν : V →L[ℝ] ℝ) (β : ℝ) (Z : Set V)

local notation "D" X:max => PathDecoratedRay T ℳ i₀ x v (fun _ => ν)
  (fun _ => SignType.sign (ν (v a i₀))) (fun _ => β) (fun _ => Set.ofPred fun y => ν y = β)
  (fun _ : Unit => Set.ofPred fun y => ν y = β) (fun _ : Unit => Z)
  (Set.ofPred fun y => 0 < (ν y - β) / ν (v a i₀)) (Path.cons (Path.nil : Path a a) e) X
local notation "Components" X:max => {q : ι b // DirectSum.decompose (ℳ b) (T e x) q ≠ 0 ∧
  (ν X - β) / ν (v b q) < 0 ∧ X - ((ν X - β) / ν (v b q)) • v b q ∉ Z}

variable (hnormal : ∀ q, DirectSum.decompose (ℳ b) (T e x) q ≠ 0 → ν (v b q) = ν (v a i₀))
  (hZ : Z ⊆ {y | ν y = β})

include hnormal hZ

omit hZ in
/-- The decorated history of the one-arrow path with output degree `q` survives exactly
when the output component of degree `q` is nonzero. -/
private theorem mem_support_iff (q : ι b) :
    ((PUnit.unit, q) : ((Path.nil : Path a a).cons e).Degrees ι) ∈
      pathDecoratedHistorySupport T ℳ i₀ x v (fun _ => ν)
        (fun _ => SignType.sign (ν (v a i₀))) ((Path.nil : Path a a).cons e) ↔
      DirectSum.decompose (ℳ b) (T e x) q ≠ 0 := by
  rw [mem_pathDecoratedHistorySupport_cons, Path.homogeneousHistory_cons_apply,
    Path.homogeneousHistory_nil, LinearMap.id_apply, Path.Degrees.terminalDegree_nil,
    mem_pathDecoratedHistorySupport, Path.homogeneousHistory_nil, LinearMap.id_apply]
  constructor
  · exact fun h => fun hz => h.2.1 (by rw [hz]; rfl)
  · intro hq
    have hx : (x : M a) ≠ 0 := fun hx => hq (by rw [hx, map_zero]; simp)
    refine ⟨⟨hx, fun j => j.elim0⟩, fun hz => hq (Subtype.ext hz), hnormal q hq, ?_⟩
    rw [hnormal q hq]

omit [∀ q, DecidableEq (ι q)] hnormal in
/-- Admission of the one-crossing realization with output degree `q` is the single-face
crossing condition. -/
private theorem nonempty_realization_iff (q : ι b) (hq : ν (v b q) = ν (v a i₀)) (X : V) :
    Nonempty (AdmissibleRayRealization
      (((Path.nil : Path a a).cons e).reverseArrowLabels fun _ => ν)
      (((Path.nil : Path a a).cons e).reverseArrowLabels fun _ => β)
      (Path.Degrees.reverseVertexLabels v i₀ ((Path.nil : Path a a).cons e) (PUnit.unit, q))
      (((Path.nil : Path a a).cons e).reverseArrowLabels fun _ => {y | ν y = β})
      (fun _ : Unit => {y | ν y = β}) (fun _ : Unit => Z) {y | 0 < (ν y - β) / ν (v a i₀)} X) ↔
      (ν X - β) / ν (v b q) < 0 ∧ X - ((ν X - β) / ν (v b q)) • v b q ∉ Z := by
  have hf : (((Path.nil : Path a a).cons e).reverseArrowLabels fun _ => ν) = fun _ => ν :=
    funext fun j => by rw [Path.reverseArrowLabels_cons]; exact Fin.cases rfl (fun j => j.elim0) j
  have hc : (((Path.nil : Path a a).cons e).reverseArrowLabels fun _ => β) = fun _ => β :=
    funext fun j => by rw [Path.reverseArrowLabels_cons]; exact Fin.cases rfl (fun j => j.elim0) j
  have hP : (((Path.nil : Path a a).cons e).reverseArrowLabels fun _ => {y | ν y = β}) =
      fun _ => {y | ν y = β} :=
    funext fun j => by rw [Path.reverseArrowLabels_cons]; exact Fin.cases rfl (fun j => j.elim0) j
  have hv : Path.Degrees.reverseVertexLabels v i₀ ((Path.nil : Path a a).cons e)
      (PUnit.unit, q) = ![v b q, v a i₀] := by
    rw [Path.Degrees.reverseVertexLabels_cons, Path.Degrees.reverseVertexLabels_nil]
    funext j
    fin_cases j <;> rfl
  rw [← AdmissibleRayRealization.nonempty_singleFace_one_iff hq hZ]
  constructor
  · rintro ⟨g⟩
    exact ⟨g.congrData hf hc hv hP⟩
  · rintro ⟨g⟩
    exact ⟨g.congrData hf.symm hc.symm hv.symm hP.symm⟩

/-- Actual one-face path rays correspond to the nonzero output components with a negative
crossing parameter and a nonsingular crossing point. This includes unchanged degrees and
equal spatial velocities. -/
def pathSingleFaceComponentFiberEquiv (X : V) : (D X) ≃ (Components X) := by
  refine Equiv.ofBijective (fun r => ⟨r.1.val.2, ?_⟩) ⟨fun r s hrs => ?_, ?_⟩
  · have hq := (mem_support_iff T ℳ e i₀ x v ν hnormal r.1.val.2).mp r.1.property
    exact ⟨hq, ((nonempty_realization_iff e i₀ v ν β Z hZ r.1.val.2 (hnormal _ hq) X).mp
      ⟨r.2⟩)⟩
  · exact PathDecoratedRay.ext_history _ _ (Prod.ext rfl (congrArg Subtype.val hrs))
  · rintro ⟨q, hq, ht, hx⟩
    obtain ⟨g⟩ := (nonempty_realization_iff e i₀ v ν β Z hZ q (hnormal q hq) X).mpr
      ⟨ht, hx⟩
    exact ⟨⟨⟨(PUnit.unit, q), (mem_support_iff T ℳ e i₀ x v ν hnormal q).mpr hq⟩, g⟩,
      rfl⟩

/-- The component index is exactly the output degree of the ray. -/
@[simp]
theorem pathSingleFaceComponentFiberEquiv_apply_val (X : V) (r : D X) :
    (pathSingleFaceComponentFiberEquiv T ℳ e i₀ x v ν β Z hnormal hZ X r).val = r.1.val.2 :=
  (rfl)

/-- The ray indexed by a component carries that entire component as its final
decoration. -/
theorem pathSingleFaceComponentFiberEquiv_symm_decoration (X : V) (q : Components X) :
    ((pathSingleFaceComponentFiberEquiv T ℳ e i₀ x v ν β Z hnormal hZ X).symm q).decoration =
      (DirectSum.decompose (ℳ b) (T e x) q.val : M b) := by
  set r := (pathSingleFaceComponentFiberEquiv T ℳ e i₀ x v ν β Z hnormal hZ X).symm q
  have he : r.1.val.2 = q.val := congrArg Subtype.val
    ((pathSingleFaceComponentFiberEquiv T ℳ e i₀ x v ν β Z hnormal hZ X).apply_symm_apply q)
  rw [PathDecoratedRay.decoration_def, ← he, show r.1.val = (r.1.val.1, r.1.val.2) from rfl,
    Path.homogeneousHistory_cons_apply, Path.homogeneousHistory_nil, LinearMap.id_apply]

open Classical in
/-- Weighted evaluation over the one-arrow path is the sum of the nonzero output
components whose computed crossings are admitted. Singular and terminal crossings
contribute no rays. The formula applies at every endpoint. -/
theorem pathDecoratedEvaluation_singleFace_one_eq_sum (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x {(Path.nil : Path a a).cons e} v (fun _ => ν)
      (fun _ => SignType.sign (ν (v a i₀))) (fun _ => β) (fun _ => {y | ν y = β})
      (fun _ : Unit => {y | ν y = β}) (fun _ : Unit => Z) {y | 0 < (ν y - β) / ν (v a i₀)} X =
        ∑ q ∈ (DirectSum.decompose (ℳ b) (T e x)).support,
          if (ν X - β) / ν (v b q) < 0 ∧ X - ((ν X - β) / ν (v b q)) • v b q ∉ Z
          then (DirectSum.decompose (ℳ b) (T e x) q : M b) else 0 := by
  classical
  let F := pathSingleFaceComponentFiberEquiv T ℳ e i₀ x v ν β Z hnormal hZ X
  let s := (DirectSum.decompose (ℳ b) (T e x)).support.filter fun q =>
    (ν X - β) / ν (v b q) < 0 ∧ X - ((ν X - β) / ν (v b q)) • v b q ∉ Z
  let F' : (Components X) ≃ (s : Type _) := Equiv.subtypeEquivRight fun q => by simp [s]
  rw [pathDecoratedEvaluation_singleton]
  dsimp only
  let := Fintype.ofFinite (D X)
  let := Fintype.ofEquiv (s : Type _) F'.symm
  calc
    ∑ r : D X, r.decoration = ∑ q : Components X, (DirectSum.decompose (ℳ b) (T e x) q.val :
        M b) := by
      apply Fintype.sum_equiv F
      intro r
      have hw := pathSingleFaceComponentFiberEquiv_symm_decoration T ℳ e i₀ x v ν β Z hnormal hZ
        X (F r)
      simpa only [F, Equiv.symm_apply_apply] using hw
    _ = ∑ q : (s : Type _), (DirectSum.decompose (ℳ b) (T e x) q.val : M b) :=
      Fintype.sum_equiv F' _ _ fun _ => rfl
    _ = _ := (Finset.sum_coe_sort s
      (fun q => (DirectSum.decompose (ℳ b) (T e x) q : M b))).trans
        (by simp only [s, Finset.sum_filter])

/-- If all nonzero components cross nonsingularly at an opposite-side endpoint, the
weighted evaluation over the one-arrow path is the full propagated coefficient. Zero
input and cancellation among output coefficients are allowed. -/
theorem pathDecoratedEvaluation_singleFace_one_eq (X : V)
    (ht : (ν X - β) / ν (v a i₀) < 0)
    (hx : ∀ q, DirectSum.decompose (ℳ b) (T e x) q ≠ 0 →
      X - ((ν X - β) / ν (v b q)) • v b q ∉ Z) :
    pathDecoratedEvaluation T ℳ i₀ x {(Path.nil : Path a a).cons e} v (fun _ => ν)
      (fun _ => SignType.sign (ν (v a i₀))) (fun _ => β) (fun _ => {y | ν y = β})
      (fun _ : Unit => {y | ν y = β}) (fun _ : Unit => Z) {y | 0 < (ν y - β) / ν (v a i₀)} X =
        T e x := by
  classical
  rw [pathDecoratedEvaluation_singleFace_one_eq_sum T ℳ e i₀ x v ν β Z hnormal hZ]
  trans ∑ q ∈ (DirectSum.decompose (ℳ b) (T e x)).support,
    (DirectSum.decompose (ℳ b) (T e x) q : M b)
  · apply Finset.sum_congr rfl
    intro q hq
    have hne := DFinsupp.mem_support_iff.mp hq
    rw [ite_eq_left ⟨by rwa [hnormal q hne], hx q hne⟩]
  · exact DirectSum.sum_support_decompose (ℳ b) (T e x)

omit hnormal in
/-- If finitely many affine subspaces cover the singular set and none contains the full
face, a uniform finite set of output degrees supplies one exceptional arrangement on
whose opposite side the weighted evaluation over the one-arrow path is the propagated
coefficient, for an entire family of inputs. The family need not be linear or finite. -/
theorem exists_uniform_pathDecoratedEvaluation_singleFace_arrangement
    {H : Type*} (α : H → ℳ a i₀)
    (hnormal : ∀ y q, DirectSum.decompose (ℳ b) (T e (α y)) q ≠ 0 →
      ν (v b q) = ν (v a i₀))
    (s : Finset (ι b)) (hs : ∀ y q, DirectSum.decompose (ℳ b) (T e (α y)) q ≠ 0 → q ∈ s)
    {κ : Type*} [Finite κ] (A : κ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ y, ν y = β ∧ y ∉ A j) :
    ∃ E : ExceptionalArrangement ℝ V, ∀ X, E.IsGeneric X →
      (ν X - β) / ν (v a i₀) < 0 → ∀ y,
        pathDecoratedEvaluation T ℳ i₀ (α y) {(Path.nil : Path a a).cons e} v (fun _ => ν)
          (fun _ => SignType.sign (ν (v a i₀))) (fun _ => β) (fun _ => {y | ν y = β})
          (fun _ : Unit => {y | ν y = β}) (fun _ : Unit => Z)
          {y | 0 < (ν y - β) / ν (v a i₀)} X = T e (α y) := by
  classical
  obtain ⟨E, hE⟩ := exists_forall_notMem_sweepProjection
    (fun _ : (s : Type _) => ν) (fun _ => β)
    (fun q => (ν (v b q.val))⁻¹ • v b q.val) A (fun _ j => hA j)
  refine ⟨E, fun X hX ht y =>
    pathDecoratedEvaluation_singleFace_one_eq T ℳ e i₀ (α y) v ν β Z (hnormal y) hZ X ht ?_⟩
  intro q hq hmem
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hmem)
  exact hE X hX ⟨q, hs y q hq⟩ j (ContinuousLinearMap.sweepProjection_inv_smul_apply X ▸ hj)

/-- If finitely many affine subspaces cover the singular set and none contains the full
face, one finite exceptional arrangement makes the opposite-side weighted evaluation over
the one-arrow path equal the propagated coefficient. The arrangement is built from the
finite output support, even when the grading is infinite. -/
theorem exists_pathDecoratedEvaluation_singleFace_arrangement {κ : Type*} [Finite κ]
    (A : κ → AffineSubspace ℝ V) (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ y, ν y = β ∧ y ∉ A j) :
    ∃ E : ExceptionalArrangement ℝ V, ∀ X, E.IsGeneric X →
      (ν X - β) / ν (v a i₀) < 0 →
        pathDecoratedEvaluation T ℳ i₀ x {(Path.nil : Path a a).cons e} v (fun _ => ν)
          (fun _ => SignType.sign (ν (v a i₀))) (fun _ => β) (fun _ => {y | ν y = β})
          (fun _ : Unit => {y | ν y = β}) (fun _ : Unit => Z)
          {y | 0 < (ν y - β) / ν (v a i₀)} X = T e x := by
  classical
  obtain ⟨E, hE⟩ := exists_uniform_pathDecoratedEvaluation_singleFace_arrangement T ℳ e i₀ v ν
    β Z hZ (fun _ : Unit => x) (fun _ => hnormal) (DirectSum.decompose (ℳ b) (T e x)).support
    (fun _ _ hq => DFinsupp.mem_support_iff.mpr hq) A hcover hA
  exact ⟨E, fun X hX ht => hE X hX ht ()⟩

end Mei

namespace Mei

variable {Q R V : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V) (ν : V →L[ℝ] ℝ) (β : ℝ) (Z : Set V)

open Classical in
/-- Along the empty path, the weighted evaluation has the incoming coefficient on the
incoming half-space and zero elsewhere. Its source contains every tail in that
half-space. -/
theorem pathDecoratedEvaluation_singleFace_nil (hZ : Z ⊆ {y | ν y = β}) (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x {(Path.nil : Path a a)} v (fun _ => ν)
      (fun _ => SignType.sign (ν (v a i₀))) (fun _ => β) (fun _ => {y | ν y = β})
      (fun _ : Unit => {y | ν y = β}) (fun _ : Unit => Z) {y | 0 < (ν y - β) / ν (v a i₀)} X =
        if 0 < (ν X - β) / ν (v a i₀) then (x : M a) else 0 := by
  classical
  rw [pathDecoratedEvaluation_singleton, sum_pathDecoratedRay_eq_sum_histories]
  have hdom : X ∈ admissibleBackwardDomain ((Path.nil : Path a a).reverseArrowLabels fun _ => ν)
      ((Path.nil : Path a a).reverseArrowLabels fun _ => β)
      (Path.Degrees.reverseVertexLabels v i₀ (Path.nil : Path a a) PUnit.unit)
      ((Path.nil : Path a a).reverseArrowLabels fun _ => {y | ν y = β})
      (fun _ : Unit => {y | ν y = β}) (fun _ : Unit => Z) {y | 0 < (ν y - β) / ν (v a i₀)} ↔
        0 < (ν X - β) / ν (v a i₀) := by
    have hf : ((Path.nil : Path a a).reverseArrowLabels fun _ => ν) = fun _ : Fin 0 => ν :=
      funext fun j => j.elim0
    have hc : ((Path.nil : Path a a).reverseArrowLabels fun _ => β) = fun _ : Fin 0 => β :=
      funext fun j => j.elim0
    have hP : ((Path.nil : Path a a).reverseArrowLabels fun _ => {y | ν y = β}) =
        fun _ : Fin 0 => {y | ν y = β} :=
      funext fun j => j.elim0
    rw [hf, hc, hP, Path.Degrees.reverseVertexLabels_nil]
    exact (nonempty_admissibleRayRealization_iff ..).symm.trans
      (AdmissibleRayRealization.nonempty_singleFace_empty_iff hZ)
  by_cases hx : (x : M a) = 0
  · have hx' : x = 0 := Subtype.ext hx
    subst hx'
    simp
  · have hsupp : pathDecoratedHistorySupport T ℳ i₀ x v (fun _ => ν)
        (fun _ => SignType.sign (ν (v a i₀))) (Path.nil : Path a a) = {PUnit.unit} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun d _ => Subsingleton.elim _ _⟩
      refine (mem_pathDecoratedHistorySupport ..).mpr ⟨?_, fun j => j.elim0⟩
      rwa [Path.homogeneousHistory_nil, LinearMap.id_apply]
    rw [Fintype.sum_eq_single ⟨PUnit.unit, by rw [hsupp]; exact Finset.mem_singleton_self _⟩]
    · simp only [hdom, Path.homogeneousHistory_nil, LinearMap.id_apply]
    · intro d hd
      exact (hd (Subtype.ext rfl)).elim

end Mei
