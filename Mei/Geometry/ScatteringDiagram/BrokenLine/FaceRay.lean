/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.LinearAlgebra.GradedCorrespondence.History

/-!
# Decorated rays through chains of chamber modules

Fix an itinerary of `n` encounters, indexed backwards from the endpoint. Segment `j`
lies in a chamber with its own coefficient module `M j`, graded by its own degree type
`ι j`, and the encounter `j` propagates coefficients from `M (j + 1)` to `M j` by a
linear map `T j`. For a face carrying a graded correspondence this map is its
zero-extended transfer `GradedCorrespondence.totalTransfer`, so the chamber module may
change across the face. Each segment has the spatial velocity of its own degree in its
own chamber.

A decorated face ray at an endpoint is a nonzero chain history of `T` with the
prescribed crossing signs and preserved normal velocities, together with its actual
admissible backward realization. Every decoration is a whole homogeneous component of
the propagated coefficient. There are finitely many such rays at each endpoint, and
`faceRayEvaluation` sums their final decorations.

Chamber maps that intertwine the propagation maps along velocity-preserving degree maps
send the evaluation of an input to the evaluation of its image (`map_faceRayEvaluation`).
Source histories with the same image are grouped first, so cancellation is allowed and no
injectivity is needed.

When all chambers carry the same graded module, the face rays are exactly the decorated
admissible rays of `BrokenLine/DecoratedRay.lean`, with the same realizations and
decorations, and the evaluations agree. In particular, ordinary walls are the
specialization in which every face carries the graph correspondence of its wall action.

This is the fixed-itinerary part of the common broken-line construction: slab faces and
ordinary walls are instances of one definition. Summation over itineraries, the bijection
of rays under coefficient embeddings, and the slab instance are separate steps.
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei

universe u v w

variable {R : Type u} [Semiring R]
  {M : ℕ → Type v} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]
  {ι : ℕ → Type w} [∀ k, DecidableEq (ι k)] (ℳ : ∀ k, ι k → Submodule R (M k))
  [∀ k, DirectSum.Decomposition (ℳ k)]
  {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (T : (j : Fin n) → M (j + 1) →ₗ[R] M j) (p₀ : ι n) (a : ℳ n p₀)
  (velocity : ∀ k, ι k → V) (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (ε : Fin n → SignType) (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

/-- The spatial velocity of each segment of a degree history, indexed backwards. Segment
`j < n` has the velocity of `p j` in chamber `j`; the incoming segment has that of `p₀`. -/
def segmentVelocity (p : (j : Fin n) → ι j) (j : Fin (n + 1)) : V :=
  if h : (j : ℕ) < n then velocity j (p ⟨j, h⟩) else velocity n p₀

omit [∀ k, DecidableEq (ι k)] [NormedAddCommGroup V] [NormedSpace ℝ V] in
variable {velocity p₀} in
/-- A segment before the incoming tail moves with the velocity of its selected degree. -/
@[simp]
theorem segmentVelocity_castSucc (p : (j : Fin n) → ι j) (j : Fin n) :
    segmentVelocity p₀ velocity p j.castSucc = velocity j (p j) := by
  simp [segmentVelocity]

omit [∀ k, DecidableEq (ι k)] [NormedAddCommGroup V] [NormedSpace ℝ V] in
variable {velocity p₀} in
/-- The incoming segment moves with the velocity of the incoming degree. -/
@[simp]
theorem segmentVelocity_last (p : (j : Fin n) → ι j) :
    segmentVelocity p₀ velocity p (Fin.last n) = velocity n p₀ := by
  simp [segmentVelocity]

open Classical in
/-- Surviving chain histories compatible with the prescribed crossing signs and with
preservation of normal velocity at each encounter. -/
def faceHistorySupport : Finset ((j : Fin n) → ι j) :=
  (chainHistorySupport ℳ T (a : M n)).filter fun p => ∀ j : Fin n,
    f j (segmentVelocity p₀ velocity p j.castSucc) =
        f j (segmentVelocity p₀ velocity p j.succ) ∧
      SignType.sign (f j (segmentVelocity p₀ velocity p j.castSucc)) = ε j

/-- Membership keeps precisely the nonzero histories satisfying both normal conditions. -/
@[simp]
theorem mem_faceHistorySupport (p : (j : Fin n) → ι j) :
    p ∈ faceHistorySupport ℳ T p₀ a velocity f ε ↔
      chainHistory ℳ T p a ≠ 0 ∧ ∀ j : Fin n,
        f j (segmentVelocity p₀ velocity p j.castSucc) =
            f j (segmentVelocity p₀ velocity p j.succ) ∧
          SignType.sign (f j (segmentVelocity p₀ velocity p j.castSucc)) = ε j := by
  classical
  simp [faceHistorySupport]

/-- Actual admissible rays through the chain, decorated by surviving whole-component
chain histories. `velocity` is the negative of forward path velocity. -/
abbrev FaceDecoratedRay (Q : V) :=
  Σ p : (faceHistorySupport ℳ T p₀ a velocity f ε : Type _),
    AdmissibleRayRealization f c (segmentVelocity p₀ velocity p.val) P W S C Q

namespace FaceDecoratedRay

variable {ℳ T p₀ a velocity f c ε P W S C} {Q : V}

/-- The whole final decoration, in the endpoint chamber. -/
def decoration (r : FaceDecoratedRay ℳ T p₀ a velocity f c ε P W S C Q) : M 0 :=
  chainHistory ℳ T r.1.val a

/-- The final decoration of a decorated face ray is nonzero. -/
theorem decoration_ne_zero (r : FaceDecoratedRay ℳ T p₀ a velocity f c ε P W S C Q) :
    r.decoration ≠ 0 :=
  ((mem_faceHistorySupport ℳ T p₀ a velocity f ε r.1.val).mp r.1.property).1

/-- Normal velocity is preserved across every recorded encounter. -/
theorem normal_velocity_eq (r : FaceDecoratedRay ℳ T p₀ a velocity f c ε P W S C Q)
    (j : Fin n) :
    f j (segmentVelocity p₀ velocity r.1.val j.castSucc) =
      f j (segmentVelocity p₀ velocity r.1.val j.succ) :=
  ((mem_faceHistorySupport ℳ T p₀ a velocity f ε r.1.val).mp r.1.property).2 j |>.1

/-- The direction determines exactly the prescribed signed crossing. -/
theorem crossing_sign (r : FaceDecoratedRay ℳ T p₀ a velocity f c ε P W S C Q)
    (j : Fin n) :
    SignType.sign (f j (segmentVelocity p₀ velocity r.1.val j.castSucc)) = ε j :=
  ((mem_faceHistorySupport ℳ T p₀ a velocity f ε r.1.val).mp r.1.property).2 j |>.2

end FaceDecoratedRay

local notation "D" Q => FaceDecoratedRay ℳ T p₀ a velocity f c ε P W S C Q
local notation "A" p => admissibleBackwardDomain f c (segmentVelocity p₀ velocity p) P W S C

/-- A face ray exists exactly when some surviving history with the prescribed crossing
signs and preserved normal velocities has an admitted endpoint. -/
theorem nonempty_faceDecoratedRay_iff (Q : V) :
    Nonempty (D Q) ↔ ∃ p ∈ faceHistorySupport ℳ T p₀ a velocity f ε, Q ∈ A p := by
  constructor
  · rintro ⟨⟨p, r⟩⟩
    exact ⟨p.val, p.property, r.mem_admissibleBackwardDomain⟩
  · rintro ⟨p, hp, hQ⟩
    exact ⟨⟨⟨p, hp⟩, admissibleRayRealization _ _ _ _ _ _ _ _ hQ⟩⟩

/-- The finite sum of whole final decorations on the actual evaluation fiber. -/
def faceRayEvaluation (Q : V) : M 0 :=
  let := Fintype.ofFinite (D Q)
  ∑ r : D Q, r.decoration

open Classical in
/-- Evaluate by summing exactly the surviving histories admitted by the full geometric
endpoint domain. Coincident domains retain distinct histories. -/
theorem faceRayEvaluation_eq_sum (Q : V) :
    faceRayEvaluation ℳ T p₀ a velocity f c ε P W S C Q =
      ∑ p : (faceHistorySupport ℳ T p₀ a velocity f ε : Type _),
        if Q ∈ A p.val then chainHistory ℳ T p.val a else 0 := by
  classical
  let := Fintype.ofFinite (D Q)
  let e := admissibleRayFiberEquiv W S Q (fun _ :
    (faceHistorySupport ℳ T p₀ a velocity f ε : Type _) => n)
    (fun _ => f) (fun _ => c) (fun p => segmentVelocity p₀ velocity p.val)
    (fun _ => P) (fun _ => C)
  rw [faceRayEvaluation]
  trans ∑ p : {p : (faceHistorySupport ℳ T p₀ a velocity f ε : Type _) // Q ∈ A p.val},
    chainHistory ℳ T p.val.val a
  · apply Fintype.sum_equiv e
    intro r
    simp only [FaceDecoratedRay.decoration, e, admissibleRayFiberEquiv_apply_val]
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun p : (faceHistorySupport ℳ T p₀ a velocity f ε : Type _) => Q ∈ A p.val)
      (Finset.univ.filter fun p : (faceHistorySupport ℳ T p₀ a velocity f ε : Type _) =>
        Q ∈ A p.val) (by intro p; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun p => chainHistory ℳ T p.val a)).symm

open Classical in
/-- Sum over all nonzero chain histories, selecting precisely those with the prescribed
normal velocities, signs and full geometric endpoint admission. -/
theorem faceRayEvaluation_eq_sum_chainHistory (Q : V) :
    faceRayEvaluation ℳ T p₀ a velocity f c ε P W S C Q =
      ∑ p ∈ chainHistorySupport ℳ T (a : M n),
        if (∀ j : Fin n, f j (segmentVelocity p₀ velocity p j.castSucc) =
            f j (segmentVelocity p₀ velocity p j.succ) ∧
              SignType.sign (f j (segmentVelocity p₀ velocity p j.castSucc)) = ε j) ∧
            Q ∈ A p
        then chainHistory ℳ T p a else 0 := by
  rw [faceRayEvaluation_eq_sum]
  trans ∑ p ∈ faceHistorySupport ℳ T p₀ a velocity f ε,
    if Q ∈ A p then chainHistory ℳ T p a else 0
  · exact Finset.sum_coe_sort _ (fun p => if Q ∈ A p then chainHistory ℳ T p a else 0)
  · rw [faceHistorySupport, Finset.sum_filter]
    exact Finset.sum_congr rfl fun p _ => (ite_and _ _ _ _).symm

/-- Zero input contributes no decorated face rays. -/
instance (Q : V) : IsEmpty (FaceDecoratedRay ℳ T p₀ 0 velocity f c ε P W S C Q) :=
  ⟨fun r => r.decoration_ne_zero (by simp [FaceDecoratedRay.decoration])⟩

/-- Vanished input has zero weighted evaluation. -/
@[simp]
theorem faceRayEvaluation_zero (Q : V) :
    faceRayEvaluation ℳ T p₀ 0 velocity f c ε P W S C Q = 0 := by
  classical
  simp [faceRayEvaluation]

section CoefficientMap

/-! ### Coefficient maps -/

variable {N : ℕ → Type*} [∀ k, AddCommMonoid (N k)] [∀ k, Module R (N k)]
  {κ : ℕ → Type*} [∀ k, DecidableEq (κ k)] (𝓝 : ∀ k, κ k → Submodule R (N k))
  [∀ k, DirectSum.Decomposition (𝓝 k)]
  (U : (j : Fin n) → N (j + 1) →ₗ[R] N j) (velocity' : ∀ k, κ k → V)
  (r : ∀ k, M k →ₗ[R] N k) (σ : ∀ k, ι k → κ k)
  (hr : ∀ k i x, x ∈ ℳ k i → r k x ∈ 𝓝 k (σ k i))
  (hT : ∀ j : Fin n, (r j).comp (T j) = (U j).comp (r (j + 1)))
  (hv : ∀ k i, velocity' k (σ k i) = velocity k i)

omit [∀ k, DecidableEq (ι k)] [∀ k, DecidableEq (κ k)] [NormedAddCommGroup V]
  [NormedSpace ℝ V] in
include hv in
/-- Velocity-preserving degree maps keep every segment velocity. -/
theorem segmentVelocity_map (p : (j : Fin n) → ι j) :
    segmentVelocity (σ n p₀) velocity' (fun j => σ j (p j)) =
      segmentVelocity p₀ velocity p := by
  funext j
  simp only [segmentVelocity]
  split_ifs <;> exact hv _ _

include hr hT hv in
/-- Coefficient maps preserve the weighted evaluation after grouping histories. Chamber
maps intertwining the propagation maps along velocity-preserving degree maps send the
evaluation of an input to the evaluation of its image. Source histories with the same
image are added, so cancellation may remove target histories; neither the chamber maps
nor the degree maps need be injective. -/
theorem map_faceRayEvaluation (Q : V) :
    r 0 (faceRayEvaluation ℳ T p₀ a velocity f c ε P W S C Q) =
      faceRayEvaluation 𝓝 U (σ n p₀) ⟨r n a, hr n p₀ a a.property⟩ velocity' f c ε P W S C Q := by
  classical
  rw [faceRayEvaluation_eq_sum_chainHistory, faceRayEvaluation_eq_sum_chainHistory]
  have h := map_sum_ite_chainHistory ℳ 𝓝 r σ hr T U hT
    (fun q => (∀ j : Fin n, f j (segmentVelocity (σ n p₀) velocity' q j.castSucc) =
        f j (segmentVelocity (σ n p₀) velocity' q j.succ) ∧
          SignType.sign (f j (segmentVelocity (σ n p₀) velocity' q j.castSucc)) = ε j) ∧
        Q ∈ admissibleBackwardDomain f c (segmentVelocity (σ n p₀) velocity' q) P W S C)
    (a : M n)
  simp only [segmentVelocity_map p₀ velocity velocity' σ hv] at h
  convert h

end CoefficientMap

section Constant

/-! ### Constant chambers -/

variable {N : Type v} {κ : Type w} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝒩 : κ → Submodule R N) [DirectSum.Decomposition 𝒩]
  (U : Fin n → Module.End R N) (q₀ : κ) (b : 𝒩 q₀) (vel : κ → V)

omit [DecidableEq κ] [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- With constant chambers the segment velocities are those of the appended degrees. -/
theorem segmentVelocity_const (p : Fin n → κ) :
    segmentVelocity (ι := fun _ => κ) q₀ (fun _ => vel) p =
      fun j => vel (Fin.snoc (α := fun _ => κ) p q₀ j) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [segmentVelocity_last, Fin.snoc_last]
  · rw [segmentVelocity_castSucc, Fin.snoc_castSucc]

/-- With constant chambers the surviving face histories are the decorated histories. -/
theorem faceHistorySupport_const :
    faceHistorySupport (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩) U q₀ b
      (fun _ => vel) f ε = decoratedHistorySupport 𝒩 U q₀ b vel f ε := by
  ext p
  simp only [mem_faceHistorySupport, mem_decoratedHistorySupport, segmentVelocity_const,
    Fin.snoc_castSucc, ← homogeneousHistory_eq_chainHistory]

/-- Admissible realizations for equal segment velocities, keeping the ray. -/
private def realizationCongr {Q : V} {v v' : Fin (n + 1) → V} (h : v = v') :
    AdmissibleRayRealization f c v P W S C Q ≃ AdmissibleRayRealization f c v' P W S C Q := by
  subst h
  exact Equiv.refl _

private theorem realizationCongr_ray {Q : V} {v v' : Fin (n + 1) → V} (h : v = v')
    (r : AdmissibleRayRealization f c v P W S C Q) :
    (realizationCongr f c P W S C h r).ray = r.ray := by
  subst h
  rfl

/-- With constant chambers, decorated face rays are the decorated admissible rays, with
the same histories and realizations. -/
def faceDecoratedRayEquivConst (Q : V) :
    FaceDecoratedRay (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩) U q₀ b (fun _ => vel)
        f c ε P W S C Q ≃ DecoratedAdmissibleRay 𝒩 U q₀ b vel f c ε P W S C Q :=
  Equiv.sigmaCongr
    (Equiv.subtypeEquivRight fun p => by rw [faceHistorySupport_const])
    fun p => realizationCongr f c P W S C (segmentVelocity_const q₀ vel p.val)

/-- The equivalence keeps the degree history. -/
@[simp]
theorem faceDecoratedRayEquivConst_fst (Q : V)
    (r : FaceDecoratedRay (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩) U q₀ b
      (fun _ => vel) f c ε P W S C Q) :
    ((faceDecoratedRayEquivConst f c ε P W S C 𝒩 U q₀ b vel Q r).1 : Fin n → κ) = r.1.val :=
  (rfl)

/-- The equivalence keeps the actual ray, including its incoming tail. -/
@[simp]
theorem faceDecoratedRayEquivConst_ray (Q : V)
    (r : FaceDecoratedRay (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩) U q₀ b
      (fun _ => vel) f c ε P W S C Q) :
    (faceDecoratedRayEquivConst f c ε P W S C 𝒩 U q₀ b vel Q r).2.ray = r.2.ray :=
  realizationCongr_ray f c P W S C _ _

/-- The equivalence keeps the final decoration. -/
theorem faceDecoratedRayEquivConst_decoration (Q : V)
    (r : FaceDecoratedRay (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩) U q₀ b
      (fun _ => vel) f c ε P W S C Q) :
    (faceDecoratedRayEquivConst f c ε P W S C 𝒩 U q₀ b vel Q r).decoration 0 =
      r.decoration := by
  rw [DecoratedAdmissibleRay.decoration_zero, faceDecoratedRayEquivConst_fst,
    homogeneousHistory_eq_chainHistory]
  rfl

/-- With constant chambers the face-ray evaluation is the decorated-ray evaluation. -/
theorem faceRayEvaluation_const (Q : V) :
    faceRayEvaluation (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩) U q₀ b (fun _ => vel)
        f c ε P W S C Q = decoratedRayEvaluation 𝒩 U q₀ b vel f c ε P W S C Q := by
  classical
  let := Fintype.ofFinite (FaceDecoratedRay (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩)
    U q₀ b (fun _ => vel) f c ε P W S C Q)
  let := Fintype.ofFinite (DecoratedAdmissibleRay 𝒩 U q₀ b vel f c ε P W S C Q)
  rw [faceRayEvaluation, decoratedRayEvaluation_def]
  exact Fintype.sum_equiv (faceDecoratedRayEquivConst f c ε P W S C 𝒩 U q₀ b vel Q) _ _
    fun r => (faceDecoratedRayEquivConst_decoration f c ε P W S C 𝒩 U q₀ b vel Q r).symm

/-- Ordinary walls are the graph-correspondence case: propagating through the graph
correspondences of the wall actions gives the decorated-ray evaluation of those actions. -/
theorem faceRayEvaluation_graph (e : Fin n → N ≃ₗ[R] N) (Q : V) :
    faceRayEvaluation (M := fun _ => N) (ι := fun _ => κ) (fun _ => 𝒩)
        (fun j => (GradedCorrespondence.graph 𝒩 𝒩 (e j)).totalTransfer) q₀ b (fun _ => vel)
        f c ε P W S C Q =
      decoratedRayEvaluation 𝒩 (fun j => (e j).toLinearMap) q₀ b vel f c ε P W S C Q := by
  simp only [GradedCorrespondence.graph_totalTransfer]
  exact faceRayEvaluation_const f c ε P W S C 𝒩 (fun j => (e j).toLinearMap) q₀ b vel Q

end Constant

end Mei
