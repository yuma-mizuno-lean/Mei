/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

/-!
# Linearity of cutoff decorated-ray evaluation

The weighted evaluation of the entire cutoff ray family is linear in its
incoming homogeneous coefficient. Individual ray fibers need not be additive:
whole decorations can cancel, and a scalar can kill a decoration. A common finite
inventory, independent of the coefficient, allows those zero weights to be kept
while taking sums of linear propagation maps. Its bound is the existing geometric
encounter bound, including encounters that preserve the degree.

`cutoffDecoratedEvaluationLinearMap` has the original actual-ray evaluation as
its value. It supplies linear branch totals for matching families and local
resolution identities, without finiteness assumptions on homogeneous modules.
For rational polyhedral data, one finite exceptional arrangement makes this
entire linear map locally constant, simultaneously for every input.

The proof uses `CutoffDecoratedRay.length_le`,
`cutoffDecoratedEvaluation_def` and the linear maps `homogeneousHistory`.
Whole-component propagation follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Definition 2.10 and
Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)

-- This inventory retains zero decorations, so it does not depend on the input.
private abbrev CutoffEvaluationIndex (k : ℕ) :=
  Σ l : {l : List J // l.length ≤ Nat.card (d.cutoff k) * Nat.card J},
    Fin l.val.length → d.cutoff k

private instance [Finite J] (k : ℕ) : Finite (CutoffEvaluationIndex (J := J) d k) := by
  let L := {l : List J // l.length ≤ Nat.card (d.cutoff k) * Nat.card J}
  let : Finite L := (List.finite_length_le J _).to_subtype
  infer_instance

private def cutoffEvaluationCondition (k : ℕ) (Q : V)
    (b : CutoffEvaluationIndex (J := J) d k) : Prop :=
  let p := fun j => (b.2 j : Γ)
  (∀ i j, i ≤ j → p i - p j ∈ d.monoid) ∧
    (∀ j, f (b.1.val.get j) (v (p j)) =
      f (b.1.val.get j) (v (Fin.snoc (α := fun _ => Γ) p 0 j.succ)) ∧
        SignType.sign (f (b.1.val.get j) (v (p j))) = ε (b.1.val.get j)) ∧
    Q ∈ admissibleBackwardDomain (fun j => f (b.1.val.get j))
      (fun j => c (b.1.val.get j))
      (fun j => v (Fin.snoc (α := fun _ => Γ) p 0 j))
      (fun j => P (b.1.val.get j)) W S C

open Classical in
private def cutoffEvaluationSummand (k : ℕ) (Q : V)
    (b : CutoffEvaluationIndex (J := J) d k) : ℳ 0 →ₗ[R] M :=
  if cutoffEvaluationCondition d v f c ε P W S C k Q b then
    (homogeneousHistory ℳ (fun j => T (b.1.val.get j)) (fun j => (b.2 j : Γ))).comp
      (ℳ 0).subtype
  else 0

private def CutoffDecoratedRay.evaluationIndex [Finite J] {k : ℕ} {Q : V} {a : ℳ 0}
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    CutoffEvaluationIndex (J := J) d k :=
  ⟨⟨r.itinerary, r.length_le⟩, fun j => ⟨r.realization.1.val j, r.degree_mem j⟩⟩

private theorem CutoffDecoratedRay.evaluationIndex_injective [Finite J]
    {k : ℕ} {Q : V} {a : ℳ 0} :
    Function.Injective (CutoffDecoratedRay.evaluationIndex d ℳ T v f c ε P W S C
      (k := k) (Q := Q) (a := a)) := by
  rintro ⟨l, ⟨⟨p, hp⟩, r⟩, hm, hd⟩ ⟨l', ⟨⟨p', hp'⟩, r'⟩, hm', hd'⟩ he
  dsimp only [CutoffDecoratedRay.evaluationIndex] at he
  have hl : l = l' := congrArg (fun b => b.1.val) he
  subst l'
  have hpq : p = p' := by
    have h := (Sigma.mk.inj_iff.mp he).2
    have h' := eq_of_heq h
    exact funext fun j => congrArg Subtype.val (congrFun h' j)
  subst p'
  cases Subsingleton.elim r r'
  rfl

private theorem CutoffDecoratedRay.evaluationSummand [Finite J]
    {k : ℕ} {Q : V} {a : ℳ 0}
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    cutoffEvaluationSummand d ℳ T v f c ε P W S C k Q
      (r.evaluationIndex d ℳ T v f c ε P W S C) a = r.decoration := by
  classical
  have hgood : cutoffEvaluationCondition d v f c ε P W S C k Q
      (r.evaluationIndex d ℳ T v f c ε P W S C) :=
    ⟨r.degree_sub_mem, (mem_decoratedHistorySupport ..).mp r.realization.1.property |>.2,
      r.realization.2.mem_admissibleBackwardDomain⟩
  rw [cutoffEvaluationSummand, ite_eq_left hgood, LinearMap.comp_apply,
    Submodule.subtype_apply, CutoffDecoratedRay.decoration_eq]
  rfl

private theorem cutoffDecoratedEvaluation_eq_uniform_sum [Finite J]
    (k : ℕ) (Q : V) (a : ℳ 0) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
      let := Fintype.ofFinite (CutoffEvaluationIndex (J := J) d k)
      ∑ b : CutoffEvaluationIndex (J := J) d k,
        cutoffEvaluationSummand d ℳ T v f c ε P W S C k Q b a := by
  classical
  let := Fintype.ofFinite (CutoffEvaluationIndex (J := J) d k)
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  rw [cutoffDecoratedEvaluation_def]
  apply Finset.sum_bij_ne_zero
    (fun r _ _ => r.evaluationIndex d ℳ T v f c ε P W S C) (by simp)
  · intro r _ _ s _ _ he
    exact CutoffDecoratedRay.evaluationIndex_injective d ℳ T v f c ε P W S C
      (k := k) (Q := Q) (a := a) he
  · intro b _ hb
    have hgood : cutoffEvaluationCondition d v f c ε P W S C k Q b := by
      by_contra hn
      simp [cutoffEvaluationSummand, hn] at hb
    have hne : homogeneousHistory ℳ (fun j => T (b.1.val.get j))
        (fun j => (b.2 j : Γ)) a ≠ 0 := by
      simpa only [cutoffEvaluationSummand, ite_eq_left hgood, LinearMap.comp_apply,
        Submodule.subtype_apply] using hb
    let r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q :=
      { itinerary := b.1.val
        realization := ⟨⟨fun j => (b.2 j : Γ),
          (mem_decoratedHistorySupport ..).mpr ⟨hne, hgood.2.1⟩⟩,
          admissibleRayRealization _ _ _ _ _ _ _ _ hgood.2.2⟩
        degree_mem := fun j => (b.2 j).property
        degree_sub_mem := hgood.1 }
    refine ⟨r, Finset.mem_univ _, r.decoration_ne_zero, ?_⟩
    rcases b with ⟨⟨l, hl⟩, p⟩
    rfl
  · intro r _ _
    exact (r.evaluationSummand d ℳ T v f c ε P W S C).symm

/-- Weighted evaluation of all cutoff decorated rays, as a linear map on the
incoming homogeneous piece. Whole decorations killed by addition or scalar
multiplication disappear from the actual ray fiber automatically. -/
def cutoffDecoratedEvaluationLinearMap [Finite J] (k : ℕ) (Q : V) : ℳ 0 →ₗ[R] M := by
  classical
  let := Fintype.ofFinite (CutoffEvaluationIndex (J := J) d k)
  exact
    { toFun := fun a => cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q
      map_add' := fun a b => by
        simp only [cutoffDecoratedEvaluation_eq_uniform_sum, map_add, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        simp only [cutoffDecoratedEvaluation_eq_uniform_sum, map_smul, Finset.smul_sum,
          RingHom.id_apply] }

/-- The linear map evaluates the original finite fiber of actual decorated rays. -/
@[simp]
theorem cutoffDecoratedEvaluationLinearMap_apply [Finite J] (k : ℕ) (Q : V) (a : ℳ 0) :
    cutoffDecoratedEvaluationLinearMap d ℳ T v f c ε P W S C k Q a =
      cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q := (rfl)

/-- Whole-component ray sums are additive, including cancellation of histories. -/
@[simp]
theorem cutoffDecoratedEvaluation_add [Finite J] (k : ℕ) (Q : V) (a b : ℳ 0) :
    cutoffDecoratedEvaluation d ℳ T (a + b) v f c ε P W S C k Q =
      cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q +
        cutoffDecoratedEvaluation d ℳ T b v f c ε P W S C k Q :=
  (cutoffDecoratedEvaluationLinearMap d ℳ T v f c ε P W S C k Q).map_add a b

/-- Scalar multiplication commutes with ray sums even when it kills some whole
components; no regularity assumption on the scalar is required. -/
@[simp]
theorem cutoffDecoratedEvaluation_smul [Finite J] (k : ℕ) (Q : V) (r : R) (a : ℳ 0) :
    cutoffDecoratedEvaluation d ℳ T (r • a) v f c ε P W S C k Q =
      r • cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q :=
  (cutoffDecoratedEvaluationLinearMap d ℳ T v f c ε P W S C k Q).map_smul r a

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ) [Finite J] [Finite K]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

include hf hP hW hS hC

/-- One finite exceptional arrangement makes the entire evaluation linear map
locally constant. The arrangement and the neighborhood work simultaneously for
all incoming coefficients, even when their surviving ray types differ. -/
theorem exists_cutoffDecoratedEvaluationLinearMap_eventually_eq (k : ℕ) :
    ∃ E : ExceptionalArrangement V, ∀ Q, E.IsGeneric Q → ∀ᶠ Q' in nhds Q,
      cutoffDecoratedEvaluationLinearMap d ℳ T (fun q => i (w q)) f c ε P W S C k Q' =
        cutoffDecoratedEvaluationLinearMap d ℳ T (fun q => i (w q)) f c ε P W S C k Q := by
  classical
  let D (b : CutoffEvaluationIndex (J := J) d k) : Set V :=
    {Q | cutoffEvaluationCondition d (fun q => i (w q)) f c ε P W S C k Q b}
  have hD (b : CutoffEvaluationIndex (J := J) d k) : IsRationalSemilinear h (D b) := by
    let p := fun j => (b.2 j : Γ)
    by_cases hd : ∀ a b, a ≤ b → p a - p b ∈ d.monoid
    · by_cases hn : ∀ j, f (b.1.val.get j) (i (w (p j))) =
          f (b.1.val.get j) (i (w (Fin.snoc (α := fun _ => Γ) p 0 j.succ))) ∧
            SignType.sign (f (b.1.val.get j) (i (w (p j)))) = ε (b.1.val.get j)
      · have he : D b = admissibleBackwardDomain
            (fun j => f (b.1.val.get j)) (fun j => c (b.1.val.get j))
            (fun j => i (w (Fin.snoc (α := fun _ => Γ) p 0 j)))
            (fun j => P (b.1.val.get j)) W S C := by
          ext Q
          exact ⟨fun hQ => hQ.2.2, fun hQ => ⟨hd, hn, hQ⟩⟩
        rw [he]
        exact isRationalSemilinear_admissibleBackwardDomain
          (fun j => f (b.1.val.get j)) (fun j => c (b.1.val.get j))
          (fun j => P (b.1.val.get j)) W S C
          (fun j => w (Fin.snoc (α := fun _ => Γ) p 0 j))
          (fun j => hf _) (fun j => hP _) hW hS hC
      · have he : D b = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun _ hQ => hn hQ.2.1
        rw [he]
        exact IsRationalSemilinear.empty h
    · have he : D b = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun _ hQ => hd hQ.1
      rw [he]
      exact IsRationalSemilinear.empty h
  obtain ⟨E, _, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement hD
  refine ⟨E, fun Q hQ => (hstable Q hQ).mono fun Q' hQQ' => ?_⟩
  ext a
  simp only [cutoffDecoratedEvaluationLinearMap_apply,
    cutoffDecoratedEvaluation_eq_uniform_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hb : cutoffEvaluationCondition d (fun q => i (w q)) f c ε P W S C k Q' b ↔
      cutoffEvaluationCondition d (fun q => i (w q)) f c ε P W S C k Q b := hQQ' b
  simp only [cutoffEvaluationSummand]
  rw [hb]

end Rational

end Mei
