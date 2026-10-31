/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Data.Fin.Tuple
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Concatenation of signed decorated histories

Split a surviving decorated history into two consecutive blocks. Both blocks
retain their crossing signs and normal-velocity equations, including the equation
at their junction. The later block starts with the entire homogeneous output of
the earlier block. The correspondence is bijective, and selected finite sums of
whole decorations factor through it. The selection may impose geometric endpoint
conditions on the joined history, so exterior and local histories can be grouped
without losing multiplicities or admitting extra paths.

Indices run backwards: the right block acts first. Empty blocks, zero input and
nonzero degree shifts with unchanged spatial velocity are included. These are
identities of coefficient histories; geometric realizations and their endpoint
domains remain those of `DecoratedAdmissibleRay`.

We use `Fin.appendEquiv`, `Equiv.subtypeSigmaEquivSigma` and
`homogeneousHistory_append` with the signed normal conditions of
`decoratedHistorySupport`. The correspondence and selected-sum formula refine
`homogeneousHistorySupportAppendEquiv` and `sum_ite_homogeneousHistory_append`
from `Mei.LinearAlgebra.GradedModule.History.Concatenation`.
Whole-component propagation and concatenation of
local histories follow Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3.2
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei

variable {R M Γ V : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n m : ℕ} (T : Fin n → Module.End R M) (U : Fin m → Module.End R M)
  {p₀ : Γ} (a : ℳ p₀) (v : Γ → V)
  (f : Fin n → V →L[ℝ] ℝ) (g : Fin m → V →L[ℝ] ℝ)
  (ε : Fin n → SignType) (η : Fin m → SignType)

/-- Membership in the joined signed support is exactly membership in each
block's signed support, using the whole intermediate decoration as input. -/
theorem mem_decoratedHistorySupport_append (p : Fin n → Γ) (q : Fin m → Γ) :
    Fin.append p q ∈ decoratedHistorySupport ℳ (Fin.append T U) p₀ a v
        (Fin.append f g) (Fin.append ε η) ↔
      q ∈ decoratedHistorySupport ℳ U p₀ a v g η ∧
        p ∈ decoratedHistorySupport ℳ T (Fin.snoc (α := fun _ => Γ) q p₀ 0)
          (homogeneousHistoryResult ℳ U q a) v f ε := by
  simp only [mem_decoratedHistorySupport, homogeneousHistory_append,
    LinearMap.comp_apply, coe_homogeneousHistoryResult, Fin.forall_fin_add,
    Fin.append_left, Fin.append_right, Fin.snoc_append_castAdd_succ,
    Fin.snoc_append_natAdd_succ]
  constructor
  · rintro ⟨hne, hp, hq⟩
    refine ⟨⟨?_, hq⟩, hne, hp⟩
    intro hz
    exact hne (by rw [hz, map_zero])
  · rintro ⟨⟨_, hq⟩, hne, hp⟩
    exact ⟨hne, hp, hq⟩

/-- Surviving signed decorated histories of a concatenation are precisely a
surviving first block followed by a surviving second block on its whole output.
The right block acts first. No basis or finite grading is required. -/
def decoratedHistorySupportAppendEquiv :
    (decoratedHistorySupport ℳ (Fin.append T U) p₀ a v
      (Fin.append f g) (Fin.append ε η) : Type _) ≃
      Σ q : (decoratedHistorySupport ℳ U p₀ a v g η : Type _),
        (decoratedHistorySupport ℳ T (Fin.snoc (α := fun _ => Γ) q.val p₀ 0)
          (homogeneousHistoryResult ℳ U q.val a) v f ε : Type _) := by
  let e : (Σ _q : Fin m → Γ, Fin n → Γ) ≃ (Fin (n + m) → Γ) :=
    (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodComm _ _).trans (Fin.appendEquiv n m))
  exact (e.subtypeEquivOfSubtype (p := fun r => r ∈
    decoratedHistorySupport ℳ (Fin.append T U) p₀ a v (Fin.append f g)
      (Fin.append ε η))).symm.trans
    ((Equiv.subtypeEquivRight fun qp : (Σ _q : Fin m → Γ, Fin n → Γ) =>
      mem_decoratedHistorySupport_append ℳ T U a v f g ε η qp.2 qp.1).trans
        (Equiv.subtypeSigmaEquivSigma
          (p := fun q : Fin m → Γ => q ∈ decoratedHistorySupport ℳ U p₀ a v g η)
          (q := fun (q : Fin m → Γ) (p : Fin n → Γ) =>
            p ∈ decoratedHistorySupport ℳ T (Fin.snoc (α := fun _ => Γ) q p₀ 0)
              (homogeneousHistoryResult ℳ U q a) v f ε)))

/-- Splitting retains exactly the right block's selected degrees. -/
@[simp]
theorem decoratedHistorySupportAppendEquiv_fst
    (r : (decoratedHistorySupport ℳ (Fin.append T U) p₀ a v
      (Fin.append f g) (Fin.append ε η) : Type _)) :
    (decoratedHistorySupportAppendEquiv ℳ T U a v f g ε η r).1.val =
      fun j => r.val (Fin.natAdd n j) := (rfl)

/-- Splitting retains exactly the left block's selected degrees. -/
@[simp]
theorem decoratedHistorySupportAppendEquiv_snd
    (r : (decoratedHistorySupport ℳ (Fin.append T U) p₀ a v
      (Fin.append f g) (Fin.append ε η) : Type _)) :
    (decoratedHistorySupportAppendEquiv ℳ T U a v f g ε η r).2.val =
      fun j => r.val (Fin.castAdd m j) := (rfl)

/-- Joining appends the two degree histories, without merging equal velocities. -/
@[simp]
theorem decoratedHistorySupportAppendEquiv_symm_val
    (r : Σ q : (decoratedHistorySupport ℳ U p₀ a v g η : Type _),
      (decoratedHistorySupport ℳ T (Fin.snoc (α := fun _ => Γ) q.val p₀ 0)
        (homogeneousHistoryResult ℳ U q.val a) v f ε : Type _)) :
    ((decoratedHistorySupportAppendEquiv ℳ T U a v f g ε η).symm r).val =
      Fin.append r.2.val r.1.val := (rfl)

/-- Splitting preserves the whole final decoration. -/
theorem decoratedHistorySupportAppendEquiv_decoration
    (r : (decoratedHistorySupport ℳ (Fin.append T U) p₀ a v
      (Fin.append f g) (Fin.append ε η) : Type _)) :
    homogeneousHistory ℳ T (decoratedHistorySupportAppendEquiv ℳ T U a v f g ε η r).2.val
        (homogeneousHistoryResult ℳ U
          (decoratedHistorySupportAppendEquiv ℳ T U a v f g ε η r).1.val a) =
      homogeneousHistory ℳ (Fin.append T U) r.val a := by
  simp only [decoratedHistorySupportAppendEquiv_fst,
    decoratedHistorySupportAppendEquiv_snd, coe_homogeneousHistoryResult]
  rw [← LinearMap.comp_apply, ← homogeneousHistory_append, Fin.append_castAdd_natAdd]

open Classical in
/-- Group any selected signed decorated histories by their earlier block.
Selection may depend on both blocks, including their joint geometric admission.
The inner history acts on the entire intermediate coefficient. -/
theorem sum_ite_decoratedHistory_append
    (E : (Fin n → Γ) → (Fin m → Γ) → Prop) :
    (∑ r : (decoratedHistorySupport ℳ (Fin.append T U) p₀ a v
        (Fin.append f g) (Fin.append ε η) : Type _),
      if E (fun j => r.val (Fin.castAdd m j)) (fun j => r.val (Fin.natAdd n j))
      then homogeneousHistory ℳ (Fin.append T U) r.val a else 0) =
      ∑ q : (decoratedHistorySupport ℳ U p₀ a v g η : Type _),
        ∑ p : (decoratedHistorySupport ℳ T (Fin.snoc (α := fun _ => Γ) q.val p₀ 0)
          (homogeneousHistoryResult ℳ U q.val a) v f ε : Type _),
          if E p.val q.val then homogeneousHistory ℳ T p.val
            (homogeneousHistoryResult ℳ U q.val a) else 0 := by
  classical
  let F (r : Σ q : (decoratedHistorySupport ℳ U p₀ a v g η : Type _),
      (decoratedHistorySupport ℳ T (Fin.snoc (α := fun _ => Γ) q.val p₀ 0)
        (homogeneousHistoryResult ℳ U q.val a) v f ε : Type _)) : M :=
    if E r.2.val r.1.val then homogeneousHistory ℳ T r.2.val
      (homogeneousHistoryResult ℳ U r.1.val a) else 0
  calc
    _ = ∑ r, F r := by
      apply Fintype.sum_equiv (decoratedHistorySupportAppendEquiv ℳ T U a v f g ε η)
      intro r
      simp only [F, decoratedHistorySupportAppendEquiv_fst,
        decoratedHistorySupportAppendEquiv_snd]
      split_ifs
      · exact (decoratedHistorySupportAppendEquiv_decoration ℳ T U a v f g ε η r).symm
      · rfl
    _ = _ := Fintype.sum_sigma F

open Classical in
/-- Evaluate actual rays along a joined encounter word by grouping their signed
histories into two blocks. The complete joined endpoint domain is tested, so
wall avoidance, singular avoidance and incoming-source admission are retained. -/
theorem decoratedRayEvaluation_append_eq_sum {J K : Type*}
    (c : Fin n → ℝ) (b : Fin m → ℝ) (P : Fin n → Set V) (A : Fin m → Set V)
    (W : J → Set V) (S : K → Set V) (C : Set V) (Q : V) :
    decoratedRayEvaluation ℳ (Fin.append T U) p₀ a v (Fin.append f g)
        (Fin.append c b) (Fin.append ε η) (Fin.append P A) W S C Q =
      ∑ q : (decoratedHistorySupport ℳ U p₀ a v g η : Type _),
        ∑ p : (decoratedHistorySupport ℳ T (Fin.snoc (α := fun _ => Γ) q.val p₀ 0)
          (homogeneousHistoryResult ℳ U q.val a) v f ε : Type _),
          if Q ∈ Convex.admissibleBackwardDomain (Fin.append f g) (Fin.append c b)
            (fun j => v (Fin.snoc (α := fun _ => Γ) (Fin.append p.val q.val) p₀ j))
            (Fin.append P A) W S C
          then homogeneousHistory ℳ T p.val (homogeneousHistoryResult ℳ U q.val a)
          else 0 := by
  rw [decoratedRayEvaluation_eq_sum]
  simpa only [Fin.append_castAdd_natAdd] using
    sum_ite_decoratedHistory_append ℳ T U a v f g ε η
      (fun p q => Q ∈ Convex.admissibleBackwardDomain (Fin.append f g) (Fin.append c b)
        (fun j => v (Fin.snoc (α := fun _ => Γ) (Fin.append p q) p₀ j))
        (Fin.append P A) W S C)

end Mei
