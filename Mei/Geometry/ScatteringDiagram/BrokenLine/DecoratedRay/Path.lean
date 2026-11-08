/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Basic

/-!
# Fixed-itinerary decorated rays as rays along quiver paths

A finite itinerary `g : Fin n → α` of encounter labels is the path
`Quiver.SingleObj.pathOfFn g` in the one-object quiver on `α`, and its degree histories
are those of the path (`Quiver.SingleObj.degreesPathOfFn`). Under these identifications
the actual decorated rays of the itinerary, `DecoratedAdmissibleRay`, are exactly the
actual decorated rays along the path, `PathDecoratedRay`, with every chamber module the
same graded module. The comparison retains the endpoint, the complete degree history,
the geometric ray with its encounter parameters and incoming tail, and the whole final
decoration. Hence the fixed-itinerary weighted evaluation is the sum over the path ray
fiber.

Thus the fixed-itinerary carrier is a presentation of the common varying-chamber
construction, specialized to a one-object quiver. We use
`homogeneousHistory_eq_pathOfFn`, `Quiver.SingleObj.reverseArrowLabels_pathOfFn` and
`Quiver.SingleObj.reverseVertexLabels_degreesPathOfFn`.
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {R M Γ V J K α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : α → Module.End R M) (p₀ : Γ) (a : ℳ p₀) (velocity : Γ → V)
  (f : α → V →L[ℝ] ℝ) (c : α → ℝ) (ε : α → SignType) (P : α → Set V)
  (W : J → Set V) (S : K → Set V) (C : Set V) {n : ℕ} (g : Fin n → α)

local notation "Ray" Q:max => DecoratedAdmissibleRay ℳ (fun j => T (g j)) p₀ a velocity
  (fun j => f (g j)) (fun j => c (g j)) (fun j => ε (g j)) (fun j => P (g j)) W S C Q
local notation "PRay" Q:max => PathDecoratedRay (Q := SingleObj α) (M := fun _ => M)
  (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) p₀ a (fun _ => velocity) (fun e => f e)
  (fun e => ε e) (fun e => c e) (fun e => P e) W S C (SingleObj.pathOfFn g) Q

private theorem cast_cast_length (j : Fin n) :
    Fin.cast (SingleObj.length_pathOfFn g) (Fin.cast (SingleObj.length_pathOfFn g).symm j) = j :=
  Fin.ext rfl

private theorem cast_cast_length' (j : Fin (n + 1)) :
    Fin.cast (congrArg (fun k => k + 1) (SingleObj.length_pathOfFn g))
      (Fin.cast (congrArg (fun k => k + 1) (SingleObj.length_pathOfFn g).symm) j) = j :=
  Fin.ext rfl

/-- A degree history survives along the itinerary exactly when the corresponding
path history survives: both conditions consist of a nonzero whole final decoration,
preserved normal velocities and the prescribed crossing signs. -/
theorem degreesPathOfFn_mem_pathDecoratedHistorySupport_iff (d : Fin n → Γ) :
    SingleObj.degreesPathOfFn Γ g d ∈ pathDecoratedHistorySupport (Q := SingleObj α)
      (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) p₀ a
      (fun _ => velocity) (fun e => f e) (fun e => ε e) (SingleObj.pathOfFn g) ↔
      d ∈ decoratedHistorySupport ℳ (fun j => T (g j)) p₀ a velocity (fun j => f (g j))
        (fun j => ε (g j)) := by
  rw [mem_pathDecoratedHistorySupport, mem_decoratedHistorySupport,
    ← homogeneousHistory_eq_pathOfFn]
  refine and_congr_right fun _ => ?_
  rw [← (finCongr (SingleObj.length_pathOfFn g)).symm.forall_congr_right]
  refine forall_congr' fun j => ?_
  simp only [finCongr_symm, finCongr_apply, SingleObj.reverseArrowLabels_pathOfFn,
    SingleObj.reverseVertexLabels_degreesPathOfFn, cast_cast_length]
  have h₁ : Fin.cast (congrArg (fun k => k + 1) (SingleObj.length_pathOfFn g))
      (Fin.cast (SingleObj.length_pathOfFn g).symm j).castSucc = j.castSucc := Fin.ext rfl
  have h₂ : Fin.cast (congrArg (fun k => k + 1) (SingleObj.length_pathOfFn g))
      (Fin.cast (SingleObj.length_pathOfFn g).symm j).succ = j.succ := Fin.ext rfl
  rw [h₁, h₂, Fin.snoc_castSucc]

/-- The actual decorated rays of a finite itinerary are the actual decorated rays along
its path in the one-object quiver of labels. The comparison retains the complete degree
history, the geometric ray and all encounter parameters. -/
def decoratedAdmissibleRayPathEquiv (Q : V) : Ray Q ≃ PRay Q where
  toFun r := ⟨⟨SingleObj.degreesPathOfFn Γ g r.1.val,
      (degreesPathOfFn_mem_pathDecoratedHistorySupport_iff ℳ T p₀ a velocity f ε g
        r.1.val).mpr r.1.property⟩,
    r.2.congrLength (SingleObj.length_pathOfFn g).symm _ _ _ _
      (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn, cast_cast_length])
      (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn, cast_cast_length])
      (fun j => by rw [SingleObj.reverseVertexLabels_degreesPathOfFn, cast_cast_length'])
      (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn, cast_cast_length])⟩
  invFun s := ⟨⟨(SingleObj.degreesPathOfFn Γ g).symm s.1.val,
      (degreesPathOfFn_mem_pathDecoratedHistorySupport_iff ℳ T p₀ a velocity f ε g _).mp
        (by rw [Equiv.apply_symm_apply]; exact s.1.property)⟩,
    s.2.congrLength (SingleObj.length_pathOfFn g) _ _ _ _
      (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn])
      (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn])
      (fun j => by
        conv_lhs => rw [← Equiv.apply_symm_apply (SingleObj.degreesPathOfFn Γ g) s.1.val]
        rw [SingleObj.reverseVertexLabels_degreesPathOfFn])
      (fun j => by rw [SingleObj.reverseArrowLabels_pathOfFn])⟩
  left_inv r := DecoratedAdmissibleRay.ext_history (Equiv.symm_apply_apply _ _)
  right_inv s := PathDecoratedRay.ext_history _ _ (Equiv.apply_symm_apply _ _)

/-- The comparison carries the degree history through `degreesPathOfFn`. -/
@[simp]
theorem decoratedAdmissibleRayPathEquiv_history (Q : V) (r : Ray Q) :
    (decoratedAdmissibleRayPathEquiv ℳ T p₀ a velocity f c ε P W S C g Q r).1.val =
      SingleObj.degreesPathOfFn Γ g r.1.val := (rfl)

/-- The comparison retains the entire geometric ray, including the incoming tail. -/
@[simp]
theorem decoratedAdmissibleRayPathEquiv_ray (Q : V) (r : Ray Q) :
    (decoratedAdmissibleRayPathEquiv ℳ T p₀ a velocity f c ε P W S C g Q r).2.ray = r.2.ray :=
  AdmissibleRayRealization.ray_congrLength _ _ _ _ _ _ _ _ _ _

/-- The comparison preserves the whole final decoration. -/
@[simp]
theorem decoratedAdmissibleRayPathEquiv_decoration (Q : V) (r : Ray Q) :
    (decoratedAdmissibleRayPathEquiv ℳ T p₀ a velocity f c ε P W S C g Q r).decoration =
      r.decoration 0 := by
  rw [PathDecoratedRay.decoration_def, decoratedAdmissibleRayPathEquiv_history,
    DecoratedAdmissibleRay.decoration_zero, homogeneousHistory_eq_pathOfFn]

/-- The fixed-itinerary weighted evaluation is the sum of the final decorations over
the actual rays along the itinerary's path. -/
theorem decoratedRayEvaluation_eq_sum_pathDecoratedRay (Q : V) :
    decoratedRayEvaluation ℳ (fun j => T (g j)) p₀ a velocity (fun j => f (g j))
      (fun j => c (g j)) (fun j => ε (g j)) (fun j => P (g j)) W S C Q =
      let := Fintype.ofFinite (PRay Q)
      ∑ r : PRay Q, r.decoration := by
  let := Fintype.ofFinite (Ray Q)
  let := Fintype.ofFinite (PRay Q)
  rw [decoratedRayEvaluation_def]
  exact Fintype.sum_equiv (decoratedAdmissibleRayPathEquiv ℳ T p₀ a velocity f c ε P W S C g Q)
    _ _ fun r => (decoratedAdmissibleRayPathEquiv_decoration ℳ T p₀ a velocity f c ε P W S C g Q
      r).symm

end Mei
