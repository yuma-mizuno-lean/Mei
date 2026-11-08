/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Truncation
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient

/-!
# Truncation of actual BCH ray fibers

For completed wall labels and an original homogeneous incoming coefficient, the
order-`k` ray fiber is exactly the part of any higher-order fiber with final relative
degree at most `k`. Quotient transitions preserve the full degree-labelled encounter
word, geometric path, incoming tail, times and whole final decoration of each survivor.
The comparisons are identities at equal cutoffs and compose through intermediate orders.

The comparison acts on actual fibers. The fixed
encounter alphabet retains walls whose labels become identities after truncation.
No generic endpoint, finiteness of that alphabet or nonzero incoming coefficient is assumed.

We specialize the coefficient and cutoff comparisons to
`ModuleFiltration.transition_truncatedBCHAction` and the inherited shifted gradings.
The interpretation of truncation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.10 and Theorem 2.14
(arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M V J K I : Type*}
  [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0)
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V) (Q : V)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "G" => fun k : ℕ =>
  TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "T" => fun (k : ℕ) (j : J) => LinearEquiv.toLinearMap
  (ModuleFiltration.truncatedBCHAction F d ℒ k (CompletedGroup.projection k (g j)))
local notation "input" => fun k : ℕ => (Subtype.mk
  (Submodule.Quotient.mk (a : shiftedSubmodule ℳ d.monoid p))
  (Iff.mpr (mem_shiftedQuotientGrading_iff d ℳ p)
    (Exists.intro a (And.intro (Subtype.property a) rfl))) : G k 0)
local notation "Rays" => fun k : ℕ => CutoffDecoratedRay d (G k) (T k) (input k)
  v f c ε P W S C k Q

/-- A ray survives coefficient truncation exactly when its final relative degree
is retained. All earlier decorations then survive as well by positive propagation. -/
theorem transition_cutoffBCHRay_decoration_ne_zero_iff {k l : ℕ} (h : k ≤ l)
    (β : Rays l) :
    (F).transition h β.decoration ≠ 0 ↔ d.degree β.finalDegree ≤ k := by
  rw [ne_eq, d.transition_eq_zero_iff_of_mem_shiftedQuotientGrading ℳ p h β.decoration_mem]
  simp only [β.decoration_ne_zero, false_or, not_lt]

omit [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [LieModule R L M] in
private theorem input_transition {k l : ℕ} (h : k ≤ l) :
    regradeBase (G l) (G k) ((F).transition h) (AddMonoidHom.id Γ)
      (fun _ _ hx => d.transition_mem_shiftedQuotientGrading ℳ p h hx) (input l) = input k := by
  apply Subtype.ext
  rw [coe_regradeBase, ModuleFiltration.transition_mk]

/-- The smaller actual ray fiber is the subfiber of a larger one whose final
relative degrees are retained. Truncation maps the entire final coefficients. -/
def cutoffBCHRayTruncationEquiv {k l : ℕ} (h : k ≤ l) :
    {β : Rays l // d.degree β.finalDegree ≤ k} ≃ Rays k := by
  have hT (j : J) : ((F).transition h).comp (T l j) = (T k j).comp ((F).transition h) := by
    apply LinearMap.ext
    intro x
    have hg : (d.truncationMap ℒ h).bchGroupMap
        (CompletedGroup.projection l (g j)) = CompletedGroup.projection k (g j) :=
      CompletedGroup.map_projection k l h (g j)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg] using
      (F).transition_truncatedBCHAction d ℒ h (CompletedGroup.projection l (g j)) x
  let e := cutoffDecoratedRayCoefficientTruncationEquiv d (G l) (G k) ((F).transition h)
    (fun _ _ hx => d.transition_mem_shiftedQuotientGrading ℳ p h hx) (T l) (T k) hT
    (input l) v f c ε P W S C h
    (fun _ _ hx hne => d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p hx hne) Q
  have ha := input_transition d ℒ ℳ p a h
  exact ((Equiv.subtypeEquivRight (fun β =>
    (d.transition_cutoffBCHRay_decoration_ne_zero_iff ℒ ℳ p g a v f c ε P W S C Q h β).symm)).trans
      e).trans (Equiv.cast (congrArg (fun a =>
        CutoffDecoratedRay d (G k) (T k) a v f c ε P W S C k Q) ha))

local notation "E" => d.cutoffBCHRayTruncationEquiv ℒ ℳ p g a v f c ε P W S C Q

/-- Every degree-labelled encounter is preserved, including unchanged degrees
and nonzero degree shifts with zero spatial projection. -/
@[simp]
theorem cutoffBCHRayTruncationEquiv_degreeItinerary {k l : ℕ} (h : k ≤ l)
    (β : {β : Rays l // d.degree β.finalDegree ≤ k}) :
    (E h β).degreeItinerary = β.val.degreeItinerary := by
  simp only [cutoffBCHRayTruncationEquiv, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply, Equiv.cast_apply]
  rw [CutoffDecoratedRay.degreeItinerary_cast_input _ (input_transition d ℒ ℳ p a h),
    cutoffDecoratedRayCoefficientTruncationEquiv_degreeItinerary]

/-- The final relative degree is unchanged by truncation. -/
@[simp]
theorem cutoffBCHRayTruncationEquiv_finalDegree {k l : ℕ} (h : k ≤ l)
    (β : {β : Rays l // d.degree β.finalDegree ≤ k}) :
    (E h β).finalDegree = β.val.finalDegree := by
  rw [← CutoffDecoratedRay.headD_map_fst_degreeItinerary,
    cutoffBCHRayTruncationEquiv_degreeItinerary, CutoffDecoratedRay.headD_map_fst_degreeItinerary]

/-- The entire path, and therefore the actual incoming tail, is unchanged. -/
@[simp]
theorem cutoffBCHRayTruncationEquiv_ray {k l : ℕ} (h : k ≤ l)
    (β : {β : Rays l // d.degree β.finalDegree ≤ k}) :
    (E h β).realization.2.ray = β.val.realization.2.ray := by
  simp only [cutoffBCHRayTruncationEquiv, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply, Equiv.cast_apply]
  simp only [CutoffDecoratedRay.ray_cast_input _ (input_transition d ℒ ℳ p a h),
    cutoffDecoratedRayCoefficientTruncationEquiv_ray]

/-- The times of all recorded encounters are unchanged. -/
@[simp]
theorem cutoffBCHRayTruncationEquiv_parameter {k l : ℕ} (h : k ≤ l)
    (β : {β : Rays l // d.degree β.finalDegree ≤ k}) :
    HEq (E h β).realization.2.parameter β.val.realization.2.parameter := by
  simp only [cutoffBCHRayTruncationEquiv, Equiv.trans_apply, Equiv.subtypeEquivRight_apply,
    Equiv.cast_apply]
  refine HEq.trans (CutoffDecoratedRay.parameter_cast_input _
    (input_transition d ℒ ℳ p a h)) ?_
  exact cutoffDecoratedRayCoefficientTruncationEquiv_parameter d (G l) (G k)
    ((F).transition h) _ (T l) (T k) _ (input l) v f c ε P W S C h _ Q _

/-- The final whole decoration is the quotient transition of the original one. -/
@[simp↓]
theorem cutoffBCHRayTruncationEquiv_decoration {k l : ℕ} (h : k ≤ l)
    (β : {β : Rays l // d.degree β.finalDegree ≤ k}) :
    (E h β).decoration = (F).transition h β.val.decoration := by
  simp only [cutoffBCHRayTruncationEquiv, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply, Equiv.cast_apply]
  rw [CutoffDecoratedRay.decoration_cast_input _ (input_transition d ℒ ℳ p a h),
    cutoffDecoratedRayCoefficientTruncationEquiv_decoration]

/-- Truncation at the same order is the identity on the actual fiber. -/
@[simp]
theorem cutoffBCHRayTruncationEquiv_refl (k : ℕ) (β : Rays k) :
    E (le_refl k) ⟨β, (d.mem_cutoff.mp β.finalDegree_mem_cutoff).2⟩ = β := by
  apply CutoffDecoratedRay.degreeItinerary_injective
  exact d.cutoffBCHRayTruncationEquiv_degreeItinerary ℒ ℳ p g a v f c ε P W S C Q _ _

/-- Truncating an actual ray through an intermediate order equals direct
truncation. Survival at the final order suffices for both comparisons. -/
theorem cutoffBCHRayTruncationEquiv_comp {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m)
    (β : {β : Rays m // d.degree β.finalDegree ≤ k}) :
    E h ⟨E h' ⟨β.val, β.property.trans (Int.ofNat_le.mpr h)⟩,
      by simpa only [cutoffBCHRayTruncationEquiv_finalDegree] using β.property⟩ =
      E (h.trans h') β := by
  apply CutoffDecoratedRay.degreeItinerary_injective
  simp only [cutoffBCHRayTruncationEquiv_degreeItinerary]

end Mei.PositiveDegrees
