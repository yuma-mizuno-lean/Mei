/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

/-!
# Stationary incoming decorations

Preservation of normal velocity prevents a stationary incoming decoration from
having any transverse encounter. Consequently its full cutoff evaluation is its
incoming coefficient at every endpoint admitted by the source and avoiding the
walls and singular sets. This includes zero input, which contributes no rays.

The finite-ray carrier permits stationary paths; these represent constant incoming
sections rather than proper incoming half-lines. We characterize the entire fiber,
including source and avoidance conditions, without assuming that other degrees
have zero spatial velocity or that propagation maps are identities.

We use `DecoratedAdmissibleRay.normal_velocity_eq`, the unique backward realization,
and the all-itinerary sum `cutoffDecoratedEvaluation`. The whole-component and
constant theta conventions follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.10 and the convention following
equation (15) (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [AddCommGroup Γ] {d : PositiveDegrees Γ}
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

namespace CutoffDecoratedRay

/-- Every cutoff ray with stationary incoming degree has empty encounter word,
even when the alphabet includes nonidentity propagation maps. -/
@[simp]
theorem itinerary_eq_nil_of_velocity_eq_zero
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) (hv : v 0 = 0) :
    r.itinerary = [] :=
  List.length_eq_zero_iff.mp (r.realization.encounter_count_eq_zero_of_velocity_eq_zero hv)

/-- With stationary incoming degree, the entire realized path is constant. -/
@[simp]
theorem ray_eq_straight_of_velocity_eq_zero
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) (hv : v 0 = 0) :
    r.realization.2.ray = FiniteAffineRay.straight Q 0 := by
  have hn := r.itinerary_eq_nil_of_velocity_eq_zero hv
  obtain ⟨l, β, hmem, hsub⟩ := r
  dsimp only at hn
  subst l
  obtain ⟨hpos, _, hr⟩ := β.2.eq_backwardRay
  simpa only [backwardRay_zero, Fin.snoc_zero, hv] using hr

/-- Stationary rays retain the whole incoming coefficient. -/
@[simp↓] -- Retain the stationary normal form before expanding homogeneous histories.
theorem decoration_eq_input_of_velocity_eq_zero
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) (hv : v 0 = 0) :
    r.decoration = (a : M) := by
  have hn := r.itinerary_eq_nil_of_velocity_eq_zero hv
  rw [decoration_eq]
  obtain ⟨l, β, hmem, hsub⟩ := r
  dsimp only at hn
  subst l
  simp

/-- The stationary ray with nonzero input, at an admitted allowed endpoint.
No propagation map is applied, and no encounter is recorded. -/
def stationary (ha : (a : M) ≠ 0) (hv : v 0 = 0)
    (hC : Q ∈ C) (hW : ∀ j, Q ∉ W j) (hS : ∀ j, Q ∉ S j) :
    CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q where
  itinerary := []
  realization := ⟨⟨Fin.elim0, by simpa using ha⟩, {
    ray := FiniteAffineRay.straight Q 0
    parameter := fun _ => 0
    parameter_zero := rfl
    strictAnti_parameter := fun i j hij => by have := Fin.eq_zero i; have := Fin.eq_zero j; omega
    transverse := fun j => Fin.elim0 j
    endpoint_eq := by simp
    directionAt_eq := fun j => by
      simp only [List.length_nil] at j ⊢
      rw [FiniteAffineRay.directionAt_straight, Fin.eq_zero j, Fin.snoc_zero, hv]
    bends_recorded := by simp
    height_eq := fun j => Fin.elim0 j
    incidence := fun j => Fin.elim0 j
    avoids_walls := fun j t _ _ => by simpa using hW j
    incoming := Filter.Eventually.of_forall fun t => by simpa using hC
    avoids_singular := fun j t _ => by simpa using hS j
    off_walls := hW }⟩
  degree_mem := fun j => Fin.elim0 j
  degree_sub_mem := fun j => Fin.elim0 j

/-- The stationary constructor records no encounters. -/
@[simp high]
theorem itinerary_stationary (ha : (a : M) ≠ 0) (hv : v 0 = 0)
    (hC : Q ∈ C) (hW : ∀ j, Q ∉ W j) (hS : ∀ j, Q ∉ S j) :
    (stationary (d := d) (T := T) (f := f) (c := c) (ε := ε) (P := P)
      (k := k) ha hv hC hW hS).itinerary = [] := (rfl)

/-- The stationary constructor realizes the constant path at the endpoint. -/
@[simp high]
theorem ray_stationary (ha : (a : M) ≠ 0) (hv : v 0 = 0)
    (hC : Q ∈ C) (hW : ∀ j, Q ∉ W j) (hS : ∀ j, Q ∉ S j) :
    (stationary (d := d) (T := T) (f := f) (c := c) (ε := ε) (P := P)
      (k := k) ha hv hC hW hS).realization.2.ray = FiniteAffineRay.straight Q 0 := (rfl)

/-- Stationary fibers have at most one member, without any finiteness assumption
on the encounter alphabet. -/
theorem subsingleton_of_velocity_eq_zero (hv : v 0 = 0) :
    Subsingleton (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) := by
  refine ⟨fun r s => ?_⟩
  have hr := r.itinerary_eq_nil_of_velocity_eq_zero hv
  have hs := s.itinerary_eq_nil_of_velocity_eq_zero hv
  obtain ⟨l, β, hmem, hsub⟩ := r
  obtain ⟨l', β', hmem', hsub'⟩ := s
  dsimp only at hr hs
  subst l
  subst l'
  have hβ : β = β' := by
    obtain ⟨p, g⟩ := β
    obtain ⟨p', g'⟩ := β'
    have hp : p = p' := Subtype.ext (funext fun j => Fin.elim0 j)
    subst p'
    exact congrArg (Sigma.mk p) (Subsingleton.elim _ _)
  cases hβ
  rfl

/-- Exact existence criterion for a stationary contribution: nonzero input,
source admission, and avoidance of every wall and singular set. -/
@[simp]
theorem nonempty_iff_of_velocity_eq_zero (hv : v 0 = 0) :
    Nonempty (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) ↔
      (a : M) ≠ 0 ∧ Q ∈ C ∧ (∀ j, Q ∉ W j) ∧ ∀ j, Q ∉ S j := by
  constructor
  · rintro ⟨r⟩
    have hr := r.ray_eq_straight_of_velocity_eq_zero hv
    refine ⟨?_, ?_, r.realization.2.off_walls, ?_⟩
    · rw [← r.decoration_eq_input_of_velocity_eq_zero hv]
      exact r.decoration_ne_zero
    · simpa only [hr, FiniteAffineRay.straight_apply, smul_zero, zero_vadd,
        eventually_const] using r.realization.2.incoming
    · intro j
      simpa only [hr, FiniteAffineRay.straight_apply, smul_zero, zero_vadd] using
        r.realization.2.avoids_singular j 0 le_rfl
  · rintro ⟨ha, hC, hW, hS⟩
    exact ⟨stationary ha hv hC hW hS⟩

end CutoffDecoratedRay

/-- Full stationary weighted evaluation is the incoming coefficient. Zero input
is allowed; source and avoidance hypotheses apply only to the endpoint. -/
@[simp]
theorem cutoffDecoratedEvaluation_of_velocity_eq_zero [Finite J]
    (hv : v 0 = 0) (hC : Q ∈ C) (hW : ∀ j, Q ∉ W j) (hS : ∀ j, Q ∉ S j) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q = (a : M) := by
  classical
  by_cases ha : (a : M) = 0
  · have ha' : a = 0 := Subtype.ext ha
    simp [ha', cutoffDecoratedEvaluation_zero]
  · let := CutoffDecoratedRay.subsingleton_of_velocity_eq_zero
      (d := d) (ℳ := ℳ) (T := T) (a := a) (f := f) (c := c)
      (ε := ε) (P := P) (W := W) (S := S) (C := C) (k := k) (Q := Q) hv
    let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    let r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q :=
      CutoffDecoratedRay.stationary ha hv hC hW hS
    rw [cutoffDecoratedEvaluation_def]
    exact (Fintype.sum_subsingleton _ r).trans
      (r.decoration_eq_input_of_velocity_eq_zero hv)

open Classical in
/-- At every endpoint, stationary evaluation is the input precisely on the
source away from the walls and singular sets, and is zero elsewhere. -/
theorem cutoffDecoratedEvaluation_eq_ite_of_velocity_eq_zero [Finite J]
    (hv : v 0 = 0) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
      if Q ∈ C ∧ (∀ j, Q ∉ W j) ∧ (∀ j, Q ∉ S j) then (a : M) else 0 := by
  classical
  split_ifs with hQ
  · exact cutoffDecoratedEvaluation_of_velocity_eq_zero hv hQ.1 hQ.2.1 hQ.2.2
  · have hi : IsEmpty (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :=
      not_nonempty_iff.mp fun hr => hQ
        ((CutoffDecoratedRay.nonempty_iff_of_velocity_eq_zero hv).mp hr).2
    rw [cutoffDecoratedEvaluation_def]
    simp

end Mei
