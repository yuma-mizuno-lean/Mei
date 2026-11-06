/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.LinearAlgebra.GradedModule.History.Erasure
public import Mei.Geometry.Convex.Sweep.Admissible.Terminal
public import Mei.Geometry.Convex.Sweep.Admissible.Itinerary

/-!
# Uniqueness of leading decorated rays

A cutoff ray ending in relative degree zero has degree zero on every segment:
positive increments cannot cancel in a sharp positive monoid. Its whole decoration
is the incoming coefficient when diagonal propagation fixes homogeneous inputs,
and its path is straight, including all unchanged-degree encounters.

If recorded encounters belong to the obstacle family and the signed encounter
labels distinguish events at a point in the incoming direction, there is at most
one such ray, across all finite itineraries. The leading component of the full
sum is therefore the input or zero, according to existence. An admissible
realization in the incoming direction supplies existence for nonzero input and
recovers the incoming coefficient, including when the coefficient is zero.

We use `PositiveDegrees.eq_zero_of_mem_of_neg_mem`, the constant-degree result
`homogeneousHistory_const_of_decompose_self`, and
`AdmissibleRayRealization.encounterParameters_eq_of_ray_eq`. The leading term
is the initial case of the broken-line recursion in Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

namespace CutoffDecoratedRay

/-- Decorate an admissible realization in the incoming direction by the constant
degree-zero history. Diagonal propagation preserves its entire nonzero input,
even when the propagation maps themselves are not identities. -/
def ofLeadingRealization (word : List J)
    (g : AdmissibleRayRealization (fun j => f (word.get j))
      (fun j => c (word.get j)) (fun _ => v 0) (fun j => P (word.get j)) W S C Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (ha : (a : M) ≠ 0)
    (hε : ∀ j : Fin word.length, SignType.sign (f (word.get j) (v 0)) = ε (word.get j)) :
    CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q := by
  have hb : ∀ i : Fin (word.length + 1),
      Fin.snoc (α := fun _ => Γ) (fun _ : Fin word.length => 0) 0 i = 0 := by
    intro i
    exact Fin.lastCases (by simp) (fun j => by simp) i
  refine ⟨word, ⟨⟨fun _ => 0, (mem_decoratedHistorySupport ..).mpr ⟨?_, ?_⟩⟩,
    g.congrVelocity (funext fun i => by rw [hb i])⟩, ?_, ?_⟩
  · rwa [homogeneousHistory_const_of_decompose_self
      (fun j => hT (word.get j)) a.property]
  · intro j
    exact ⟨by rw [hb j.succ], hε j⟩
  · intro j
    exact d.mem_cutoff.mpr ⟨d.monoid.zero_mem, by simp⟩
  · intro i j _
    simp

/-- The leading constructor retains the prescribed encounter word. -/
@[simp]
theorem itinerary_ofLeadingRealization (word : List J)
    (g : AdmissibleRayRealization (fun j => f (word.get j))
      (fun j => c (word.get j)) (fun _ => v 0) (fun j => P (word.get j)) W S C Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (ha : (a : M) ≠ 0)
    (hε : ∀ j : Fin word.length, SignType.sign (f (word.get j) (v 0)) = ε (word.get j)) :
    (ofLeadingRealization (d := d) (k := k) word g hT ha hε).itinerary = word := (rfl)

/-- Every selected degree of the leading constructor is zero. -/
@[simp]
theorem history_ofLeadingRealization (word : List J)
    (g : AdmissibleRayRealization (fun j => f (word.get j))
      (fun j => c (word.get j)) (fun _ => v 0) (fun j => P (word.get j)) W S C Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (ha : (a : M) ≠ 0)
    (hε : ∀ j : Fin word.length, SignType.sign (f (word.get j) (v 0)) = ε (word.get j)) :
    (ofLeadingRealization (d := d) (k := k) word g hT ha hε).realization.1.val =
      fun _ => 0 := (rfl)

/-- The constructed ray has leading output, including for an empty itinerary. -/
@[simp↓] -- Recognize the leading constructor before simplifying its degree history.
theorem final_eq_zero_ofLeadingRealization (word : List J)
    (g : AdmissibleRayRealization (fun j => f (word.get j))
      (fun j => c (word.get j)) (fun _ => v 0) (fun j => P (word.get j)) W S C Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (ha : (a : M) ≠ 0)
    (hε : ∀ j : Fin word.length, SignType.sign (f (word.get j) (v 0)) = ε (word.get j)) :
    Fin.snoc (α := fun _ => Γ)
      (ofLeadingRealization (d := d) (k := k) word g hT ha hε).realization.1.val 0 0 = 0 := by
  rw [history_ofLeadingRealization]
  exact Fin.lastCases (by simp) (fun j => by simp) 0

/-- The leading constructor retains the entire supplied geometric ray. -/
@[simp]
theorem ray_ofLeadingRealization (word : List J)
    (g : AdmissibleRayRealization (fun j => f (word.get j))
      (fun j => c (word.get j)) (fun _ => v 0) (fun j => P (word.get j)) W S C Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (ha : (a : M) ≠ 0)
    (hε : ∀ j : Fin word.length, SignType.sign (f (word.get j) (v 0)) = ε (word.get j)) :
    (ofLeadingRealization (d := d) (k := k) word g hT ha hε).realization.2.ray = g.ray := by
  simp only [ofLeadingRealization, AdmissibleRayRealization.ray_congrVelocity]

/-- The leading constructor retains every encounter parameter. -/
@[simp↓] -- Rewrite the whole parameter list before `List.ofFn_succ` expands it.
theorem encounterParameters_ofLeadingRealization (word : List J)
    (g : AdmissibleRayRealization (fun j => f (word.get j))
      (fun j => c (word.get j)) (fun _ => v 0) (fun j => P (word.get j)) W S C Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (ha : (a : M) ≠ 0)
    (hε : ∀ j : Fin word.length, SignType.sign (f (word.get j) (v 0)) = ε (word.get j)) :
    List.ofFn (ofLeadingRealization (d := d) (k := k) word g hT ha hε).realization.2.parameter =
      List.ofFn g.parameter := by
  simp only [ofLeadingRealization, AdmissibleRayRealization.parameter_congrVelocity]

/-- A leading output cannot have any earlier positive relative degree.
The appended incoming degree and every recorded output degree are zero. -/
theorem degrees_eq_zero_of_final_eq_zero
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hr : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0) :
    ∀ i, Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 i = 0 := by
  intro i
  refine Fin.lastCases (by simp) (fun j => ?_) i
  rw [Fin.snoc_castSucc]
  let z : Fin r.itinerary.length := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
  have hz : r.realization.1.val z = 0 := by
    have hi : z.castSucc = (0 : Fin (r.itinerary.length + 1)) := Fin.ext rfl
    simpa only [← hi, Fin.snoc_castSucc] using hr
  have hneg := r.degree_sub_mem z j (by simp [z, Fin.le_def])
  rw [hz, zero_sub] at hneg
  exact d.eq_zero_of_mem_of_neg_mem (d.mem_cutoff.mp (r.degree_mem j)).1 hneg

/-- The whole decoration of a leading ray is its incoming coefficient. -/
theorem decoration_eq_input_of_final_eq_zero
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (hr : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0) :
    r.decoration = (a : M) := by
  have hh : r.realization.1.val = fun _ => 0 := by
    funext j
    simpa only [Fin.snoc_castSucc] using r.degrees_eq_zero_of_final_eq_zero hr j.castSucc
  rw [decoration_eq, hh]
  exact homogeneousHistory_const_of_decompose_self (fun j => hT (r.itinerary.get j)) a.property

/-- A leading ray follows the incoming straight half-line through the endpoint.
Recorded encounters that preserve degree remain present. -/
theorem ray_eq_of_final_eq_zero
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hr : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0)
    {t : ℝ} (ht : t ≤ 0) :
    r.realization.2.ray t = Q - t • v 0 := by
  have hd := r.degrees_eq_zero_of_final_eq_zero hr
  simpa only [hd] using r.realization.2.ray_eq_endpoint_sub_smul_of_directions_eq
    (fun i => by rw [hd i, hd 0]) ht

/-- Leading rays are unique across all encounter itineraries. Every recorded
support must lie on an obstacle, and at a point on the incoming straight path,
at most one incident encounter label has the prescribed crossing sign.
Neither existence nor nonzero incoming spatial direction is assumed. -/
theorem itinerary_eq_of_final_eq_zero
    (r s : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hr : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0)
    (hs : Fin.snoc (α := fun _ => Γ) s.realization.1.val 0 0 = 0)
    (hP : ∀ j, P j ⊆ ⋃ b, W b)
    (hsep : ∀ t < (0 : ℝ), ∀ j l,
      Q - t • v 0 ∈ P j → Q - t • v 0 ∈ P l →
      SignType.sign (f j (v 0)) = ε j →
      SignType.sign (f l (v 0)) = ε l → j = l) : r.itinerary = s.itinerary := by
  have hp := r.realization.2.encounterParameters_eq_of_ray_eq s.realization.2
    (fun t ht => (r.ray_eq_of_final_eq_zero hr ht).trans
      (s.ray_eq_of_final_eq_zero hs ht).symm)
    (fun j => hP (r.itinerary.get j)) (fun j => hP (s.itinerary.get j))
  have hl : r.itinerary.length = s.itinerary.length := by
    simpa only [List.length_ofFn] using congrArg List.length hp
  apply List.ext_get hl
  intro i hi hi'
  let j : Fin r.itinerary.length := ⟨i, hi⟩
  let l : Fin s.itinerary.length := ⟨i, hi'⟩
  have ht : r.realization.2.parameter j.succ = s.realization.2.parameter l.succ := by
    have he := congrArg (fun ts : List ℝ => ts[i]?) hp
    simpa [j, l, hi, hi'] using he
  have hneg : r.realization.2.parameter j.succ < 0 := by
    simpa only [r.realization.2.parameter_zero] using
      r.realization.2.strictAnti_parameter (Fin.succ_pos j)
  apply hsep _ hneg
  · simpa only [r.ray_eq_of_final_eq_zero hr hneg.le] using r.realization.2.incidence j
  · rw [ht]
    simpa only [s.ray_eq_of_final_eq_zero hs (ht ▸ hneg.le)] using
      s.realization.2.incidence l
  · have hd : r.realization.1.val j = 0 := by
      simpa only [Fin.snoc_castSucc] using r.degrees_eq_zero_of_final_eq_zero hr j.castSucc
    simpa only [hd] using r.realization.crossing_sign j
  · have hd : s.realization.1.val l = 0 := by
      simpa only [Fin.snoc_castSucc] using s.degrees_eq_zero_of_final_eq_zero hs l.castSucc
    simpa only [hd] using s.realization.crossing_sign l

/-- There is at most one leading contribution, including its entire degree
history and actual admissible realization. The separation condition permits
different signed labels on the same geometric support. -/
theorem eq_of_final_eq_zero
    (r s : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hr : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0)
    (hs : Fin.snoc (α := fun _ => Γ) s.realization.1.val 0 0 = 0)
    (hP : ∀ j, P j ⊆ ⋃ b, W b)
    (hsep : ∀ t < (0 : ℝ), ∀ j l,
      Q - t • v 0 ∈ P j → Q - t • v 0 ∈ P l →
      SignType.sign (f j (v 0)) = ε j →
      SignType.sign (f l (v 0)) = ε l → j = l) : r = s := by
  have hword := r.itinerary_eq_of_final_eq_zero s hr hs hP hsep
  obtain ⟨word, β, hmem, hsub⟩ := r
  obtain ⟨word', β', hmem', hsub'⟩ := s
  dsimp only at hword
  subst word'
  have hb : β.1 = β'.1 := by
    apply Subtype.ext
    funext j
    exact ((by simpa only [Fin.snoc_castSucc] using
      degrees_eq_zero_of_final_eq_zero ⟨word, β, hmem, hsub⟩ hr j.castSucc) :
        β.1.val j = 0).trans
      ((by simpa only [Fin.snoc_castSucc] using
        degrees_eq_zero_of_final_eq_zero ⟨word, β', hmem', hsub'⟩ hs j.castSucc) :
        β'.1.val j = 0).symm
  have hβ : β = β' := by
    apply Sigma.ext hb
    obtain ⟨b, g⟩ := β
    obtain ⟨b', g'⟩ := β'
    dsimp only at hb
    cases hb
    exact heq_of_eq (Subsingleton.elim _ _)
  cases hβ
  rfl

end CutoffDecoratedRay

open Classical in
/-- The leading component of the full cutoff evaluation is the input if a
leading ray exists, and zero otherwise. Signed separation prevents overcounting
across different encounter words. Source admission and all avoidance conditions
remain part of the existence test. -/
theorem decompose_cutoffDecoratedEvaluation_zero_eq_ite [Finite J]
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (hP : ∀ j, P j ⊆ ⋃ b, W b)
    (hsep : ∀ t < (0 : ℝ), ∀ j l,
      Q - t • v 0 ∈ P j → Q - t • v 0 ∈ P l →
      SignType.sign (f j (v 0)) = ε j →
      SignType.sign (f l (v 0)) = ε l → j = l) :
    (DirectSum.decompose ℳ (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) 0 : M) =
      if ∃ r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
        Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0 then (a : M) else 0 := by
  classical
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  let leading (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :=
    Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 = 0
  have hcomponent (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
      (DirectSum.decompose ℳ r.decoration 0 : M) = if leading r then (a : M) else 0 := by
    split_ifs with hr
    · rw [r.decoration_eq_input_of_final_eq_zero hT hr]
      exact DirectSum.decompose_of_mem_same ℳ a.property
    · have hmem := homogeneousHistoryStage_mem_snoc ℳ
        (fun j => T (r.itinerary.get j)) r.realization.1.val 0 a 0
      rw [homogeneousHistoryStage_zero, ← r.decoration_eq] at hmem
      exact DirectSum.decompose_of_mem_ne ℳ hmem hr
  rw [cutoffDecoratedEvaluation_def]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  simp_rw [hcomponent]
  by_cases hex : ∃ r, leading r
  · obtain ⟨r, hr⟩ := hex
    rw [ite_eq_left ⟨r, hr⟩, Finset.sum_eq_single r]
    · exact ite_eq_left hr
    · intro s _ hsr
      exact ite_eq_right fun hs => hsr (s.eq_of_final_eq_zero r hs hr hP hsep)
    · simp
  · rw [ite_eq_right hex]
    exact Finset.sum_eq_zero fun r _ => ite_eq_right (fun hr => hex ⟨r, hr⟩)

/-- An admissible incoming straight realization recovers the leading coefficient
of the entire cutoff sum. The input may vanish. The geometric realization retains
the full source and obstacle conditions and records the signs of its encounters. -/
theorem decompose_cutoffDecoratedEvaluation_zero [Finite J] (word : List J)
    (g : AdmissibleRayRealization (fun j => f (word.get j))
      (fun j => c (word.get j)) (fun _ => v 0) (fun j => P (word.get j)) W S C Q)
    (hT : ∀ j x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T j x) 0 : M) = x)
    (hε : ∀ j : Fin word.length, SignType.sign (f (word.get j) (v 0)) = ε (word.get j))
    (hP : ∀ j, P j ⊆ ⋃ b, W b)
    (hsep : ∀ t < (0 : ℝ), ∀ j l,
      Q - t • v 0 ∈ P j → Q - t • v 0 ∈ P l →
      SignType.sign (f j (v 0)) = ε j →
      SignType.sign (f l (v 0)) = ε l → j = l) :
    (DirectSum.decompose ℳ (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) 0 : M) =
      (a : M) := by
  classical
  by_cases ha : (a : M) = 0
  · have ha' : a = 0 := Subtype.ext ha
    simp [ha']
  · rw [decompose_cutoffDecoratedEvaluation_zero_eq_ite hT hP hsep]
    apply ite_eq_left
    refine ⟨CutoffDecoratedRay.ofLeadingRealization word g hT ha hε, ?_⟩
    exact CutoffDecoratedRay.final_eq_zero_ofLeadingRealization ..

end Mei
