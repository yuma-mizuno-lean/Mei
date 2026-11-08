/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Basic
public import Mei.Geometry.Convex.Sweep.Admissible.Deletion
public import Mei.LinearAlgebra.GradedModule.History.Path.Erasure

/-!
# Deleting encounters between varying-chamber propagation blocks

An encounter in a chamber can be deleted when its entire homogeneous output
equals its input and its point misses every retained wall. The preceding and
following blocks may visit independently graded chamber modules. The shortened
ray retains the original incoming tail, every other encounter time, its complete
remaining degree history and its final whole decoration. Equality of spatial
directions alone does not permit deleting a change of degree.

We combine `Quiver.Path.degreesErase` with
`AdmissibleRayRealization.restrictEncounters` on the original path.
The conventions for broken lines are
those of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei.PathDecoratedRay

variable {Q R V J J' K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  {T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c}
  {ℳ : ∀ q, ι q → Submodule R (M q)} [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b z : Q} {i₀ : ι a} {x : ℳ a i₀}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {v : ∀ q, ι q → V}
  {ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ}
  {ε : ∀ {b c : Q}, (b ⟶ c) → SignType}
  {c : ∀ {b c : Q}, (b ⟶ c) → ℝ}
  {P : ∀ {b c : Q}, (b ⟶ c) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {X : V}
  (p : Path a b) (e : b ⟶ b) (q : Path b z)

variable (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C ((p.cons e).comp q) X)
  (hfix : (p.cons e).homogeneousHistory T ℳ (Path.degreesComp (ι := ι) (p.cons e) q r.1.val).1 x =
    p.homogeneousHistory T ℳ (Path.degreesComp (ι := ι) (p.cons e) q r.1.val).1.1 x)
  (W' : J' → Set V) (u : J' → J) (hW : ∀ j, W' j ⊆ W (u j))
  (hoff : ∀ j, r.2.ray (r.2.parameter (Path.loopIndex p e q).succ) ∉ W' j)

include hfix hoff u hW

private def erasureRealization :
    AdmissibleRayRealization ((p.comp q).reverseArrowLabels ν)
      ((p.comp q).reverseArrowLabels c)
      (Path.Degrees.reverseVertexLabels v i₀ (p.comp q)
        (Path.degreesErase p q e r.1.val))
      ((p.comp q).reverseArrowLabels P) W' S C X := by
  have hd := Path.erased_degree_eq_of_decoration_eq p e i₀ T ℳ q r.1.val x hfix
    (by simpa only [decoration_def] using r.decoration_ne_zero)
  have hp := Path.reverseVertexLabels_loopErasureParameter p e v i₀ q r.1.val hd
  have hout := Path.reverseVertexLabels_loopErasure_castSucc p e v i₀ q r.1.val
  have hdir j :
      Path.Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) r.1.val
          (Path.loopErasureParameter p e q j.castSucc) =
        Path.Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) r.1.val
          (Path.loopErasureArrow p e q j).castSucc :=
    (hp j.castSucc).symm.trans (hout j)
  let g := r.2.restrictEncounters (Path.loopErasureArrow p e q)
    (Path.loopErasureParameter p e q) (Path.loopErasureParameter_zero p e q)
    (Path.strictMono_loopErasureParameter p e q)
    (Path.loopErasureParameter_succ p e q) hdir W' u hW (fun j hj => by
      have heq : j = (Path.loopIndex p e q) := by
        rcases Path.eq_loopIndex_or_exists_loopErasureArrow p e q j with h | ⟨k, hk⟩
        · exact h
        · exact (hj ⟨k, hk⟩).elim
      subst j
      refine ⟨?_, hoff⟩
      rw [r.2.bends_parameter,
        Path.reverseVertexLabels_loopIndex_eq p e v i₀ q r.1.val hd, sub_self])
  exact g.congrData
    (funext fun j => (Path.reverseArrowLabels_loopErasure p e ν q j).symm)
    (funext fun j => (Path.reverseArrowLabels_loopErasure p e c q j).symm)
    (funext fun j => (hp j).symm)
    (funext fun j => (Path.reverseArrowLabels_loopErasure p e P q j).symm)

variable {p e q}

/-- Delete an encounter that fixes its whole decoration. The point of deletion
must miss all retained walls, including any coincident support. No propagation
map in either exterior block needs to be invertible or injective. -/
def removeEncounter : PathDecoratedRay T ℳ i₀ x v ν ε c P W' S C (p.comp q) X := by
  have hd := Path.erased_degree_eq_of_decoration_eq p e i₀ T ℳ q r.1.val x hfix
    (by simpa only [decoration_def] using r.decoration_ne_zero)
  refine ⟨⟨Path.degreesErase p q e r.1.val,
    (mem_pathDecoratedHistorySupport ..).mpr ⟨?_, fun j => ?_⟩⟩,
    erasureRealization p e q r hfix W' u hW hoff⟩
  · rw [Path.homogeneousHistory_degreesErase_of_eq p e T ℳ q r.1.val x hfix]
    simpa only [decoration_def] using r.decoration_ne_zero
  · have hn := ((mem_pathDecoratedHistorySupport ..).mp r.1.property).2
      (Path.loopErasureArrow p e q j)
    rw [Path.reverseArrowLabels_loopErasure p e ν q j,
      Path.reverseArrowLabels_loopErasure p e ε q j,
      Path.reverseVertexLabels_loopErasure_castSucc p e v i₀ q r.1.val j,
      Path.reverseVertexLabels_loopErasureParameter p e v i₀ q r.1.val hd j.succ,
      Path.loopErasureParameter_succ p e q j]
    exact hn

/-- The shortened history erases just the selected loop's degree. -/
@[simp]
theorem history_removeEncounter :
    (r.removeEncounter (p := p) (e := e) (q := q) hfix W' u hW hoff).1.val =
      Path.degreesErase p q e r.1.val := (rfl)

/-- Deletion preserves the entire path, including its incoming half-line. -/
@[simp]
theorem ray_removeEncounter :
    (r.removeEncounter (p := p) (e := e) (q := q) hfix W' u hW hoff).2.ray = r.2.ray := by
  simp only [removeEncounter, erasureRealization, AdmissibleRayRealization.ray_congrData,
    AdmissibleRayRealization.ray_restrictEncounters]

/-- Every retained encounter keeps its original parameter; endpoint time stays zero. -/
@[simp]
theorem parameter_removeEncounter (j : Fin ((p.comp q).length + 1)) :
    (r.removeEncounter (p := p) (e := e) (q := q) hfix W' u hW hoff).2.parameter j =
      r.2.parameter (Path.loopErasureParameter p e q j) := by
  simp only [removeEncounter, erasureRealization,
    AdmissibleRayRealization.parameter_congrData,
    AdmissibleRayRealization.parameter_restrictEncounters]

/-- The whole terminal coefficient is unchanged by encounter deletion. -/
@[simp↓]
theorem decoration_removeEncounter :
    (r.removeEncounter (p := p) (e := e) (q := q) hfix W' u hW hoff).decoration = r.decoration := by
  rw [decoration_def, history_removeEncounter, decoration_def]
  exact Path.homogeneousHistory_degreesErase_of_eq p e T ℳ q r.1.val x hfix

omit hfix hoff u hW in
/-- An identity loop fixes the whole intermediate decoration of every surviving
ray. Other arrows in the two exterior blocks remain arbitrary. -/
theorem loop_decoration_eq_of_eq_id (he : T e = LinearMap.id) :
    (p.cons e).homogeneousHistory T ℳ
        (Path.degreesComp (ι := ι) (p.cons e) q r.1.val).1 x =
      p.homogeneousHistory T ℳ
        (Path.degreesComp (ι := ι) (p.cons e) q r.1.val).1.1 x := by
  have hd := Path.last_eq_of_identity_history_ne_zero T ℳ p q e he i₀ r.1.val x.property
    (by simpa only [decoration_def] using r.decoration_ne_zero)
  have hh : (Path.degreesComp (ι := ι) (p.cons e) q r.1.val).1 =
      ((Path.degreesComp (ι := ι) (p.cons e) q r.1.val).1.1,
        Path.Degrees.terminalDegree i₀ p
          (Path.degreesComp (ι := ι) (p.cons e) q r.1.val).1.1) := Prod.ext rfl hd
  rw [hh]
  exact Path.homogeneousHistory_cons_last_of_eq_id T ℳ p e he i₀ _ x.property

/-- Encounter deletion cannot identify distinct complete rays when each omitted
encounter fixes its whole decoration. At a fixed endpoint the shortened history
recovers the original one by repeating the intermediate degree. -/
@[simp]
theorem removeEncounter_inj
    (s : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C ((p.cons e).comp q) X)
    (hs : (p.cons e).homogeneousHistory T ℳ
        (Path.degreesComp (ι := ι) (p.cons e) q s.1.val).1 x =
      p.homogeneousHistory T ℳ
        (Path.degreesComp (ι := ι) (p.cons e) q s.1.val).1.1 x)
    (hsW : ∀ j, s.2.ray (s.2.parameter (Path.loopIndex p e q).succ) ∉ W' j) :
    r.removeEncounter hfix W' u hW hoff = s.removeEncounter hs W' u hW hsW ↔ r = s := by
  constructor
  · intro h
    have hh := congrArg (fun t : PathDecoratedRay T ℳ i₀ x v ν ε c P W' S C (p.comp q) X =>
      t.1.val) h
    simp only [history_removeEncounter] at hh
    apply ext_history
    have hr := Path.degreesRepeat_degreesErase p q e i₀ r.1.val
      (Path.erased_degree_eq_of_decoration_eq p e i₀ T ℳ q r.1.val x hfix
        (by simpa only [decoration_def] using r.decoration_ne_zero))
    have hs' := Path.degreesRepeat_degreesErase p q e i₀ s.1.val
      (Path.erased_degree_eq_of_decoration_eq p e i₀ T ℳ q s.1.val x hs
        (by simpa only [decoration_def] using s.decoration_ne_zero))
    exact hr.symm.trans ((congrArg (Path.degreesRepeat p q e i₀) hh).trans hs')
  · rintro rfl
    rfl

omit hoff in
/-- Deletion with the original path and retained times is possible exactly
when the omitted encounter point misses every retained wall. Thus a coincident
wall cannot be silently dropped from the encounter record. -/
theorem exists_removeEncounter_iff :
    (∃ s : PathDecoratedRay T ℳ i₀ x v ν ε c P W' S C (p.comp q) X,
      s.1.val = Path.degreesErase p q e r.1.val ∧ s.2.ray = r.2.ray ∧
        ∀ j, s.2.parameter j = r.2.parameter (Path.loopErasureParameter p e q j)) ↔
      ∀ j, r.2.ray (r.2.parameter (Path.loopIndex p e q).succ) ∉ W' j := by
  constructor
  · rintro ⟨s, _, hr, ht⟩ j
    have hneg : r.2.parameter (Path.loopIndex p e q).succ < 0 := by
      simpa only [r.2.parameter_zero] using
        r.2.strictAnti_parameter (Fin.succ_pos (Path.loopIndex p e q))
    rw [← hr]
    apply s.2.avoids_walls j _ hneg
    intro k heq
    rw [ht] at heq
    exact Path.loopErasureParameter_ne_loopIndex_succ p e q k.succ
      (r.2.strictAnti_parameter.injective heq.symm)
  · intro h
    exact ⟨r.removeEncounter (p := p) (e := e) (q := q) hfix W' u hW h,
      history_removeEncounter .., ray_removeEncounter ..,
      fun j => parameter_removeEncounter r hfix W' u hW h j⟩

end Mei.PathDecoratedRay
