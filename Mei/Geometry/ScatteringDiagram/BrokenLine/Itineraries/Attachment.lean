/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Extend.Fiber
import Mei.Data.List.OfFn

/-!
# Final-encounter attachment across all cutoff itineraries

Attach a prescribed transverse encounter to every incoming cutoff ray of a chosen
final degree whose selected output component survives. The resulting embedding
retains the entire incoming encounter word. Its exact image tests the outgoing
word's first encounter, the adjacent degrees and admission of its complete older
history at the incoming endpoint. This last test includes source admission and
all wall and singular avoidance conditions.

The weighted image is the selected component of the propagation map applied to
the entire incoming degree component of `cutoffDecoratedEvaluation`. Thus the
identity sums over all encounter words, retaining distinct histories with equal
or cancelling coefficients, and includes killed output components as zero.

We use `DecoratedAdmissibleRay.finalEncounterEmbedding` and its exact-image
criterion, and Mathlib's `Fintype.sum_of_injective`. This is the final-encounter
part of the weighted cut/glue recursion in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ}
  (w : J) (p q : Γ) (Y : V) (s t : ℝ)
  (hs : 0 ≤ s) (ht : 0 < t)
  (hq : q ∈ d.cutoff k) (hqp : q - p ∈ d.monoid)
  (hnormal : f w (v q) = f w (v p)) (htrans : f w (v q) ≠ 0)
  (hsign : SignType.sign (f w (v q)) = ε w)
  (hheight : f w (Y - s • v p) = c w) (hinc : Y - s • v p ∈ P w)
  (hW₁ : ∀ j u, 0 < u → u < s → Y - u • v p ∉ W j)
  (hW₂ : ∀ j u, -t < u → u ≤ 0 → (Y - s • v p - t • v q) - u • v q ∉ W j)
  (hS₁ : ∀ j u, 0 < u → u ≤ s → Y - u • v p ∉ S j)
  (hS₂ : ∀ j u, -t < u → u ≤ 0 → (Y - s • v p - t • v q) - u • v q ∉ S j)

local notation "In" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Y
local notation "Out" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Y - s • v p - t • v q)
local notation "A" => {r : In // CutoffDecoratedRay.finalDegree r = p ∧
  DirectSum.decompose ℳ (T w (CutoffDecoratedRay.decoration r)) q ≠ 0}

private def attach (r : A) : Out := by
  -- Reuse the geometric extension at the incoming ray's actual word.
  let z := DecoratedAdmissibleRay.finalEncounterEmbedding
    (T := fun j => T (r.val.itinerary.get j)) (a := a) (v := v)
    (f := fun j => f (r.val.itinerary.get j)) (c := fun j => c (r.val.itinerary.get j))
    (ε := fun j => ε (r.val.itinerary.get j)) (P := fun j => P (r.val.itinerary.get j))
    (W := W) (S := S) (C := C) (T w) p q Y s t hs ht (f w) (c w) (P w)
    hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂
    ⟨r.val.realization, by
      simpa only [← finalDegree_def, decoration_eq, DecoratedAdmissibleRay.decoration_zero]
        using r.property⟩
  have hz := DecoratedAdmissibleRay.history_finalEncounterEmbedding
    (T := fun j => T (r.val.itinerary.get j)) (a := a) (v := v)
    (f := fun j => f (r.val.itinerary.get j)) (c := fun j => c (r.val.itinerary.get j))
    (ε := fun j => ε (r.val.itinerary.get j)) (P := fun j => P (r.val.itinerary.get j))
    (W := W) (S := S) (C := C) (T w) p q Y s t hs ht (f w) (c w) (P w)
    hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂
    ⟨r.val.realization, by
      simpa only [← finalDegree_def, decoration_eq, DecoratedAdmissibleRay.decoration_zero]
        using r.property⟩
  -- Normalize the tuple-indexed extension to the prepended list, keeping the
  -- degree tuple explicit so that dependent transports do not hide its entries.
  let pp : Fin (r.val.itinerary.length + 1) → Γ := Fin.cons q r.val.realization.1.val
  have hhist : pp ∈ decoratedHistorySupport ℳ (fun j => T ((w :: r.val.itinerary).get j))
      0 a v (fun j => f ((w :: r.val.itinerary).get j))
      (fun j => ε ((w :: r.val.itinerary).get j)) := by
    have hh := z.1.property
    rw [hz] at hh
    simpa only [pp, List.length_cons, List.get_cons_eq_cons, ← Function.comp_def,
      Fin.comp_cons, hsign] using hh
  let zz : DecoratedAdmissibleRay ℳ (fun j => T ((w :: r.val.itinerary).get j)) 0 a v
      (fun j => f ((w :: r.val.itinerary).get j))
      (fun j => c ((w :: r.val.itinerary).get j))
      (fun j => ε ((w :: r.val.itinerary).get j))
      (fun j => P ((w :: r.val.itinerary).get j)) W S C (Y - s • v p - t • v q) := by
    refine ⟨⟨pp, hhist⟩, ?_⟩
    have hh := z.2
    rw [hz] at hh
    simpa only [pp, List.length_cons, List.get_cons_eq_cons, ← Function.comp_def,
      Fin.comp_cons] using hh
  have hh : zz.1.val = Fin.cons q r.val.realization.1.val := rfl
  -- Old cutoff bounds persist, and q - oldDegree is the sum of the new
  -- increment q - p and the existing increment p - oldDegree.
  refine ⟨w :: r.val.itinerary, zz, ?_, ?_⟩
  · intro j
    rw [hh]
    exact Fin.cases hq (fun i => r.val.degree_mem i) j
  · intro i j hij
    rw [hh]
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp
      | succ j =>
        have hpj : p - r.val.realization.1.val j ∈ d.monoid := by
          let z₀ : Fin r.val.itinerary.length := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
          have hf : r.val.finalDegree = r.val.realization.1.val z₀ := by
            have hi : z₀.castSucc = (0 : Fin (r.val.itinerary.length + 1)) := Fin.ext rfl
            rw [finalDegree_def, ← hi, Fin.snoc_castSucc]
          have hpj := r.val.degree_sub_mem z₀ j (by simp [z₀, Fin.le_def])
          simpa only [← hf, r.property.1] using hpj
        simpa only [Fin.cons_zero, Fin.cons_succ, sub_add_sub_cancel] using
          d.monoid.add_mem hqp hpj
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Nat.not_succ_le_zero _ hij).elim
      | succ j => exact r.val.degree_sub_mem i j (Fin.succ_le_succ_iff.mp hij)

/-- Attach one encounter to the full incoming cutoff fiber. The new final
degree survives the cutoff and its increment belongs to the positive monoid;
every older degree and encounter is retained. Only surviving components create rays. -/
def finalEncounterEmbedding : A ↪ Out where
  toFun := attach w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc hW₁ hW₂ hS₁ hS₂
  inj' := by
    intro r r' he
    have hl : r.val.itinerary = r'.val.itinerary :=
      (List.cons.inj (congrArg itinerary he)).2
    apply Subtype.ext
    apply CutoffDecoratedRay.ext hl
    rcases r with ⟨⟨l, z, hm, hmono⟩, hr⟩
    rcases r' with ⟨⟨l', z', hm', hmono'⟩, hr'⟩
    dsimp only at hl
    subst l'
    apply heq_of_eq
    apply Sigma.fst_injective
    apply Subtype.ext
    have hh := congrArg (fun b : Out =>
      (⟨b.itinerary.length, b.realization.1.val⟩ : Σ n, Fin n → Γ)) he
    have hh' := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    exact funext fun i => by simpa only [attach, Fin.cons_succ] using congrFun hh' i.succ

private theorem finalEncounterEmbedding_apply (r : A) :
    finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc
      hW₁ hW₂ hS₁ hS₂ r =
      attach w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc hW₁ hW₂ hS₁ hS₂ r := rfl

/-- Attachment prepends the encounter and preserves the entire older word. -/
@[simp]
theorem itinerary_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).itinerary = w :: r.val.itinerary := (rfl)

/-- The complete degree-labelled itinerary retains every earlier degree and
encounter, including coefficient changes with unchanged spatial velocity. -/
@[simp]
theorem degreeItinerary_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).degreeItinerary = (q, w) :: r.val.degreeItinerary := by
  rw [finalEncounterEmbedding_apply]
  simp only [degreeItinerary_eq]
  rw [← List.ofFn_cons]
  congr 1
  funext j
  cases j using Fin.cases <;> rfl

/-- The output ray has the selected final degree. -/
@[simp]
theorem finalDegree_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).finalDegree = q := by
  rw [finalEncounterEmbedding_apply, finalDegree_def]
  rfl

/-- Attachment retains the complete incoming path by the canonical finite-ray
extension, including all old bend increments and the incoming tail. -/
@[simp]
theorem ray_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).realization.2.ray =
      r.val.realization.2.ray.extend s t (v q) hs ht := by
  rw [← DecoratedAdmissibleRay.ray_finalEncounterEmbedding
    (T w) p q Y s t hs ht (f w) (c w) (P w) hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂
    ⟨r.val.realization, by
      simpa only [← finalDegree_def, decoration_eq, DecoratedAdmissibleRay.decoration_zero]
        using r.property⟩]
  rw [finalEncounterEmbedding_apply]
  simp only [attach, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast]
  -- The list and history transports change only the realization's indices.
  congr 1 <;> simp only [List.get_cons_eq_cons, ← Function.comp_def, Fin.comp_cons,
    DecoratedAdmissibleRay.history_finalEncounterEmbedding, cast_heq]

/-- The endpoint parameter remains zero, the new encounter occurs at `-t`,
and all earlier encounter times are translated by `s + t`. -/
@[simp↓] -- Rewrite the packaged parameters before `List.ofFn_succ` expands them.
theorem parameter_finalEncounterEmbedding (r : A) :
    List.ofFn (finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign
      hheight hinc hW₁ hW₂ hS₁ hS₂ r).realization.2.parameter =
      0 :: -t :: List.ofFn (fun j => r.val.realization.2.parameter j.succ - (s + t)) := by
  rw [← List.ofFn_cons, ← List.ofFn_cons,
    ← DecoratedAdmissibleRay.parameter_finalEncounterEmbedding
      (T w) p q Y s t hs ht (f w) (c w) (P w) hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂
      ⟨r.val.realization, by
        simpa only [← finalDegree_def, decoration_eq, DecoratedAdmissibleRay.decoration_zero]
          using r.property⟩]
  rw [finalEncounterEmbedding_apply]
  simp only [attach, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast]
  apply congrArg List.ofFn
  -- As for the ray, the index transports preserve the underlying parameter data.
  funext i
  congr 1 <;> simp only [List.get_cons_eq_cons, ← Function.comp_def, Fin.comp_cons,
    DecoratedAdmissibleRay.history_finalEncounterEmbedding, cast_heq]

/-- The attached final weight is the whole degree-`q` component after applying
the wall action `T w` to the incoming weight, without splitting it into monomials. -/
@[simp↓]
theorem decoration_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).decoration =
      (DirectSum.decompose ℳ (T w r.val.decoration) q : M) := by
  rw [finalEncounterEmbedding_apply, decoration_eq, r.val.decoration_eq]
  -- Reduce the new embedding's structural projections before rewriting the
  -- list-indexed propagation tuple; `simp` does not project an embedding coercion.
  change homogeneousHistory ℳ (fun j => T ((w :: r.val.itinerary).get j))
    (Fin.cons q r.val.realization.1.val) a = _
  simp only [List.length_cons, List.get_cons_eq_cons, ← Function.comp_def, Fin.comp_cons,
    homogeneousHistory_succ_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- The image consists exactly of rays whose final encounter and adjacent degrees
are the prescribed ones and whose complete older history admits `Y`. The latter
condition retains source admission and avoidance of all obstacles. -/
@[simp↓]
theorem mem_range_finalEncounterEmbedding (z : Out) :
    z ∈ Set.range (finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign
      hheight hinc hW₁ hW₂ hS₁ hS₂) ↔
      match z with
      | ⟨[], _, _, _⟩ => False
      | ⟨j :: l, z, _, _⟩ =>
        j = w ∧ z.1.val 0 = q ∧
        Fin.snoc (α := fun _ => Γ) (fun i : Fin l.length => z.1.val i.succ) 0 0 = p ∧
        Y ∈ admissibleBackwardDomain (fun i => f (l.get i)) (fun i => c (l.get i))
          (fun i => v (Fin.snoc (α := fun _ => Γ)
            (fun j : Fin l.length => z.1.val j.succ) 0 i))
          (fun i => P (l.get i)) W S C := by
  constructor
  · rintro ⟨r, rfl⟩
    rw [finalEncounterEmbedding_apply]
    dsimp only [attach]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨trivial, trivial, by simpa only [← finalDegree_def] using r.property.1,
      r.val.realization.2.mem_admissibleBackwardDomain⟩
  · rcases z with ⟨l, z, hm, hmono⟩
    cases l with
    | nil => exact False.elim
    | cons j l =>
      rintro ⟨hj, hzq, hzp, hY⟩
      subst j
      -- Recognize the existing fixed-word attachment image, then lift its
      -- incoming ray with the cutoff and positivity proofs inherited from z.
      let zz : DecoratedAdmissibleRay ℳ (Fin.cons (T w) (fun i => T (l.get i))) 0 a v
          (Fin.cons (f w) (fun i => f (l.get i)))
          (Fin.cons (c w) (fun i => c (l.get i)))
          (Fin.cons (SignType.sign (f w (v q))) (fun i => ε (l.get i)))
          (Fin.cons (P w) (fun i => P (l.get i))) W S C (Y - s • v p - t • v q) := by
        refine ⟨⟨z.1.val, ?_⟩, ?_⟩
        · simpa only [List.length_cons, List.get_cons_eq_cons, ← Function.comp_def,
            Fin.comp_cons, hsign] using z.1.property
        · simpa only [List.length_cons, List.get_cons_eq_cons, ← Function.comp_def,
            Fin.comp_cons] using z.2
      obtain ⟨r, hr⟩ := (DecoratedAdmissibleRay.mem_range_finalEncounterEmbedding
        (T w) p q Y s t hs ht (f w) (c w) (P w) hnormal htrans hheight hinc
        hW₁ hW₂ hS₁ hS₂ zz).mpr ⟨hzq, hzp, hY⟩
      have hh := congrArg (fun b => b.1.val) hr
      rw [DecoratedAdmissibleRay.history_finalEncounterEmbedding] at hh
      have hold (i : Fin l.length) : r.val.1.val i = z.1.val i.succ := by
        simpa only [Fin.cons_succ] using congrFun hh i.succ
      let rr : In := ⟨l, r.val,
        (fun i => hold i ▸ hm i.succ),
        (fun i j hij => by
          rw [hold i, hold j]
          exact hmono i.succ j.succ (Fin.succ_le_succ_iff.mpr hij))⟩
      have hrr : rr.finalDegree = p ∧ DirectSum.decompose ℳ (T w rr.decoration) q ≠ 0 := by
        simpa only [rr, finalDegree_def, decoration_eq, DecoratedAdmissibleRay.decoration_zero]
          using r.property
      refine ⟨⟨rr, hrr⟩, ?_⟩
      refine CutoffDecoratedRay.ext ?_ ?_
      · rfl
      apply heq_of_eq
      apply Sigma.fst_injective
      exact Subtype.ext hh

include hs ht hq hqp hnormal htrans hsign hheight hinc hW₁ hW₂ hS₁ hS₂

open Classical in
/-- The weighted image across every encounter word is the selected component
of the wall action on the full incoming degree-`p` evaluation. Killed output
components contribute zero; histories with coincident or cancelling weights
remain distinct. The preceding image criterion gives the geometric selection. -/
theorem sum_ite_decoration_finalEncounter_eq_component [Finite J] :
    (let := Fintype.ofFinite Out
     ∑ z : Out, if z ∈ Set.range (finalEncounterEmbedding w p q Y s t hs ht hq hqp
       hnormal htrans hsign hheight hinc hW₁ hW₂ hS₁ hS₂) then z.decoration else 0) =
      (DirectSum.decompose ℳ (T w
        (DirectSum.decompose ℳ
          (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Y) p)) q : M) := by
  classical
  let := Fintype.ofFinite In
  let := Fintype.ofFinite Out
  let := Fintype.ofFinite A
  let B := {r : In // r.finalDegree = p}
  let := Fintype.ofFinite B
  let e : A ↪ Out := finalEncounterEmbedding w p q Y s t hs ht hq hqp hnormal htrans hsign
    hheight hinc hW₁ hW₂ hS₁ hS₂
  trans ∑ r : A, (DirectSum.decompose ℳ (T w r.val.decoration) q : M)
  · symm
    apply Fintype.sum_of_injective e e.injective
    · intro z hz
      exact ite_eq_right hz
    · intro r
      rw [ite_eq_left (show e r ∈ Set.range e from ⟨r, rfl⟩)]
      exact (decoration_finalEncounterEmbedding ..).symm
  trans ∑ r : B, (DirectSum.decompose ℳ (T w r.val.decoration) q : M)
  · let inc : A → B := fun r => ⟨r.val, r.property.1⟩
    apply Fintype.sum_of_injective inc
      (fun r r' h => Subtype.ext (congrArg (fun b : B => b.val) h))
    · intro r hr
      have hc : DirectSum.decompose ℳ (T w r.val.decoration) q = 0 := by
        by_contra hc
        exact hr ⟨⟨r.val, r.property, hc⟩, rfl⟩
      rw [hc, Submodule.coe_zero]
    · intro r
      rfl
  · rw [decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree]
    simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    rfl

end Mei.CutoffDecoratedRay
