/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Attachment
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cutoff
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut.Incoming
public import Mei.Geometry.Affine.Segment
import Mei.Data.List.OfFn

/-!
# Complete final-encounter sums across cutoff itineraries

At a prescribed transverse final encounter, sum every outgoing cutoff ray with
that encounter and the prescribed adjacent degrees. For every sufficiently
small incoming displacement, this equals the selected component of propagation
of the whole incoming degree fiber. There is no residual incoming-admission
test and no fixed older encounter word. The incoming enumeration cutoff can be
any cutoff retaining its degree, so a strict degree change permits induction.

Source admission, wall and singular avoidance, whole decorations and distinct
histories remain in both fibers. Equal spatial velocities do not erase a
coefficient-degree change. Neither consistency nor preservation of diagonal
components is required.

We combine `CutoffDecoratedRay.sum_ite_decoration_finalEncounter_eq_component`
with `DecoratedAdmissibleRay.eventually_forall_mem_admissibleBackwardDomain_cons`,
using finiteness of the full outgoing cutoff inventory to choose a common cut.
The local incoming-segment argument is shared with
`DecoratedAdmissibleRay.eventually_sum_finalEncounter_eq_component_sum`.
This is the changing-encounter part of the backward-ray recursion in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

private theorem eventually_admits_older_words [Finite J]
    (w : J) (p q : Γ) (hsign : SignType.sign (f w (v q)) = ε w) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∀ z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
        match z with
        | ⟨[], _, _, _⟩ => True
        | ⟨j :: l, z, _, _⟩ => j = w → z.1.val 0 = q →
          Fin.snoc (α := fun _ => Γ) (fun i : Fin l.length => z.1.val i.succ) 0 0 = p →
          Q + ((c w - f w Q) / f w (v q)) • v q + η • v p ∈
            admissibleBackwardDomain (fun i => f (l.get i)) (fun i => c (l.get i))
              (fun i => v (Fin.snoc (α := fun _ => Γ)
                (fun j : Fin l.length => z.1.val j.succ) 0 i))
              (fun i => P (l.get i)) W S C := by
  apply eventually_all.mpr
  rintro ⟨l, z, _, _⟩
  cases l with
  | nil => exact Eventually.of_forall fun _ => trivial
  | cons j l =>
    by_cases hj : j = w
    · subst j
      have hh := DecoratedAdmissibleRay.eventually_forall_mem_admissibleBackwardDomain_cons
        (T := fun i => T (l.get i)) (a := a) (v := v)
        (f := fun i => f (l.get i)) (c := fun i => c (l.get i))
        (ε := fun i => ε (l.get i)) (P := fun i => P (l.get i))
        (W := W) (S := S) (C := C) (T w) p q Q (f w) (c w) (P w)
      filter_upwards [hh] with η hη _ hq hp
      -- The list's head/tail tuple is exactly the supplier's `Fin.cons` tuple;
      -- replace its sign using the prescribed outgoing crossing sign.
      let zz : DecoratedAdmissibleRay ℳ (Fin.cons (T w) (fun i => T (l.get i))) 0 a v
          (Fin.cons (f w) (fun i => f (l.get i)))
          (Fin.cons (c w) (fun i => c (l.get i)))
          (Fin.cons (SignType.sign (f w (v q))) (fun i => ε (l.get i)))
          (Fin.cons (P w) (fun i => P (l.get i))) W S C Q := by
        refine ⟨⟨z.1.val, ?_⟩, ?_⟩
        · simpa only [List.length_cons, List.get_cons_eq_cons, ← Function.comp_def,
            Fin.comp_cons, hsign] using z.1.property
        · simpa only [List.length_cons, List.get_cons_eq_cons, ← Function.comp_def,
            Fin.comp_cons] using z.2
      exact hη zz hq hp
    · exact Eventually.of_forall fun _ he => (hj he).elim

/-- The cutoff ray `z` has final encounter `w`, final degree `q` and incoming
degree `p` at that encounter. Its older encounter word is unrestricted. -/
def HasFinalEncounter (z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (w : J) (p q : Γ) : Prop :=
  match z with
  | ⟨[], _, _, _⟩ => False
  | ⟨j :: l, z, _, _⟩ => j = w ∧ z.1.val 0 = q ∧
    Fin.snoc (α := fun _ => Γ) (fun i : Fin l.length => z.1.val i.succ) 0 0 = p

open Classical in
/-- Sum the complete final-encounter fiber over all older words at every
sufficiently short incoming cut. The incoming degree component may be evaluated
at any enumeration cutoff `l` retaining `p`; in particular, a degree-raising
encounter allows a strictly lower cutoff. Killed components contribute zero,
while distinct histories with equal or cancelling weights remain distinct.
Obstacle supports need not be closed: only their closures incident to the crossing
must lie in its supporting hyperplane. -/
theorem eventually_sum_finalEncounter_eq_component [Finite J] [Finite K]
    (w : J) (p q : Γ) (l : ℕ) (hp : d.degree p ≤ l)
    (hq : q ∈ d.cutoff k) (hqp : q - p ∈ d.monoid)
    (t : ℝ) (ht : 0 < t)
    (hnormal : f w (v q) = f w (v p)) (htrans : f w (v q) ≠ 0)
    (hsign : SignType.sign (f w (v q)) = ε w)
    (hheight : f w (Q + t • v q) = c w) (hinc : Q + t • v q ∈ P w)
    (hplane : ∀ j, Q + t • v q ∈ closure (W j) →
      ∀ y ∈ closure (W j), f w y = c w)
    (hclosedS : ∀ j, IsClosed (S j)) (hregular : ∀ j, Q + t • v q ∉ S j)
    (hW : ∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ W j)
    (hS : ∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ S j) :
    let Out := CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
    let := Fintype.ofFinite Out
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      (∑ z : Out, if z.HasFinalEncounter w p q then z.decoration else 0) =
      (DirectSum.decompose ℳ (T w (DirectSum.decompose ℳ
        (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C l
          (Q + t • v q + η • v p)) p)) q : M) := by
  classical
  dsimp only
  let x := Q + t • v q
  have htime : (c w - f w Q) / f w (v q) = t := by
    apply (div_eq_iff htrans).mpr
    rw [map_add, map_smul, smul_eq_mul] at hheight
    linarith
  have hcut := eventually_admits_older_words (d := d) (ℳ := ℳ) (T := T) (a := a)
    (v := v) (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S) (C := C)
    (k := k) (Q := Q) w p q hsign
  rw [htime] at hcut
  have hnear := eventually_incomingSegment_notMem
    (W := fun j => closure (W j)) x (v p) (f w).toLinearMap (c w)
    (hnormal ▸ htrans) hheight (fun _ => isClosed_closure) hplane hclosedS hregular
  filter_upwards [hcut, hnear, self_mem_nhdsWithin] with η hcut hnear hη
  have hη : 0 < η := hη
  let Y := x + η • v p
  have hend : Y - η • v p - t • v q = Q := by simp [Y, x]
  -- The exact attachment image already accounts for every surviving incoming
  -- component. Uniform cuts now remove its admission test across all words.
  have hh := sum_ite_decoration_finalEncounter_eq_component
    (d := d) (ℳ := ℳ) (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε)
    (P := P) (W := W) (S := S) (C := C) w p q Y η t hη.le ht hq hqp
    hnormal htrans hsign (by simpa [Y, x] using hheight) (by simpa [Y] using hinc)
    (fun j u hu huη hmem => hnear.1 j u hu huη (subset_closure hmem))
    (by simpa only [hend] using hW) hnear.2 (by simpa only [hend] using hS)
  simp only [mem_range_finalEncounterEmbedding] at hh
  -- Give the selection an independent endpoint argument. The matcher in the
  -- image theorem otherwise ties its ambient ray type to `Y - η • v p - t • v q`,
  -- preventing dependent transport of the sum to the actual endpoint Q.
  let admitted (Z : V) (z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Z) : Prop :=
    match z with
    | ⟨[], _, _, _⟩ => False
    | ⟨j :: word, z, _, _⟩ => j = w ∧ z.1.val 0 = q ∧
      Fin.snoc (α := fun _ => Γ) (fun i : Fin word.length => z.1.val i.succ) 0 0 = p ∧
      Y ∈ admissibleBackwardDomain (fun i => f (word.get i)) (fun i => c (word.get i))
        (fun i => v (Fin.snoc (α := fun _ => Γ)
          (fun j : Fin word.length => z.1.val j.succ) 0 i))
        (fun i => P (word.get i)) W S C
  have hsum :
      (let := Fintype.ofFinite
        (CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Y - η • v p - t • v q))
       ∑ z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Y - η • v p - t • v q),
         if admitted _ z then z.decoration else 0) =
      (DirectSum.decompose ℳ (T w (DirectSum.decompose ℳ
        (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Y) p)) q : M) := by
    refine Eq.trans ?_ hh
    apply Finset.sum_congr rfl
    rintro ⟨word, z, hm, hmono⟩ _
    cases word <;> rfl
  rw [hend] at hsum
  have hpk : d.degree p ≤ k := by
    have hn := d.degree_nonneg hqp
    rw [map_sub] at hn
    exact (sub_nonneg.mp hn).trans (d.mem_cutoff.mp hq).2
  rw [decompose_cutoffDecoratedEvaluation_eq_of_degree_le p hpk hp] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  rintro ⟨word, z, hm, hmono⟩ _
  dsimp only [admitted]
  cases word with
  | nil => simp [HasFinalEncounter]
  | cons j word =>
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact (h₂ ⟨h₁.1, h₁.2.1, h₁.2.2, hcut ⟨j :: word, z, hm, hmono⟩ h₁.1 h₁.2.1 h₁.2.2⟩).elim
    · exact (h₁ ⟨h₂.1, h₂.2.1, h₂.2.2.1⟩).elim
    · rfl

end Mei.CutoffDecoratedRay
