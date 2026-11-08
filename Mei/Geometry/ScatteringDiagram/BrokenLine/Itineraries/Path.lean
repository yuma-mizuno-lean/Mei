/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay.Path
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family

/-!
# Cutoff decorated rays as rays along quiver paths

Encounter words over an alphabet `J` are the paths of the one-object quiver on `J`
(`Quiver.SingleObj.listToPath`). Suppose that at an endpoint every actual decorated ray
of every word already satisfies the two cutoff conditions: its selected relative degrees
lie in the cutoff and decrease in the positive monoid when read backwards. This holds,
for instance, when the homogeneous pieces outside the cutoff vanish and nonzero transfer
components raise relative degree in the positive monoid. Then the cutoff decorated rays
at that endpoint are exactly the actual decorated rays along all paths of the quiver,
with the same chamber module throughout.

Consequently the cutoff weighted evaluation is the common weighted evaluation
`pathDecoratedEvaluation` over any finite inventory of paths containing every path that
carries a ray at the endpoint. The comparison retains the encounter word, the complete
degree history, the geometric ray with its incoming tail, and the whole final decoration.

This identifies the cutoff carrier with the common varying-chamber construction on a
one-object quiver. It uses `decoratedAdmissibleRayPathEquiv` for each word and Mathlib's
`Quiver.SingleObj.pathEquivList`.
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (a : ℳ 0) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)

local notation "WordRay" l:max Q:max => DecoratedAdmissibleRay ℳ (fun j => T (List.get l j)) 0 a v
  (fun j => f (List.get l j)) (fun j => c (List.get l j)) (fun j => ε (List.get l j))
  (fun j => P (List.get l j)) W S C Q
local notation "PRay" p:max Q:max => PathDecoratedRay (Q := SingleObj J) (M := fun _ => M)
  (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
  (fun e => ε e) (fun e => c e) (fun e => P e) W S C p Q

/-- The path of the lookup function of a word is the path of the word. -/
theorem _root_.Quiver.SingleObj.pathOfFn_get {α : Type*} :
    ∀ l : List α, SingleObj.pathOfFn l.get = SingleObj.listToPath l
  | [] => rfl
  | x :: l => by
    rw [SingleObj.pathOfFn_succ, SingleObj.listToPath]
    exact congrArg (fun p => Path.cons p x) (Quiver.SingleObj.pathOfFn_get l)

/-- The actual decorated rays of all words are the actual decorated rays along all paths
of the one-object quiver on the alphabet. -/
def wordDecoratedRayPathEquiv (Q : V) :
    (Σ l : List J, WordRay l Q) ≃ (Σ p : Path (SingleObj.star J) (SingleObj.star J), PRay p Q) :=
  Equiv.sigmaCongr SingleObj.pathEquivList.symm fun l =>
    (decoratedAdmissibleRayPathEquiv ℳ T 0 a v f c ε P W S C l.get Q).trans
      (Equiv.cast (congrArg (fun p => PRay p Q) (SingleObj.pathOfFn_get l)))

/-- The path comparison of words sends a word to its path. -/
@[simp]
theorem wordDecoratedRayPathEquiv_fst (Q : V) (z : Σ l : List J, WordRay l Q) :
    (wordDecoratedRayPathEquiv ℳ T a v f c ε P W S C Q z).1 = SingleObj.listToPath z.1 :=
  (rfl)

/-- The path comparison of words preserves the whole final decoration. -/
theorem wordDecoratedRayPathEquiv_decoration (Q : V) (z : Σ l : List J, WordRay l Q) :
    (wordDecoratedRayPathEquiv ℳ T a v f c ε P W S C Q z).2.decoration = z.2.decoration 0 := by
  obtain ⟨l, r⟩ := z
  have key : ∀ {p : Path (SingleObj.star J) (SingleObj.star J)}
      (h : SingleObj.pathOfFn l.get = p) (s : PRay (SingleObj.pathOfFn l.get) Q),
      (Equiv.cast (congrArg (fun p => PRay p Q) h) s).decoration = s.decoration := by
    intro p h s
    subst h
    rfl
  exact (key (SingleObj.pathOfFn_get l) _).trans
    (decoratedAdmissibleRayPathEquiv_decoration ℳ T 0 a v f c ε P W S C l.get Q r)

variable {k : ℕ}

/-- If the nonzero homogeneous pieces lie in the cutoff and every nonzero transfer
component raises degree in the positive monoid, every actual ray of every word satisfies
both cutoff conditions. -/
theorem DecoratedAdmissibleRay.cutoff_conditions_of_sub_mem
    (hcutoff : ∀ {q : Γ} {x : M}, x ∈ ℳ q → x ≠ 0 → q ∈ d.cutoff k)
    (hshift : ∀ (e : J) (i j : Γ) (x : M), x ∈ ℳ i →
      DirectSum.decompose ℳ (T e x) j ≠ 0 → j - i ∈ d.monoid)
    {Q : V} (l : List J) (r : WordRay l Q) :
    (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid := by
  refine ⟨fun j => hcutoff (r.decoration_mem j) (r.decoration_ne_zero j.castSucc),
    fun i j hij => ?_⟩
  have hne := ((mem_decoratedHistorySupport ..).mp r.1.property).1
  simpa only [Fin.snoc_castSucc] using homogeneousHistory_snoc_sub_mem_of_le d.monoid _
    (fun j' => hshift (l.get j')) r.1.val 0 a hne i.castSucc j.castSucc
    (Fin.castSucc_le_castSucc_iff.mpr hij)

/-- When every actual ray of every word satisfies the cutoff conditions at the endpoint,
the cutoff rays there are the actual rays of all words. -/
def cutoffDecoratedRayWordEquiv {Q : V}
    (hcut : ∀ (l : List J) (r : WordRay l Q),
      (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid) :
    CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q ≃ Σ l : List J, WordRay l Q where
  toFun r := ⟨r.itinerary, r.realization⟩
  invFun z := ⟨z.1, z.2, (hcut z.1 z.2).1, (hcut z.1 z.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A cutoff ray is sent to its encounter word and realization. -/
@[simp]
theorem cutoffDecoratedRayWordEquiv_apply {Q : V}
    (hcut : ∀ (l : List J) (r : WordRay l Q),
      (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    cutoffDecoratedRayWordEquiv d ℳ T a v f c ε P W S C hcut r = ⟨r.itinerary, r.realization⟩ :=
  (rfl)

/-- The inverse retains the encounter word. -/
@[simp]
theorem cutoffDecoratedRayWordEquiv_symm_itinerary {Q : V}
    (hcut : ∀ (l : List J) (r : WordRay l Q),
      (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
    (z : Σ l : List J, WordRay l Q) :
    ((cutoffDecoratedRayWordEquiv d ℳ T a v f c ε P W S C hcut).symm z).itinerary = z.1 :=
  (rfl)

/-- The inverse retains the degree-labelled encounter word. -/
@[simp]
theorem cutoffDecoratedRayWordEquiv_symm_degreeItinerary {Q : V}
    (hcut : ∀ (l : List J) (r : WordRay l Q),
      (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
    (z : Σ l : List J, WordRay l Q) :
    ((cutoffDecoratedRayWordEquiv d ℳ T a v f c ε P W S C hcut).symm z).degreeItinerary =
      List.ofFn fun j => (z.2.1.val j, z.1.get j) :=
  CutoffDecoratedRay.degreeItinerary_eq _

/-- The inverse retains the whole final decoration. -/
theorem cutoffDecoratedRayWordEquiv_symm_decoration {Q : V}
    (hcut : ∀ (l : List J) (r : WordRay l Q),
      (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
    (z : Σ l : List J, WordRay l Q) :
    ((cutoffDecoratedRayWordEquiv d ℳ T a v f c ε P W S C hcut).symm z).decoration =
      z.2.decoration 0 :=
  (CutoffDecoratedRay.decoration_eq _).trans (DecoratedAdmissibleRay.decoration_zero _).symm

variable [Finite J]

/-- When every actual ray of every word satisfies the cutoff conditions at the endpoint,
the cutoff weighted evaluation is the common weighted evaluation over any finite path
inventory containing every path that carries a ray there. -/
theorem cutoffDecoratedEvaluation_eq_pathDecoratedEvaluation {Q : V}
    (hcut : ∀ (l : List J) (r : WordRay l Q),
      (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
    (s : Finset (Path (SingleObj.star J) (SingleObj.star J)))
    (hs : ∀ p, PRay p Q → p ∈ s) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
      pathDecoratedEvaluation (Q := SingleObj J) (M := fun _ => M) (ι := fun _ => Γ)
        (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v) (fun e => f e) (fun e => ε e)
        (fun e => c e) (fun e => P e) W S C Q := by
  let e := ((cutoffDecoratedRayWordEquiv d ℳ T a v f c ε P W S C hcut).trans
    (wordDecoratedRayPathEquiv ℳ T a v f c ε P W S C Q)).trans
    (Equiv.sigmaSubtypeEquivOfSubset (fun p => PRay p Q) (fun p => p ∈ s) hs).symm
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  let := Fintype.ofFinite (Σ p : (s : Type _), PRay p.val Q)
  rw [cutoffDecoratedEvaluation_def, pathDecoratedEvaluation_def]
  refine Fintype.sum_equiv e _ _ fun r => ?_
  have h := wordDecoratedRayPathEquiv_decoration ℳ T a v f c ε P W S C Q
    ⟨r.itinerary, r.realization⟩
  rw [CutoffDecoratedRay.decoration_eq, ← DecoratedAdmissibleRay.decoration_zero]
  exact h.symm

/-- If the nonzero homogeneous pieces lie in the cutoff and nonzero transfer components
raise degree in the positive monoid, the cutoff weighted evaluation is the common
weighted evaluation over any finite path inventory exhausting the endpoint fiber. -/
theorem cutoffDecoratedEvaluation_eq_pathDecoratedEvaluation_of_sub_mem {Q : V}
    (hcutoff : ∀ {q : Γ} {x : M}, x ∈ ℳ q → x ≠ 0 → q ∈ d.cutoff k)
    (hshift : ∀ (e : J) (i j : Γ) (x : M), x ∈ ℳ i →
      DirectSum.decompose ℳ (T e x) j ≠ 0 → j - i ∈ d.monoid)
    (s : Finset (Path (SingleObj.star J) (SingleObj.star J)))
    (hs : ∀ p, PRay p Q → p ∈ s) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
      pathDecoratedEvaluation (Q := SingleObj J) (M := fun _ => M) (ι := fun _ => Γ)
        (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v) (fun e => f e) (fun e => ε e)
        (fun e => c e) (fun e => P e) W S C Q :=
  cutoffDecoratedEvaluation_eq_pathDecoratedEvaluation d ℳ T a v f c ε P W S C
    (fun l r => DecoratedAdmissibleRay.cutoff_conditions_of_sub_mem d ℳ T a v f c ε P W S C
      hcutoff hshift l r) s hs

end Mei
