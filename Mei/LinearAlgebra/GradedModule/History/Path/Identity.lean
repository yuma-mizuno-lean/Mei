/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Path

/-!
# Identity insertion in paths of graded modules

Insert an identity arrow between two propagation blocks through possibly different
chamber modules. On a homogeneous input, every surviving history repeats the
incoming degree at the inserted arrow. Deleting that repetition gives a bijection
of the finite contributing histories, preserving whole final decorations and any
selection on the retained history. The prefix may be empty: in that case the
inserted degree is the original homogeneous input degree. Zero inputs are allowed.

These are coefficient subdivision laws; they do not assert that a geometric path
can omit a wall encounter. We use the shared path-history concatenation theorem
and homogeneous projections, without finiteness of the degree types or modules.
-/

public noncomputable section

namespace Quiver.Path

variable {Q : Type*} [Quiver Q] {ι : Q → Type*} {a b c : Q}

/-- Insert one arrow between two blocks, repeating its incoming degree. -/
def degreesRepeat (p : Path a b) (q : Path b c) (e : b ⟶ b) (i : ι a)
    (d : (p.comp q).Degrees ι) : ((p.cons e).comp q).Degrees ι :=
  (degreesComp (ι := ι) (p.cons e) q).symm
    (((degreesComp (ι := ι) p q d).1, Degrees.terminalDegree i p (degreesComp (ι := ι) p q d).1),
      (degreesComp (ι := ι) p q d).2)

/-- Erase the selected degree at the arrow between two blocks. -/
def degreesErase (p : Path a b) (q : Path b c) (e : b ⟶ b)
    (d : ((p.cons e).comp q).Degrees ι) : (p.comp q).Degrees ι :=
  (degreesComp (ι := ι) p q).symm
    ((degreesComp (ι := ι) (p.cons e) q d).1.1, (degreesComp (ι := ι) (p.cons e) q d).2)

/-- The inserted history repeats precisely the terminal degree of the prefix. -/
-- Use this dependent splitting formula with `rw`; simp cannot infer its degree family.
theorem degreesComp_degreesRepeat (p : Path a b) (q : Path b c) (e : b ⟶ b)
    (i : ι a) (d : (p.comp q).Degrees ι) :
    degreesComp (ι := ι) (p.cons e) q (degreesRepeat p q e i d) =
      (((degreesComp (ι := ι) p q d).1, Degrees.terminalDegree i p (degreesComp (ι := ι) p q d).1),
        (degreesComp (ι := ι) p q d).2) := by
  simp [degreesRepeat]

/-- Splitting an erased history drops only the inserted degree. -/
@[simp]
theorem degreesComp_degreesErase (p : Path a b) (q : Path b c) (e : b ⟶ b)
    (d : ((p.cons e).comp q).Degrees ι) :
    degreesComp (ι := ι) p q (degreesErase p q e d) =
      ((degreesComp (ι := ι) (p.cons e) q d).1.1, (degreesComp (ι := ι) (p.cons e) q d).2) := by
  simp [degreesErase]

@[simp]
theorem degreesErase_degreesRepeat (p : Path a b) (q : Path b c) (e : b ⟶ b)
    (i : ι a) (d : (p.comp q).Degrees ι) :
    degreesErase p q e (degreesRepeat p q e i d) = d := by
  apply (degreesComp (ι := ι) p q).injective
  simp [degreesErase, degreesRepeat]

/-- Repeating after erasing recovers a history if its inserted degree
agrees with the incoming degree. -/
theorem degreesRepeat_degreesErase (p : Path a b) (q : Path b c) (e : b ⟶ b)
    (i : ι a) (d : ((p.cons e).comp q).Degrees ι)
    (hd : (degreesComp (ι := ι) (p.cons e) q d).1.2 =
      Degrees.terminalDegree i p (degreesComp (ι := ι) (p.cons e) q d).1.1) :
    degreesRepeat p q e i (degreesErase p q e d) = d := by
  apply (degreesComp (ι := ι) (p.cons e) q).injective
  rw [degreesComp_degreesRepeat, degreesComp_degreesErase]
  exact Prod.ext (Prod.ext rfl hd.symm) rfl

variable {R : Type*} [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {u v : Q}, (u ⟶ v) → M u →ₗ[R] M v)
  [∀ q, DecidableEq (ι q)]
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]

/-- At the end of a block, an identity arrow retains exactly its incoming
homogeneous decoration. The block can be empty. -/
@[simp]
theorem homogeneousHistory_cons_last_of_eq_id (p : Path a b)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a)
    (d : p.Degrees ι) {x : M a} (hx : x ∈ ℳ a i) :
    (p.cons e).homogeneousHistory T ℳ
        ((d, Degrees.terminalDegree i p d) : (p.cons e).Degrees ι) x =
      p.homogeneousHistory T ℳ d x := by
  rw [homogeneousHistory_cons_of_eq_id T ℳ p e he, LinearMap.comp_apply]
  exact Mei.homogeneousComponent_apply_of_mem (ℳ b)
    (homogeneousHistory_mem_vertex (T := T) (ℳ := ℳ) p d i x hx)

/-- Repeating the incoming degree at an identity arrow preserves the entire
final decoration after both propagation blocks. -/
@[simp]
theorem homogeneousHistory_degreesRepeat (p : Path a b) (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a)
    (d : (p.comp q).Degrees ι) {x : M a} (hx : x ∈ ℳ a i) :
    ((p.cons e).comp q).homogeneousHistory T ℳ (degreesRepeat p q e i d) x =
      (p.comp q).homogeneousHistory T ℳ d x := by
  rw [degreesRepeat, homogeneousHistory_comp, LinearMap.comp_apply,
    homogeneousHistory_cons_last_of_eq_id T ℳ p e he i _ hx]
  simpa only [LinearMap.comp_apply, Prod.mk.eta, Equiv.symm_apply_apply] using
    (LinearMap.congr_fun (homogeneousHistory_comp T ℳ p q
      ((degreesComp (ι := ι) p q) d).1 ((degreesComp (ι := ι) p q) d).2) x).symm

/-- A surviving history forces the inserted identity arrow to repeat the
incoming degree; an empty prefix uses the homogeneous input degree. -/
theorem last_eq_of_identity_history_ne_zero (p : Path a b) (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a)
    (d : ((p.cons e).comp q).Degrees ι) {x : M a} (hx : x ∈ ℳ a i)
    (hd : ((p.cons e).comp q).homogeneousHistory T ℳ d x ≠ 0) :
    (degreesComp (ι := ι) (p.cons e) q d).1.2 =
      Degrees.terminalDegree i p (degreesComp (ι := ι) (p.cons e) q d).1.1 := by
  by_contra hne
  apply hd
  rw [← (degreesComp (ι := ι) (p.cons e) q).symm_apply_apply d,
    homogeneousHistory_comp, LinearMap.comp_apply,
    homogeneousHistory_cons_of_eq_id T ℳ p e he, LinearMap.comp_apply,
    Mei.homogeneousComponent_apply_of_mem_ne (ℳ b)
      (homogeneousHistory_mem_vertex (T := T) (ℳ := ℳ) p _ i x hx) (Ne.symm hne), map_zero]

/-- Erasing an identity arrow from a surviving history keeps its whole output. -/
theorem homogeneousHistory_degreesErase (p : Path a b) (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a)
    (d : ((p.cons e).comp q).Degrees ι) {x : M a} (hx : x ∈ ℳ a i)
    (hd : ((p.cons e).comp q).homogeneousHistory T ℳ d x ≠ 0) :
    (p.comp q).homogeneousHistory T ℳ (degreesErase p q e d) x =
      ((p.cons e).comp q).homogeneousHistory T ℳ d x := by
  rw [← homogeneousHistory_degreesRepeat T ℳ p q e he i _ hx,
    degreesRepeat_degreesErase p q e i d
      (last_eq_of_identity_history_ne_zero T ℳ p q e he i d hx hd)]

/-- Insertion of an identity between arbitrary chamber blocks gives a bijection
of surviving histories. Whole decorations, rather than just their degrees, are
preserved. No injectivity of any propagation map is assumed. -/
def historySupportIdentityEquiv (p : Path a b) (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a) (x : ℳ a i) :
    ((p.comp q).historySupport T ℳ x : Type _) ≃
      (((p.cons e).comp q).historySupport T ℳ x : Type _) where
  toFun d := ⟨degreesRepeat p q e i d.val, by
    rw [mem_historySupport, homogeneousHistory_degreesRepeat T ℳ p q e he i _ x.property]
    exact (mem_historySupport ..).mp d.property⟩
  invFun d := ⟨degreesErase p q e d.val, by
    rw [mem_historySupport, homogeneousHistory_degreesErase T ℳ p q e he i _ x.property
      ((mem_historySupport ..).mp d.property)]
    exact (mem_historySupport ..).mp d.property⟩
  left_inv d := Subtype.ext (degreesErase_degreesRepeat p q e i d.val)
  right_inv d := Subtype.ext (degreesRepeat_degreesErase p q e i d.val
    (last_eq_of_identity_history_ne_zero T ℳ p q e he i d.val x.property
      ((mem_historySupport ..).mp d.property)))

/-- Insertion repeats the degree at the chosen block boundary. -/
@[simp]
theorem historySupportIdentityEquiv_val (p : Path a b) (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a) (x : ℳ a i)
    (d : ((p.comp q).historySupport T ℳ x : Type _)) :
    (historySupportIdentityEquiv T ℳ p q e he i x d).val =
      degreesRepeat p q e i d.val := (rfl)

/-- The inverse erases only the extra degree at the block boundary. -/
@[simp]
theorem historySupportIdentityEquiv_symm_val (p : Path a b) (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a) (x : ℳ a i)
    (d : (((p.cons e).comp q).historySupport T ℳ x : Type _)) :
    ((historySupportIdentityEquiv T ℳ p q e he i x).symm d).val =
      degreesErase p q e d.val := (rfl)

open Classical in
/-- Identity insertion preserves every finite incidence-selected expansion as an
identity of linear maps on a homogeneous input family. The finite index set is
fixed across that family; it need not contain every contributing history. -/
theorem sum_ite_comp_homogeneousHistory_degreesRepeat
    (p : Path a b) (q : Path b c) (e : b ⟶ b) (he : T e = LinearMap.id)
    (i : ι a) {E O : Type*} [AddCommMonoid E] [Module R E]
    [AddCommMonoid O] [Module R O]
    (f : E →ₗ[R] ℳ a i) (g : M c →ₗ[R] O)
    (S : Finset ((p.comp q).Degrees ι)) (P : (p.comp q).Degrees ι → Prop) :
    (∑ d ∈ S.image (degreesRepeat p q e i),
      if P (degreesErase p q e d) then
        g.comp ((((p.cons e).comp q).homogeneousHistory T ℳ d).comp
          ((ℳ a i).subtype.comp f)) else 0) =
      ∑ d ∈ S, if P d then
        g.comp (((p.comp q).homogeneousHistory T ℳ d).comp
          ((ℳ a i).subtype.comp f)) else 0 := by
  have hinj : Function.Injective (degreesRepeat p q e i) :=
    Function.LeftInverse.injective (degreesErase_degreesRepeat p q e i)
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro d _
  rw [degreesErase_degreesRepeat]
  split_ifs
  · ext x
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      homogeneousHistory_degreesRepeat T ℳ p q e he i _ (f x).property]
  · rfl

open Classical in
/-- Any selection of the retained histories has the same weighted sum after
inserting an identity. Distinct histories remain distinct even if their outputs
coincide or cancel. -/
theorem sum_ite_homogeneousHistory_identity (p : Path a b) (q : Path b c)
    (e : b ⟶ b) (he : T e = LinearMap.id) (i : ι a) (x : ℳ a i)
    (P : (p.comp q).Degrees ι → Prop) :
    (∑ d : (((p.cons e).comp q).historySupport T ℳ x : Type _),
      if P (degreesErase p q e d.val) then
        ((p.cons e).comp q).homogeneousHistory T ℳ d.val x else 0) =
      ∑ d : ((p.comp q).historySupport T ℳ x : Type _),
        if P d.val then (p.comp q).homogeneousHistory T ℳ d.val x else 0 := by
  symm
  apply Fintype.sum_equiv (historySupportIdentityEquiv T ℳ p q e he i x)
  intro d
  simp only [historySupportIdentityEquiv_val, degreesErase_degreesRepeat,
    homogeneousHistory_degreesRepeat T ℳ p q e he i _ x.property]

end Quiver.Path
