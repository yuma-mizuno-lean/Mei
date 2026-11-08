/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Filtration
public import Mei.LinearAlgebra.GradedModule.History.Path.Labels

/-!
# Filtration ranks of the segments of a complete degree history

Give each component encounter `e : b ⟶ c` between the degrees `i` and `j` a natural
number mark `w e i j`. The ranks of a degree history accumulate these marks: the
incoming segment has rank zero, and every later segment has the rank of the previous one
plus the mark of the encounter between them. Marks and ranks are listed in backward
order, with the last encounter and the final segment at index zero, exactly like
`Quiver.Path.Degrees.reverseVertexLabels`. Chamber modules and degree types may vary
along the path, and every encounter keeps its own mark, including encounters whose two
degrees agree.

The rank of the final segment is the total weight of the lifted history, so a nonzero
whole history through a nilpotent filtration, with component transfers raising it by
the marks, has final rank below the vanishing order. Consecutive ranks agree exactly
when the intervening mark is zero. When zero marks force equal labels, such as spatial
directions, consecutive labels of segments of equal rank agree: ranks stratify a history
into runs of constant label.
-/

public section

namespace Quiver.Path.Degrees

open Mei

variable {Q : Type*} [Quiver Q] {ι : Q → Type*} {a : Q}
  (w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ) (i₀ : ι a)

/-- The mark of every encounter of a complete degree history, in backward order. -/
def reverseMarks : {b : Q} → (p : Path a b) → p.Degrees ι → Fin p.length → ℕ
  | _, nil, _ => Fin.elim0
  | _, @cons _ _ _ _ _ p e, d => Fin.cons (w e (terminalDegree i₀ p d.1) d.2) (reverseMarks p d.1)

/-- The ranks of the segments of a complete degree history, in backward order: the sum of
the marks of all earlier encounters. -/
def reverseRanks : {b : Q} → (p : Path a b) → p.Degrees ι → Fin (p.length + 1) → ℕ
  | _, nil, _ => fun _ => 0
  | _, @cons _ _ _ _ _ p e, d =>
      Fin.cons (reverseRanks p d.1 0 + w e (terminalDegree i₀ p d.1) d.2) (reverseRanks p d.1)

/-- The last encounter carries the mark of its two adjacent degrees. -/
@[simp]
theorem reverseMarks_cons_zero {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) :
    reverseMarks w i₀ (p.cons e) (d, i) (0 : Fin (p.length + 1)) =
      w e (terminalDegree i₀ p d) i := Fin.cons_zero ..

/-- The marks of earlier encounters are those of the shorter path. -/
@[simp]
theorem reverseMarks_cons_succ {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) (j : Fin p.length) :
    reverseMarks w i₀ (p.cons e) (d, i) j.succ = reverseMarks w i₀ p d j := Fin.cons_succ ..

/-- The final rank adds the mark of the last encounter to the previous final rank. -/
theorem reverseRanks_cons_zero {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) :
    reverseRanks w i₀ (p.cons e) (d, i) (0 : Fin (p.length + 1 + 1)) =
      reverseRanks w i₀ p d 0 + w e (terminalDegree i₀ p d) i := Fin.cons_zero ..

/-- The ranks of earlier segments are those of the shorter path. -/
@[simp]
theorem reverseRanks_cons_succ {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι)
    (i : ι c) (j : Fin (p.length + 1)) :
    reverseRanks w i₀ (p.cons e) (d, i) j.succ = reverseRanks w i₀ p d j := Fin.cons_succ ..

/-- The incoming segment has rank zero. -/
@[simp]
theorem reverseRanks_last : ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
    reverseRanks w i₀ p d (Fin.last p.length) = 0
  | _, nil, _ => rfl
  | _, cons p e, d => (reverseRanks_cons_succ w i₀ p e d.1 d.2 (Fin.last p.length)).trans
      (reverseRanks_last p d.1)

/-- A segment's rank is the rank of the previous segment plus the mark of the
encounter between them. -/
theorem reverseRanks_castSucc : ∀ {b : Q} (p : Path a b) (d : p.Degrees ι) (j : Fin p.length),
    reverseRanks w i₀ p d j.castSucc =
      reverseRanks w i₀ p d j.succ + reverseMarks w i₀ p d j
  | _, nil, _, j => j.elim0
  | _, cons p e, d, j => by
    obtain ⟨d, i⟩ := d
    refine Fin.cases (motive := fun j : Fin (p.length + 1) =>
      reverseRanks w i₀ (p.cons e) (d, i) j.castSucc =
        reverseRanks w i₀ (p.cons e) (d, i) j.succ + reverseMarks w i₀ (p.cons e) (d, i) j)
      ?_ (fun k => ?_) j
    · simp only [Fin.castSucc_zero, reverseMarks_cons_zero, reverseRanks_cons_succ]
      exact reverseRanks_cons_zero w i₀ p e d i
    · simp only [Fin.castSucc_succ, reverseRanks_cons_succ, reverseMarks_cons_succ]
      exact reverseRanks_castSucc p d k

/-- Ranks decrease backwards along a history. -/
theorem antitone_reverseRanks {b : Q} (p : Path a b) (d : p.Degrees ι) :
    Antitone (reverseRanks w i₀ p d) :=
  Fin.antitone_iff_succ_le.mpr fun j => by
    rw [reverseRanks_castSucc]
    exact Nat.le_add_right _ _

/-- The rank of the final segment is the total weight of the lifted history. -/
theorem reverseRanks_zero : ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
    reverseRanks w i₀ p d 0 =
      addWeight (GradedVertex.componentWeight w) (liftPath i₀ p d)
  | _, nil, _ => by
    rw [liftPath_nil, addWeight_nil]
    rfl
  | _, cons p e, d => by
    obtain ⟨d, i⟩ := d
    refine (reverseRanks_cons_zero w i₀ p e d i).trans ?_
    rw [addWeight_componentWeight_liftPath_cons, reverseRanks_zero p d]

/-- Consecutive segments of equal rank are separated by a zero mark. -/
theorem reverseMarks_eq_zero_of_reverseRanks_castSucc_eq {b : Q} (p : Path a b)
    (d : p.Degrees ι) (j : Fin p.length)
    (h : reverseRanks w i₀ p d j.castSucc = reverseRanks w i₀ p d j.succ) :
    reverseMarks w i₀ p d j = 0 := by
  rw [reverseRanks_castSucc] at h
  omega

/-- If zero marks force equal labels, consecutive segments of equal rank carry equal
labels. Chamber degrees with equal labels need not be equal, and every encounter
between them is retained. -/
theorem reverseVertexLabels_castSucc_eq_succ_of_reverseRanks_eq {A : Type*}
    (v : ∀ q, ι q → A)
    (hv : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c), w e i j = 0 → v b i = v c j) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι) (j : Fin p.length),
      reverseRanks w i₀ p d j.castSucc = reverseRanks w i₀ p d j.succ →
        reverseVertexLabels v i₀ p d j.castSucc = reverseVertexLabels v i₀ p d j.succ
  | _, nil, _, j, _ => j.elim0
  | _, cons p e, d, j, h => by
    obtain ⟨d, i⟩ := d
    revert h
    refine Fin.cases (motive := fun j : Fin (p.length + 1) =>
      reverseRanks w i₀ (p.cons e) (d, i) j.castSucc =
          reverseRanks w i₀ (p.cons e) (d, i) j.succ →
        reverseVertexLabels v i₀ (p.cons e) (d, i) j.castSucc =
          reverseVertexLabels v i₀ (p.cons e) (d, i) j.succ) (fun h => ?_) (fun k h => ?_) j
    · have hm := reverseMarks_eq_zero_of_reverseRanks_castSucc_eq w i₀ (p.cons e) (d, i)
        (0 : Fin (p.length + 1)) h
      rw [reverseMarks_cons_zero] at hm
      rw [Fin.castSucc_zero]
      refine (reverseVertexLabels_cons_zero v i₀ p e d i).trans (Eq.trans ?_
        (reverseVertexLabels_cons_succ v i₀ p e d i 0).symm)
      rw [reverseVertexLabels_zero]
      exact (hv e _ _ hm).symm
    · simp only [Fin.castSucc_succ, reverseRanks_cons_succ] at h
      simp only [Fin.castSucc_succ, reverseVertexLabels_cons_succ]
      exact reverseVertexLabels_castSucc_eq_succ_of_reverseRanks_eq v hv p d k h

end Quiver.Path.Degrees

namespace Quiver.Path

open Mei

variable {Q : Type*} [Quiver Q] {ι : Q → Type*} {a : Q}
  {R : Type*} [Semiring R] {M : Q → Type*}
  [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, DecidableEq (ι q)]
  {T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c}
  {ℳ : ∀ q, ι q → Submodule R (M q)} [∀ q, DirectSum.Decomposition (ℳ q)]
  {F : ∀ q, ModuleFiltration R (M q)}
  {w : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ}

/-- A surviving history through a nilpotent filtration has final rank below the
vanishing order, however its encounters are marked. -/
theorem Degrees.reverseRanks_zero_lt_of_homogeneousHistory_ne_zero {b : Q} (p : Path a b)
    (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := w))
    (i₀ : ι a) {d : p.Degrees ι} {x : M a} {r : ℕ}
    (hx : x ∈ ℳ a i₀) (hr : (F b).submodule r = ⊥)
    (hne : p.homogeneousHistory T ℳ d x ≠ 0) :
    Degrees.reverseRanks w i₀ p d 0 < r := by
  rw [Degrees.reverseRanks_zero]
  exact componentWeight_lt_of_homogeneousHistory_ne_zero p hT i₀ hx hr hne

end Quiver.Path
