/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Basic

/-!
# Encounter bounds for filtered histories

A finite history is a composite of module endomorphisms. Some steps preserve a
decreasing filtration and the remaining steps raise it by one. If every maximal
block of preserving steps has length at most `h` and the filtration vanishes at
order `r`, then a nonzero history has at most `r - 1` raising steps and at most
`r * h + r - 1` steps in total.

The count of raising steps follows from the filtration order of the composite:
each raising step increases the order by one, and order `r` is zero. The total
length then follows from the hypothesis that the preserving steps occur in
blocks of length at most `h`. No ring inverse, commutativity, finite generation
or separatedness assumption is used.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The filtration action of a marked endomorphism: `false` preserves and `true`
raises the filtration by one. -/
def FiltrationStep (F : ModuleFiltration R M) (p : Module.End R M × Bool) : Prop :=
  match p.2 with
  | false => F.PreservesFiltration p.1
  | true => F.RaisesFiltration p.1

/-- A `false` mark preserves the filtration. -/
@[simp]
theorem filtrationStep_false {F : ModuleFiltration R M} {T : Module.End R M} :
    F.FiltrationStep (T, false) ↔ F.PreservesFiltration T := Iff.rfl

/-- A `true` mark raises the filtration by one. -/
@[simp]
theorem filtrationStep_true {F : ModuleFiltration R M} {T : Module.End R M} :
    F.FiltrationStep (T, true) ↔ F.RaisesFiltration T := Iff.rfl

/-- A marked step maps an element of filtration order `k` into the order increased
by its mark. -/
theorem FiltrationStep.map_mem {F : ModuleFiltration R M}
    {p : Module.End R M × Bool} (hp : F.FiltrationStep p) {k : ℕ} {x : M}
    (hx : x ∈ F.submodule k) :
    p.1 x ∈ F.submodule (k + if p.2 then 1 else 0) := by
  obtain ⟨T, mark⟩ := p
  cases mark
  · simpa using (PreservesFiltration.map_mem hp hx)
  · simpa using (RaisesFiltration.map_mem hp hx)

/-- Along a finite marked history, the composite maps filtration order `k` into
order `k` increased by the number of marked steps. -/
theorem map_prod_mem (F : ModuleFiltration R M) (s : List (Module.End R M × Bool))
    (hs : ∀ p ∈ s, F.FiltrationStep p) (k : ℕ) {x : M}
    (hx : x ∈ F.submodule k) :
    ((s.map Prod.fst).prod) x ∈ F.submodule (k + (s.map Prod.snd).count true) := by
  induction s generalizing k with
  | nil => simpa using hx
  | cons p s ih =>
      have hp : F.FiltrationStep p := hs p (by simp)
      have hs' : ∀ q ∈ s, F.FiltrationStep q := fun q hq => hs q (by simp [hq])
      obtain ⟨T, b⟩ := p
      have hmem := FiltrationStep.map_mem (p := (T, b)) hp
        (k := k + (s.map Prod.snd).count true) (ih hs' k hx)
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      have hidx : k + (b :: s.map Prod.snd).count true =
          (k + (s.map Prod.snd).count true) + if b then 1 else 0 := by
        cases b
        · simp
        · simp
          omega
      rw [hidx]
      exact hmem

/-- If a finite marked history has at least `r` marked steps, its composite vanishes
when filtration order `r` is zero. -/
theorem map_prod_eq_zero_of_le_count (F : ModuleFiltration R M) {r : ℕ}
    (hr : F.submodule r = ⊥) (s : List (Module.End R M × Bool))
    (hs : ∀ p ∈ s, F.FiltrationStep p)
    (hcount : r ≤ (s.map Prod.snd).count true) :
    (s.map Prod.fst).prod = 0 := by
  ext x
  have hmem := map_prod_mem F s hs 0 (x := x) (by simp)
  have hmem' : ((s.map Prod.fst).prod) x ∈ F.submodule r :=
    F.antitone hcount (by simpa using hmem)
  simpa [hr] using hmem'

/-- `RunsBoundedAux h run l`: given that the current block of `false` entries
already has length `run`, this block and every later maximal block of `false`
entries in `l` have length at most `h`. -/
def RunsBoundedAux (h run : ℕ) : List Bool → Prop
  | [] => run ≤ h
  | true :: l => run ≤ h ∧ RunsBoundedAux h 0 l
  | false :: l => RunsBoundedAux h (run + 1) l

/-- The empty list leaves only the run counter to check. -/
@[simp]
theorem runsBoundedAux_nil (h run : ℕ) : RunsBoundedAux h run [] ↔ run ≤ h := Iff.rfl

/-- A raising step closes the current block and starts a fresh one. -/
@[simp]
theorem runsBoundedAux_cons_true (h run : ℕ) (l : List Bool) :
    RunsBoundedAux h run (true :: l) ↔ run ≤ h ∧ RunsBoundedAux h 0 l := Iff.rfl

/-- A preserving step extends the current block by one. -/
@[simp]
theorem runsBoundedAux_cons_false (h run : ℕ) (l : List Bool) :
    RunsBoundedAux h run (false :: l) ↔ RunsBoundedAux h (run + 1) l := Iff.rfl

/-- Every maximal block of preserving (`false`) steps has length at most `h`. -/
def RunsBounded (h : ℕ) (l : List Bool) : Prop := RunsBoundedAux h 0 l

/-- The run counter read off the marks: prepending `run` preserving steps to `l`,
every block of preserving steps has length at most `h`. -/
private theorem runsBoundedAux_iff_splitOnPPrepend (h run : ℕ) (l : List Bool) :
    RunsBoundedAux h run l ↔
      ∀ b ∈ List.splitOnPPrepend (fun x : Bool => x == true) l (List.replicate run false),
        b.length ≤ h := by
  induction l generalizing run with
  | nil => simp [RunsBoundedAux, List.splitOnPPrepend_nil]
  | cons b l ih =>
      cases b with
      | false =>
          rw [show List.splitOnPPrepend (fun x : Bool => x == true) (false :: l)
                (List.replicate run false)
              = List.splitOnPPrepend (fun x : Bool => x == true) l
                (List.replicate (run + 1) false) from by
            rw [List.splitOnPPrepend_cons_neg (p := fun x : Bool => x == true) (a := false)
              (l := l) (acc := List.replicate run false) (by decide), ← List.replicate_succ]]
          exact ih (run + 1)
      | true =>
          rw [show List.splitOnPPrepend (fun x : Bool => x == true) (true :: l)
                (List.replicate run false)
              = List.replicate run false ::
                List.splitOnP (fun x : Bool => x == true) l from by
            rw [List.splitOnPPrepend_cons_pos (p := fun x : Bool => x == true) (a := true)
              (l := l) (acc := List.replicate run false) (by decide), List.reverse_replicate]]
          rw [RunsBoundedAux, List.forall_mem_cons, List.length_replicate]
          have hih := ih 0
          simp only [List.replicate, List.splitOnP_eq_splitOnPPrepend] at hih ⊢
          exact and_congr_right (fun _ => hih)

/-- The empty history is run-bounded. -/
@[simp]
theorem RunsBounded.nil (h : ℕ) : RunsBounded h [] := by
  simp [RunsBounded, RunsBoundedAux]

/-- `RunsBounded h l` holds exactly when every maximal block of preserving (`false`)
steps in `l`, as split off by the raising (`true`) steps, has length at most `h`. -/
theorem runsBounded_iff_splitOn {h : ℕ} {l : List Bool} :
    RunsBounded h l ↔ ∀ b ∈ l.splitOn true, b.length ≤ h := by
  change RunsBoundedAux h 0 l ↔ ∀ b ∈ l.splitOn true, b.length ≤ h
  have hmain := runsBoundedAux_iff_splitOnPPrepend h 0 l
  simp only [List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend, List.replicate]
    at hmain ⊢
  exact hmain

/-- A raising step starts a fresh block, so it does not affect the block bound. -/
@[simp]
theorem runsBounded_cons_true {h : ℕ} {l : List Bool} :
    RunsBounded h (true :: l) ↔ RunsBounded h l := by
  simp [RunsBounded, RunsBoundedAux]

/-- A preserving step extends the current block, which is then checked by the
run counter. -/
theorem runsBounded_cons_false {h : ℕ} {l : List Bool} :
    RunsBounded h (false :: l) ↔ RunsBoundedAux h 1 l := by
  simp [RunsBounded, RunsBoundedAux]

/-- If `RunsBoundedAux h run l`, then `run + l.length ≤ (r + 1) * h + r`, where
`r = l.count true`; with `run = 0` this bounds the length of a `RunsBounded h`
list. -/
theorem RunsBoundedAux.length_le (h run : ℕ) (l : List Bool)
    (hb : RunsBoundedAux h run l) :
    run + l.length ≤ (l.count true + 1) * h + l.count true := by
  induction l generalizing run with
  | nil =>
      simp only [RunsBoundedAux] at hb
      simpa using hb
  | cons b l ih =>
      cases b
      · simp only [RunsBoundedAux] at hb
        have hlen := ih (run + 1) hb
        rw [List.length_cons, List.count_cons_of_ne (by decide : (false : Bool) ≠ true)]
        omega
      · simp only [RunsBoundedAux] at hb
        obtain ⟨hrun, hrest⟩ := hb
        have hlen := ih 0 hrest
        rw [List.length_cons, List.count_cons_self]
        have hrewrite : (l.count true + 1 + 1) * h + (l.count true + 1) =
            ((l.count true + 1) * h + l.count true) + h + 1 := by ring
        rw [hrewrite]
        omega

/-- A run-bounded list of marks has length at most `(r + 1) * h + r`, where `r` is
the number of marked entries. -/
theorem RunsBounded.length_le {h : ℕ} {l : List Bool} (hb : RunsBounded h l) :
    l.length ≤ (l.count true + 1) * h + l.count true := by
  have hlen := RunsBoundedAux.length_le h 0 l hb
  simpa using hlen

/-- **Filtration encounter bound.** A nonzero composite of a finite marked history
has at most `r - 1` filtration-raising steps and at most `r * h + r - 1` steps in
total, provided filtration order `r` is zero and every maximal block of preserving
steps has length at most `h`. -/
theorem count_true_le_sub_one_and_length_le_of_prod_ne_zero (F : ModuleFiltration R M)
    {r h n : ℕ} (hr : F.submodule r = ⊥) (T : Fin n → Module.End R M)
    (mark : Fin n → Bool) (hstep : ∀ i, F.FiltrationStep (T i, mark i))
    (hblock : RunsBounded h (List.ofFn mark))
    (hne : (List.ofFn T).prod ≠ 0) :
    (List.ofFn mark).count true ≤ r - 1 ∧ n ≤ r * h + r - 1 := by
  let s : List (Module.End R M × Bool) := List.ofFn fun i : Fin n => (T i, mark i)
  have hs : ∀ p ∈ s, F.FiltrationStep p := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hstep i
  have hfst : s.map Prod.fst = List.ofFn T := by
    simp only [s, List.map_ofFn, Function.comp_def]
  have hsnd : s.map Prod.snd = List.ofFn mark := by
    simp only [s, List.map_ofFn, Function.comp_def]
  have hlt : (List.ofFn mark).count true < r := by
    by_contra h
    have hzero : (List.ofFn T).prod = 0 := by
      rw [← hfst]
      exact map_prod_eq_zero_of_le_count F hr s hs (by
        rw [hsnd]
        exact Nat.le_of_not_lt h)
    exact hne hzero
  refine ⟨Nat.le_sub_one_of_lt hlt, ?_⟩
  have hlen := RunsBounded.length_le hblock
  have hlen' : n ≤ ((List.ofFn mark).count true + 1) * h +
      (List.ofFn mark).count true := by
    simpa using hlen
  have hsucc : (List.ofFn mark).count true + 1 ≤ r := by omega
  have hmain : ((List.ofFn mark).count true + 1) * h +
      (List.ofFn mark).count true ≤ r * h + (r - 1) :=
    Nat.add_le_add (Nat.mul_le_mul_right h hsucc) (Nat.le_sub_one_of_lt hlt)
  omega

end Mei.ModuleFiltration
