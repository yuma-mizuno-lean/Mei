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

/-- An endomorphism preserves a module filtration if it maps each filtration
term into itself. -/
def PreservesFiltration (F : ModuleFiltration R M) (T : Module.End R M) : Prop :=
  ∀ k, F.submodule k ≤ (F.submodule k).comap T

/-- An endomorphism raises a module filtration by one if it maps filtration
order `k` into filtration order `k + 1`. -/
def RaisesFiltration (F : ModuleFiltration R M) (T : Module.End R M) : Prop :=
  ∀ k, F.submodule k ≤ (F.submodule (k + 1)).comap T

/-- A filtration-preserving endomorphism maps each filtration term into itself. -/
theorem PreservesFiltration.map_mem {F : ModuleFiltration R M} {T : Module.End R M}
    (hT : F.PreservesFiltration T) {k : ℕ} {x : M} (hx : x ∈ F.submodule k) :
    T x ∈ F.submodule k := hT k hx

/-- A filtration-raising endomorphism maps filtration order `k` into order `k + 1`. -/
theorem RaisesFiltration.map_mem {F : ModuleFiltration R M} {T : Module.End R M}
    (hT : F.RaisesFiltration T) {k : ℕ} {x : M} (hx : x ∈ F.submodule k) :
    T x ∈ F.submodule (k + 1) := hT k hx

/-- The filtration action of a marked endomorphism: `false` preserves and `true`
raises the filtration by one. -/
def FiltrationStep (F : ModuleFiltration R M) (p : Module.End R M × Bool) : Prop :=
  match p.2 with
  | false => F.PreservesFiltration p.1
  | true => F.RaisesFiltration p.1

/-- A marked step maps an element of filtration order `k` into the order increased
by its mark. -/
theorem FiltrationStep.map_mem {F : ModuleFiltration R M}
    {p : Module.End R M × Bool} (hp : F.FiltrationStep p) {k : ℕ} {x : M}
    (hx : x ∈ F.submodule k) :
    p.1 x ∈ F.submodule (k + if p.2 then 1 else 0) := by
  obtain ⟨T, mark⟩ := p
  cases mark
  · simpa [FiltrationStep] using (PreservesFiltration.map_mem hp hx)
  · simpa [FiltrationStep] using (RaisesFiltration.map_mem hp hx)

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
      -- Unfold the cons product definitionally so that the induction hypothesis applies.
      change T ((s.map Prod.fst).prod x) ∈
        F.submodule (k + (List.map Prod.snd ((T, b) :: s)).count true)
      have hidx : k + (List.map Prod.snd ((T, b) :: s)).count true =
          (k + (List.map Prod.snd s).count true) + if b then 1 else 0 := by
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

/-- Auxiliary run counter: `run` is the length of the current block of `false`
entries, every completed block already has length at most `h`, and `false` entries
after the current block are still to be checked. -/
def RunsBoundedAux (h run : ℕ) : List Bool → Prop
  | [] => run ≤ h
  | true :: l => run ≤ h ∧ RunsBoundedAux h 0 l
  | false :: l => RunsBoundedAux h (run + 1) l

/-- Every maximal block of preserving (`false`) steps has length at most `h`. -/
def RunsBounded (h : ℕ) (l : List Bool) : Prop := RunsBoundedAux h 0 l

private theorem count_true_cons_true (l : List Bool) :
    (true :: l).count true = l.count true + 1 := by simp

private theorem count_true_cons_false (l : List Bool) :
    (false :: l).count true = l.count true := by simp

/-- A run-bounded list of marks has length at most `(r + 1) * h + r`, where `r` is
the number of marked entries. -/
theorem RunsBoundedAux.length_le (h run : ℕ) (l : List Bool)
    (hb : RunsBoundedAux h run l) :
    run + l.length ≤ (l.count true + 1) * h + l.count true := by
  induction l generalizing run with
  | nil =>
      -- Unfold the run counter at the end of the list.
      change run ≤ h at hb
      simpa using hb
  | cons b l ih =>
      cases b
      · -- Unfold the run counter at a preserving step.
        change RunsBoundedAux h (run + 1) l at hb
        have hlen := ih (run + 1) hb
        rw [List.length_cons, count_true_cons_false]
        omega
      · -- Unfold the run counter at a raising step and reset the current run.
        change run ≤ h ∧ RunsBoundedAux h 0 l at hb
        obtain ⟨hrun, hrest⟩ := hb
        have hlen := ih 0 hrest
        rw [List.length_cons, count_true_cons_true]
        have hrewrite : (l.count true + 1 + 1) * h + (l.count true + 1) =
            ((l.count true + 1) * h + l.count true) + h + 1 := by ring
        rw [hrewrite]
        omega

/-- **Filtration encounter bound.** A nonzero composite of a finite marked history
has at most `r - 1` filtration-raising steps and at most `r * h + r - 1` steps in
total, provided filtration order `r` is zero and every maximal block of preserving
steps has length at most `h`. -/
theorem filtrationEncounterBound (F : ModuleFiltration R M) {r h n : ℕ}
    (hr : F.submodule r = ⊥) (T : Fin n → Module.End R M) (mark : Fin n → Bool)
    (hstep : ∀ i, F.FiltrationStep (T i, mark i))
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
  have hlen := RunsBoundedAux.length_le h 0 (List.ofFn mark) hblock
  have hlen' : n ≤ ((List.ofFn mark).count true + 1) * h +
      (List.ofFn mark).count true := by
    simpa using hlen
  have hsucc : (List.ofFn mark).count true + 1 ≤ r := by omega
  have hmain : ((List.ofFn mark).count true + 1) * h +
      (List.ofFn mark).count true ≤ r * h + (r - 1) :=
    Nat.add_le_add (Nat.mul_le_mul_right h hsucc) (Nat.le_sub_one_of_lt hlt)
  omega

end Mei.ModuleFiltration
