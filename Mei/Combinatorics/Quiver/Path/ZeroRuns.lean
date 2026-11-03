/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Tactic.Linarith

/-!
# Runs of weight zero along quiver paths

Give every arrow of a quiver a natural number weight, and write `Quiver.Path.addWeight` for the
total weight of a path. A path has *zero-weight runs of length at most `h`* when every subpath of
total weight zero uses at most `h` arrows. A path of total weight `W` has at most `W` arrows of
positive weight, which cut it into at most `W + 1` stretches of weightless arrows, each of length at
most `h`; so its length is at most `(W + 1) * h + W`.

## Main declarations

* `Quiver.Path.IsZeroRunBounded`: every subpath of weight zero has at most `h` arrows.
* `Quiver.Path.isZeroRunBounded_cons_iff`, `Quiver.Path.IsZeroRunBounded.of_comp_left`,
  `Quiver.Path.IsZeroRunBounded.of_comp_right`: introduction and restriction lemmas.
* `Quiver.Path.length_add_one_le_of_isZeroRunBounded`: the length of such a path satisfies
  `length + 1 ≤ (addWeight w p + 1) * (h + 1)`.
-/

public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {a : V} (w : ∀ {b c : V}, (b ⟶ c) → ℕ) (h : ℕ)

/-- A path has zero-weight runs of length at most `h` when each of its subpaths of total weight
zero has at most `h` arrows. -/
def IsZeroRunBounded {b : V} (p : Path a b) : Prop :=
  ∀ {u v : V} (p₁ : Path a u) (q : Path u v) (p₂ : Path v b),
    p = (p₁.comp q).comp p₂ → addWeight w q = 0 → q.length ≤ h

variable {w h}

/-- The defining condition of `IsZeroRunBounded`. -/
theorem isZeroRunBounded_iff {b : V} {p : Path a b} :
    IsZeroRunBounded w h p ↔
      ∀ {u v : V} (p₁ : Path a u) (q : Path u v) (p₂ : Path v b),
        p = (p₁.comp q).comp p₂ → addWeight w q = 0 → q.length ≤ h := Iff.rfl

/-- The empty path has no zero-weight runs of positive length. -/
@[simp]
theorem isZeroRunBounded_nil : IsZeroRunBounded w h (nil : Path a a) := by
  intro u v p₁ q p₂ hdec _
  have hlen := congrArg length hdec
  simp only [length_nil, length_comp] at hlen
  omega

/-- Dropping the last arrow keeps the zero-weight runs short. -/
theorem IsZeroRunBounded.of_cons {b c : V} {p : Path a b} {e : b ⟶ c}
    (hp : IsZeroRunBounded w h (p.cons e)) : IsZeroRunBounded w h p := by
  intro u v p₁ q p₂ hdec hq
  exact hp p₁ q (p₂.cons e) (by rw [hdec, comp_cons]) hq

/-- A subpath at the start of a path with short zero-weight runs has short zero-weight runs. -/
theorem IsZeroRunBounded.of_comp_left {b c : V} {p : Path a b} {q : Path b c}
    (hp : IsZeroRunBounded w h (p.comp q)) : IsZeroRunBounded w h p := by
  intro u v p₁ r p₂ hdec hr
  exact hp p₁ r (p₂.comp q) (by rw [hdec, comp_assoc]) hr

/-- A subpath at the end of a path with short zero-weight runs has short zero-weight runs. -/
theorem IsZeroRunBounded.of_comp_right {b c : V} {p : Path a b} {q : Path b c}
    (hp : IsZeroRunBounded w h (p.comp q)) : IsZeroRunBounded w h q := by
  intro u v p₁ r p₂ hdec hr
  exact hp (p.comp p₁) r p₂ (by rw [hdec]; simp only [comp_assoc]) hr

/-- The path `p.cons e` has short zero-weight runs exactly when `p` does and every suffix `q` of `p`
for which `q` followed by `e` has weight zero has fewer than `h` arrows. -/
theorem isZeroRunBounded_cons_iff {b c : V} {p : Path a b} {e : b ⟶ c} :
    IsZeroRunBounded w h (p.cons e) ↔ IsZeroRunBounded w h p ∧
      ∀ {u : V} (p₁ : Path a u) (q : Path u b),
        p = p₁.comp q → addWeight w q + w e = 0 → q.length + 1 ≤ h := by
  refine ⟨fun hp => ⟨hp.of_cons, fun p₁ q hpq hq => ?_⟩, fun hh => ?_⟩
  · have := hp p₁ (q.cons e) nil (by rw [hpq, comp_cons, comp_nil]) (by simpa using hq)
    simpa using this
  · obtain ⟨hp, hs⟩ := hh
    intro u v p₁ q p₂ hdec hq
    cases p₂ with
    | nil =>
      cases q with
      | nil => simp
      | cons q' e' =>
        rw [comp_nil, comp_cons] at hdec
        obtain rfl := obj_eq_of_cons_eq_cons hdec
        obtain ⟨-, hpq, he⟩ := Path.cons.inj hdec
        obtain rfl := eq_of_heq he
        have := hs p₁ q' (eq_of_heq hpq) (by simpa using hq)
        simpa using this
    | cons p₂' e' =>
      obtain rfl := obj_eq_of_cons_eq_cons hdec
      obtain ⟨-, hpq, -⟩ := Path.cons.inj hdec
      exact hp p₁ q p₂' (eq_of_heq hpq) hq

/-- A path with short zero-weight runs ends with a weightless stretch `q` of at most `h` arrows,
and its length is bounded by `h + 1` for each unit of weight, plus the length of `q`. -/
theorem IsZeroRunBounded.exists_suffix {b : V} {p : Path a b}
    (hp : IsZeroRunBounded w h p) :
    ∃ (u : V) (p₁ : Path a u) (q : Path u b), p = p₁.comp q ∧ addWeight w q = 0 ∧
      q.length ≤ h ∧ p.length ≤ addWeight w p * (h + 1) + q.length := by
  induction p with
  | nil => exact ⟨a, nil, nil, rfl, addWeight_nil w a, Nat.zero_le _, by simp⟩
  | @cons b' c p e ih =>
    obtain ⟨u, p₁, q, hpq, hq, hqh, hlen⟩ := ih hp.of_cons
    by_cases he : w e = 0
    · refine ⟨u, p₁, q.cons e, by rw [hpq, comp_cons], by simp [hq, he], ?_, ?_⟩
      · exact hp p₁ (q.cons e) nil (by rw [hpq, comp_cons, comp_nil]) (by simp [hq, he])
      · simp only [length_cons, addWeight_cons, he, Nat.add_zero]
        omega
    · refine ⟨c, p.cons e, nil, rfl, addWeight_nil w c, Nat.zero_le _, ?_⟩
      have hw : addWeight w p + 1 ≤ addWeight w p + w e := by omega
      have := Nat.mul_le_mul_right (h + 1) hw
      simp only [length_cons, addWeight_cons, length_nil]
      nlinarith

/-- A path whose zero-weight runs have at most `h` arrows and whose total weight is `W` has at most
`(W + 1) * h + W` arrows. -/
theorem length_add_one_le_of_isZeroRunBounded {b : V} {p : Path a b}
    (hp : IsZeroRunBounded w h p) : p.length + 1 ≤ (addWeight w p + 1) * (h + 1) := by
  obtain ⟨u, p₁, q, -, -, hqh, hlen⟩ := hp.exists_suffix
  nlinarith

end Quiver.Path
