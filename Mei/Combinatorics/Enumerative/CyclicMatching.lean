/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Matching tokens with sinks on a cycle

Arrange `n` positions on a cycle, call the positions in `B` sinks, and put `τ k` tokens at
every other position `k`. Give a sink the weight `-1` and any other position the weight `τ k`.
A sink `v` is *matched* if some non-sink `h` reaches it before balancing: every cyclic window
from `h` that stops strictly before `v` has nonzero total weight.

The number of matched sinks is `min #B (∑ k ∉ B, τ k)`. Equivalently a sink is matched
exactly when some cyclic window ending just before it has positive weight, and the unmatched
sinks are counted by the record lows of the periodic walk when the total weight is negative.
In periods after the first, unmatched sinks are exactly the drops of the running minimum,
and each period contributes `#B - ∑ τ` such drops. When the total weight is nonnegative,
every sink is matched; record lows in the initial period need not be unmatched.

This is a cycle lemma in the style of Dvoretzky–Motzkin; it counts the total shadows of gradings
of maximal Dyck paths.
-/

public section

open Finset

namespace Fin

variable {n : ℕ}

/-- The offset of `k` from `e` vanishes exactly at `e`. -/
theorem val_sub_eq_zero_iff {k e : Fin n} : (k - e).val = 0 ↔ k = e := by
  have : NeZero n := ⟨e.pos.ne'⟩
  rw [Fin.val_eq_zero_iff]
  exact sub_eq_zero

/-- The offset of a position from itself is zero. -/
@[simp]
theorem val_sub_self (e : Fin n) : (e - e).val = 0 :=
  val_sub_eq_zero_iff.mpr rfl

/-- A position lies in the cyclic interval `[a, c]` exactly when its distance to `c` is at most
the length of the interval. -/
theorem val_sub_le_val_sub_iff (a b c : Fin n) :
    (c - b).val ≤ (c - a).val ↔ (b - a).val ≤ (c - a).val := by
  have : NeZero n := ⟨a.pos.ne'⟩
  have hcb : c - b = (c - a) - (b - a) := by abel
  rw [hcb]
  exact Fin.sub_le_iff

end Fin

namespace Mei.CyclicMatching

open Fin (val_sub_eq_zero_iff val_sub_self val_sub_le_val_sub_iff)

variable {n : ℕ}

/-- The cyclic interval from `e` to `e'`, both included. -/
def cyclicIcc (e e' : Fin n) : Finset (Fin n) := {k | (k - e).val ≤ (e' - e).val}

@[simp]
theorem mem_cyclicIcc {e e' k : Fin n} : k ∈ cyclicIcc e e' ↔ (k - e).val ≤ (e' - e).val := by
  simp [cyclicIcc]

/-- The one-point cyclic interval. -/
@[simp]
theorem cyclicIcc_self (e : Fin n) : cyclicIcc e e = {e} := by
  ext k
  rw [mem_cyclicIcc, val_sub_self, Nat.le_zero, val_sub_eq_zero_iff, mem_singleton]

/-- Negation reverses cyclic intervals. -/
theorem neg_mem_cyclicIcc {e v x : Fin n} : -x ∈ cyclicIcc e v ↔ x ∈ cyclicIcc (-v) (-e) := by
  have : NeZero n := ⟨e.pos.ne'⟩
  rw [mem_cyclicIcc, mem_cyclicIcc, ← val_sub_le_val_sub_iff e (-x) v]
  simp only [sub_eq_add_neg, neg_neg, add_comm]

variable (B : Finset (Fin n)) (τ : Fin n → ℕ)

/-- The weight of a position: `-1` at a sink and the number of tokens elsewhere. -/
def weight (k : Fin n) : ℤ := if k ∈ B then -1 else τ k

theorem weight_def (k : Fin n) : weight B τ k = if k ∈ B then -1 else (τ k : ℤ) := (rfl)

/-- A sink has weight `-1`. -/
@[simp]
theorem weight_of_mem {k : Fin n} (hk : k ∈ B) : weight B τ k = -1 := by
  simp [weight, hk]

/-- A non-sink has nonnegative weight. -/
theorem weight_nonneg {k : Fin n} (hk : k ∉ B) : 0 ≤ weight B τ k := by
  simp [weight, hk]

/-- A non-sink carries its tokens as weight. -/
@[simp]
theorem weight_of_notMem {k : Fin n} (hk : k ∉ B) : weight B τ k = τ k := by
  simp [weight, hk]

/-- Every weight is at least `-1`. -/
theorem neg_one_le_weight (k : Fin n) : -1 ≤ weight B τ k := by
  unfold weight
  split_ifs
  · exact le_rfl
  · exact le_trans (by decide) (Int.natCast_nonneg _)

/-- A position of negative weight is a sink. -/
theorem mem_of_weight_neg {k : Fin n} (hk : weight B τ k < 0) : k ∈ B := by
  by_contra h
  exact absurd hk (not_lt.mpr (weight_nonneg B τ h))

/-- A weight sum counts tokens off the sinks and subtracts the sinks. -/
theorem sum_weight_eq (S : Finset (Fin n)) :
    ∑ k ∈ S, weight B τ k = (∑ k ∈ S ∩ Bᶜ, τ k : ℕ) - (#(S ∩ B) : ℤ) := by
  rw [← sum_filter_add_sum_filter_not S (· ∈ B)]
  rw [sum_congr rfl fun k hk ↦ weight_of_mem B τ (mem_filter.mp hk).2,
    sum_congr rfl fun k hk ↦ weight_of_notMem B τ (mem_filter.mp hk).2]
  have hfilter : S.filter (· ∉ B) = S ∩ Bᶜ := by ext; simp
  rw [filter_mem_eq_inter, hfilter]
  simp [sub_eq_neg_add]

/-- The total weight is the number of tokens minus the number of sinks. -/
theorem sum_weight : ∑ i : Fin n, weight B τ i = (∑ k ∈ Bᶜ, τ k : ℕ) - (#B : ℤ) := by
  simpa using sum_weight_eq B τ Finset.univ

/-- A sink `v` is matched if from some non-sink `h`, every cyclic window `[h, e]` stopping
strictly before `v` has nonzero total weight. -/
def Matched (v : Fin n) : Prop :=
  ∃ h ∉ B, ∀ e : Fin n, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0

/-- A matched position has a non-sink whose proper initial cyclic windows have nonzero weight. -/
theorem matched_iff_forall (v : Fin n) :
    Matched B τ v ↔ ∃ h ∉ B, ∀ e : Fin n,
      (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0 := (Iff.rfl)

instance : DecidablePred (Matched B τ) := fun v ↦
  decidable_of_iff (∃ h ∉ B, ∀ e : Fin n,
    (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0)
    (matched_iff_forall B τ v).symm

section Walk

variable [NeZero n]

/-- The position of the periodic extension at time `k`. -/
private def pos (k : ℕ) : Fin n := Fin.ofNat n k

/-- The walk of partial weight sums along the periodic extension. -/
private def walk (k : ℕ) : ℤ := ∑ j ∈ range k, weight B τ (pos j)

private theorem pos_add_self (k : ℕ) : pos (k + n) = (pos k : Fin n) := by
  simp [pos, Fin.ext_iff]

private theorem walk_succ (k : ℕ) : walk B τ (k + 1) = walk B τ k + weight B τ (pos k) := by
  simp [walk, sum_range_succ]

/-- One period changes the walk by the total weight. -/
private theorem walk_add_self (k : ℕ) :
    walk B τ (k + n) = walk B τ k + ∑ i : Fin n, weight B τ i := by
  induction k with
  | zero =>
    rw [zero_add, walk, ← Fin.sum_univ_eq_sum_range (fun j ↦ weight B τ (pos j)) n]
    simp [walk, pos]
  | succ k ih =>
    -- Put the shifted successor in the form required by walk_succ.
    rw [show k + 1 + n = k + n + 1 by omega, walk_succ, ih, walk_succ, pos_add_self,
      add_right_comm]

/-- A cyclic window sum is an increment of the walk. -/
private theorem sum_cyclicIcc (h e : Fin n) :
    ∑ k ∈ cyclicIcc h e, weight B τ k = walk B τ (h.val + (e - h).val + 1) - walk B τ h.val := by
  have himage : cyclicIcc h e = (range ((e - h).val + 1)).image fun j ↦ h + pos j := by
    ext k
    simp only [mem_cyclicIcc, mem_image, mem_range, Nat.lt_succ_iff]
    constructor
    · intro hk
      exact ⟨(k - h).val, hk, by simp [pos]⟩
    · rintro ⟨j, hj, rfl⟩
      have hjn : j < n := lt_of_le_of_lt hj (e - h).isLt
      simpa [pos, Nat.mod_eq_of_lt hjn] using hj
  have hinj : Set.InjOn (fun j ↦ h + pos j) (range ((e - h).val + 1) : Set ℕ) := by
    intro i hi j hj hij
    have hin : i < n := lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hi)) (e - h).isLt
    have hjn : j < n := lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hj)) (e - h).isLt
    have := congrArg Fin.val (add_left_cancel hij)
    simpa [pos, Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hjn] using this
  rw [himage, sum_image hinj, walk, walk, add_assoc,
    sum_range_add (fun j ↦ weight B τ (pos j)) h.val ((e - h).val + 1), add_sub_cancel_left]
  refine sum_congr rfl fun j _ ↦ ?_
  congr 1
  simp [pos, Fin.ext_iff, Fin.val_add, Nat.add_mod]


private theorem pos_add (a b : ℕ) : pos (a + b) = (pos a + pos b : Fin n) := by
  simp [pos, Fin.ext_iff, Fin.val_add, Nat.add_mod]

private theorem pos_val (k : Fin n) : pos k.val = k := by
  simp [pos]

/-- The walk is periodic up to the total weight. -/
private theorem walk_add_self_sub (a b : ℕ) :
    walk B τ (b + n) - walk B τ (a + n) = walk B τ b - walk B τ a := by
  rw [walk_add_self, walk_add_self]
  abel

/-- The cyclic offset to `v` from a time in its preceding period. -/
private theorem val_sub_pos_of_mem_period {v : Fin n} {a : ℕ}
    (hva : v.val < a) (hav : a < v.val + n) :
    (v - pos a).val = v.val + n - a := by
  have hv' : v = pos a + pos (v.val + n - a) := by
    -- Natural subtraction cancels because a lies in this preceding period.
    rw [← pos_add, show a + (v.val + n - a) = v.val + n by omega,
      pos_add_self, pos_val]
  rw [sub_eq_iff_eq_add'.mpr hv']
  -- The same period bounds keep the offset below the modulus.
  simp [pos, Nat.mod_eq_of_lt (show v.val + n - a < n by omega)]

/-- A walk increment depends only on the residue of its starting time. -/
private theorem walk_increment_pos (a t : ℕ) :
    walk B τ ((pos a : Fin n).val + t) - walk B τ (pos a : Fin n).val =
      walk B τ (a + t) - walk B τ a := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, walk_succ, Nat.add_succ, walk_succ]
    have hp : pos ((pos a : Fin n).val + t) = (pos (a + t) : Fin n) := by
      simp [pos, Fin.ext_iff, Nat.add_mod]
    rw [hp]
    linarith

/-- Starting at a non-sink, a walk whose increments never vanish stays above its start. -/
private theorem lt_walk_of_ne {a s : ℕ} (ha : pos a ∉ B)
    (hne : ∀ t < s, walk B τ (a + t + 1) ≠ walk B τ a) :
    ∀ t < s, walk B τ a < walk B τ (a + t + 1) := by
  intro t
  induction t with
  | zero =>
    intro hs
    have h₀ := weight_nonneg B τ ha
    have h₁ := hne 0 hs
    rw [add_zero, walk_succ] at h₁ ⊢
    omega
  | succ t ih =>
    intro hs
    have h₀ := ih (by omega)
    have h₁ := hne (t + 1) hs
    have h₂ := neg_one_le_weight B τ (pos (a + t + 1))
    -- Reassociate the time so walk_succ exposes the final weight.
    rw [show a + (t + 1) + 1 = a + t + 1 + 1 by omega, walk_succ] at h₁ ⊢
    omega


/-- A last point below the final walk height lies strictly below every later point.
Choosing the maximum such time in the open interval gives the start of a matched window. -/
private theorem exists_last_low_point {l i : ℕ}
    (h : ∃ a, l < a ∧ a < i ∧ walk B τ a < walk B τ i) :
    ∃ a, l < a ∧ a < i ∧ ∀ j, a < j → j ≤ i → walk B τ a < walk B τ j := by
  obtain ⟨a, hla, hai, hwa⟩ := h
  set F := (Ioo l i).filter fun a ↦ walk B τ a < walk B τ i
  have hF : F.Nonempty := ⟨a, by simp [F, hla, hai, hwa]⟩
  set a' := F.max' hF
  have ha'F : a' ∈ F := F.max'_mem hF
  simp only [F, mem_filter, mem_Ioo] at ha'F
  obtain ⟨⟨hla', ha'i⟩, hwa'⟩ := ha'F
  have habove : ∀ j, a' < j → j ≤ i → walk B τ a' < walk B τ j := by
    intro j hj hji
    rcases lt_or_eq_of_le hji with hji | rfl
    · by_contra hle
      have hjF : j ∈ F := by
        simp only [F, mem_filter, mem_Ioo]
        exact ⟨⟨by omega, hji⟩, by linarith [not_lt.mp hle]⟩
      exact absurd (F.le_max' j hjF) (not_le.mpr hj)
    · exact hwa'
  exact ⟨a', hla', ha'i, habove⟩

/-- A sink is matched exactly when some cyclic window ending just before it has positive
weight, read on the walk over the preceding period. -/
private theorem matched_iff {v : Fin n} (hv : v ∈ B) :
    Matched B τ v ↔
      ∃ a, v.val < a ∧ a < v.val + n ∧ walk B τ a < walk B τ (v.val + n) := by
  constructor
  · rintro ⟨h, hh, hwin⟩
    have hhv : h ≠ v := fun e ↦ hh (e ▸ hv)
    set s := (v - h).val with hs_def
    have hs0 : s ≠ 0 := fun h0 ↦ hhv (by
      have : NeZero n := inferInstance
      rw [hs_def, Fin.val_eq_zero_iff, sub_eq_zero] at h0
      exact h0.symm)
    have hne : ∀ t < s, walk B τ (h.val + t + 1) ≠ walk B τ h.val := by
      intro t ht heq
      have htn : t < n := lt_trans ht (v - h).isLt
      have he : (h + pos t - h).val = t := by
        simp [pos, Nat.mod_eq_of_lt htn]
      have := hwin (h + pos t) (by rw [he]; exact ht)
      rw [sum_cyclicIcc, he, heq, sub_self] at this
      exact this rfl
    have hlt := lt_walk_of_ne B τ (by rw [pos_val]; exact hh) hne (s - 1) (by omega)
    -- s is positive, so this endpoint is exactly the start plus s.
    rw [show h.val + (s - 1) + 1 = h.val + s by omega] at hlt
    rcases le_or_gt h v with hle | hlt'
    · have hs : s = v.val - h.val := Fin.coe_sub_iff_le.mpr hle
      have hhv' : h.val < v.val := lt_of_le_of_ne hle (fun e ↦ hhv (Fin.ext e))
      refine ⟨h.val + n, by omega, by omega, ?_⟩
      have := walk_add_self_sub B τ h.val v.val
      -- In the non-wrapping case the cyclic endpoint is v itself.
      rw [show h.val + s = v.val by omega] at hlt
      linarith
    · have hs : s = n + v.val - h.val := Fin.coe_sub_iff_lt.mpr hlt'
      refine ⟨h.val, by omega, by omega, ?_⟩
      -- In the wrapping case the endpoint is v in the following period.
      rw [show h.val + s = v.val + n by omega] at hlt
      exact hlt
  · rintro ⟨a, hva, hai, hwa⟩
    set i := v.val + n
    obtain ⟨a', hva', ha'i, habove⟩ :=
      exists_last_low_point B τ ⟨a, hva, hai, hwa⟩
    refine ⟨pos a', fun hmem ↦ ?_, fun e he ↦ ?_⟩
    · have h₁ := habove (a' + 1) (by omega) (by omega)
      rw [walk_succ, weight_of_mem B τ hmem] at h₁
      omega
    · have hdiff : (v - pos a').val = i - a' :=
        val_sub_pos_of_mem_period hva' ha'i
      rw [hdiff] at he
      have hshift := walk_increment_pos B τ a' ((e - pos a').val + 1)
      simp only [← Nat.add_assoc] at hshift
      rw [sum_cyclicIcc, hshift]
      have := habove (a' + (e - pos a').val + 1) (by omega) (by omega)
      linarith

/-- The running minimum of the walk up to time `k`. -/
private def runMin (k : ℕ) : ℤ := partialSups (α := ℤᵒᵈ) (walk B τ) k

private theorem runMin_le {a k : ℕ} (h : a ≤ k) : runMin B τ k ≤ walk B τ a :=
  le_partialSups_of_le (α := ℤᵒᵈ) (walk B τ) h

private theorem exists_runMin (k : ℕ) : ∃ a ≤ k, walk B τ a = runMin B τ k := by
  obtain ⟨a, ha, he⟩ := exists_partialSups_eq (α := ℤᵒᵈ) (walk B τ) k
  exact ⟨a, ha, he.symm⟩

private theorem runMin_succ (k : ℕ) :
    runMin B τ (k + 1) = min (runMin B τ k) (walk B τ (k + 1)) :=
  partialSups_add_one (α := ℤᵒᵈ) (walk B τ) k

/-- The running minimum drops by at most one per step. -/
private theorem runMin_succ_ge (k : ℕ) : runMin B τ k - 1 ≤ runMin B τ (k + 1) := by
  rw [runMin_succ]
  refine le_min (by omega) ?_
  have h₁ := runMin_le B τ (le_refl k)
  have h₂ := neg_one_le_weight B τ (pos k)
  rw [walk_succ]
  omega

/-- Counting unit drops of the running minimum telescopes over any finite interval. -/
private theorem runMin_drop_count (a len : ℕ) :
    (#{i ∈ Ico a (a + len) | runMin B τ (i + 1) < runMin B τ i} : ℤ) =
      runMin B τ a - runMin B τ (a + len) := by
  rw [card_filter, Nat.cast_sum, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have htel := sum_range_sub' (fun k ↦ runMin B τ (a + k)) len
  simp only [add_zero] at htel
  rw [← htel]
  refine sum_congr rfl fun k _ ↦ ?_
  have h₁ := runMin_succ_ge B τ (a + k)
  have h₂ : runMin B τ (a + k + 1) ≤ runMin B τ (a + k) := by
    rw [runMin_succ]
    exact min_le_left _ _
  simp only [← Nat.add_assoc]
  split_ifs <;> push_cast <;> omega

/-- After a period of negative total weight, the running minimum has dropped by that weight. -/
private theorem runMin_add_self (hT : ∑ i : Fin n, weight B τ i < 0) :
    runMin B τ (n + n) = runMin B τ n + ∑ i : Fin n, weight B τ i := by
  apply le_antisymm
  · obtain ⟨a, ha, he⟩ := exists_runMin B τ n
    rw [← he, ← walk_add_self]
    exact runMin_le B τ (by omega)
  · obtain ⟨a, ha, he⟩ := exists_runMin B τ (n + n)
    rw [← he]
    rcases Nat.lt_or_ge a n with h | h
    · have := runMin_le B τ h.le
      omega
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_comm n b, walk_add_self]
      have hb : b ≤ n := by omega
      have := runMin_le B τ hb
      omega

/-- When the total weight is negative, an unmatched sink at time `i` of the second period is
exactly a step at which the running minimum drops. -/
private theorem unmatched_iff_drop (hT : ∑ i : Fin n, weight B τ i < 0) {i : ℕ} (hni : n ≤ i)
    (hi : i < n + n) :
    (pos i ∈ B ∧ ∀ a, i - n < a → a < i → walk B τ i ≤ walk B τ a) ↔
      runMin B τ (i + 1) < runMin B τ i := by
  constructor
  · rintro ⟨hB, hmin⟩
    have hwi : walk B τ i ≤ runMin B τ i := by
      obtain ⟨a, ha, he⟩ := exists_runMin B τ i
      rw [← he]
      rcases lt_or_eq_of_le ha with ha | rfl
      · rcases Nat.lt_or_ge (i - n) a with h | h
        · exact hmin a h ha
        · have hb : a + n ≤ i := by omega
          have hwalk := walk_add_self B τ a
          rcases lt_or_eq_of_le hb with hb | hb
          · have := hmin (a + n) (by omega) hb
            omega
          · rw [hb] at hwalk
            omega
      · exact le_rfl
    have := runMin_le B τ (le_refl (i + 1))
    rw [walk_succ, weight_of_mem B τ hB] at this
    omega
  · intro hdrop
    rw [runMin_succ] at hdrop
    have hlt : walk B τ (i + 1) < runMin B τ i := by
      by_contra h
      exact absurd hdrop (not_lt.mpr (le_min le_rfl (not_lt.mp h)))
    have hle := runMin_le B τ (le_refl i)
    have hB : pos i ∈ B := mem_of_weight_neg B τ (by rw [walk_succ] at hlt; omega)
    refine ⟨hB, fun a _ ha ↦ ?_⟩
    have := runMin_le B τ ha.le
    rw [walk_succ, weight_of_mem B τ hB] at hlt
    omega

/-- A sink `v` is matched exactly when some cyclic interval `[u, v]` with `u ≠ v` has
nonnegative weight, that is, when the window ending just before `v` has positive weight. -/
theorem matched_iff_exists_nonneg {v : Fin n} (hv : v ∈ B) :
    Matched B τ v ↔ ∃ u, u ≠ v ∧ 0 ≤ ∑ k ∈ cyclicIcc u v, weight B τ k := by
  have hvn : walk B τ (v.val + n + 1) = walk B τ (v.val + n) - 1 := by
    rw [walk_succ, pos_add_self, pos_val, weight_of_mem B τ hv]
    ring_nf
  have hv1 : walk B τ (v.val + 1) = walk B τ v.val - 1 := by
    rw [walk_succ, pos_val, weight_of_mem B τ hv]
    ring_nf
  have hper := walk_add_self B τ v.val
  rw [matched_iff B τ hv]
  constructor
  · rintro ⟨a, hva, hav, hwa⟩
    refine ⟨pos a, fun he ↦ ?_, ?_⟩
    · have hmod : a % n = v.val := by
        have := congrArg Fin.val he
        simpa [pos] using this
      rcases lt_or_ge a n with han | han
      · rw [Nat.mod_eq_of_lt han] at hmod
        omega
      · rw [Nat.mod_eq_sub_mod han, Nat.mod_eq_of_lt (by omega)] at hmod
        omega
    · have hdiff := val_sub_pos_of_mem_period hva hav
      have hshift := walk_increment_pos B τ a ((v - pos a).val + 1)
      simp only [← Nat.add_assoc] at hshift
      -- The period bounds let natural subtraction recover the lifted endpoint.
      rw [sum_cyclicIcc, hshift, hdiff,
        show a + (v.val + n - a) + 1 = v.val + n + 1 by omega, hvn]
      omega
  · rintro ⟨u, huv, hsum⟩
    rw [sum_cyclicIcc] at hsum
    rcases le_or_gt u v with hle | hlt
    · have hlt : u.val < v.val := lt_of_le_of_ne hle (fun e ↦ huv (Fin.ext e))
      -- Non-wrapping subtraction recovers the ordinary successor endpoint.
      rw [Fin.coe_sub_iff_le.mpr hle, show u.val + (v.val - u.val) + 1 = v.val + 1 by omega,
        hv1] at hsum
      refine ⟨u.val + n, by omega, by omega, ?_⟩
      have := walk_add_self B τ u.val
      omega
    · -- Wrapping subtraction recovers the successor endpoint in the next period.
      rw [Fin.coe_sub_iff_lt.mpr hlt, show u.val + (n + v.val - u.val) + 1 = v.val + n + 1 by
        omega, hvn] at hsum
      exact ⟨u.val, by omega, by omega, by omega⟩

end Walk

/-- **Cyclic matching.** The number of matched sinks is the smaller of the number of sinks and
the number of tokens. -/
theorem card_matched : #{v ∈ B | Matched B τ v} = min #B (∑ k ∈ Bᶜ, τ k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Finset.eq_empty_of_isEmpty B]
  have : NeZero n := ⟨hn.ne'⟩
  have hT := sum_weight B τ
  rcases le_or_gt #B (∑ k ∈ Bᶜ, τ k) with hle | hlt
  · -- Enough tokens: every sink is matched.
    rw [min_eq_left hle, filter_true_of_mem]
    intro v hv
    have hcompl : (Bᶜ).Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty.mp hc, sum_empty] at hle
      exact absurd hle (not_le.mpr (card_pos.mpr ⟨v, hv⟩))
    have hn2 : 1 < n := by
      by_contra h
      obtain ⟨k, hk⟩ := hcompl
      exact mem_compl.mp hk (by
        have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
        exact Subsingleton.elim v k ▸ hv)
    refine (matched_iff B τ hv).mpr ⟨v.val + 1, by omega, by omega, ?_⟩
    have h₁ := walk_add_self B τ v.val
    rw [walk_succ, pos_val, weight_of_mem B τ hv]
    omega
  · -- Too few tokens: the unmatched sinks are the record lows of one period.
    rw [min_eq_right hlt.le]
    have hneg : ∑ i : Fin n, weight B τ i < 0 := by omega
    have hun : #{v ∈ B | ¬Matched B τ v} = #{i ∈ Ico n (n + n) |
        runMin B τ (i + 1) < runMin B τ i} := by
      refine card_nbij' (fun v ↦ v.val + n) (fun i ↦ pos i) ?_ ?_ ?_ ?_
      · intro v hv
        simp only [coe_filter, Set.mem_ofPred_eq] at hv ⊢
        obtain ⟨hvB, hvm⟩ := hv
        refine ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
        refine (unmatched_iff_drop B τ hneg (by omega) (by omega)).mp ⟨?_, fun a h₁ h₂ ↦ ?_⟩
        · rw [pos_add_self, pos_val]
          exact hvB
        · by_contra hlt'
          exact hvm ((matched_iff B τ hvB).mpr ⟨a, by omega, h₂, not_le.mp hlt'⟩)
      · intro i hi
        simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hi ⊢
        obtain ⟨⟨hni, hi2⟩, hdrop⟩ := hi
        obtain ⟨hB, hmin⟩ := (unmatched_iff_drop B τ hneg hni hi2).mpr hdrop
        have hval : (pos i : Fin n).val = i - n := by
          simp only [pos, Fin.val_ofNat]
          rw [Nat.mod_eq_sub_mod hni, Nat.mod_eq_of_lt (by omega)]
        refine ⟨hB, fun hm ↦ ?_⟩
        obtain ⟨a, h₁, h₂, h₃⟩ := (matched_iff B τ hB).mp hm
        -- i is in the second period, so restoring the removed period gives i.
        rw [hval, show i - n + n = i by omega] at h₂ h₃
        rw [hval] at h₁
        exact absurd (hmin a h₁ h₂) (not_le.mpr h₃)
      · intro v _
        simp only
        rw [pos_add_self, pos_val]
      · intro i hi
        simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hi
        simp only [pos, Fin.val_ofNat]
        rw [Nat.mod_eq_sub_mod hi.1.1, Nat.mod_eq_of_lt (by omega)]
        omega
    have hdrops := runMin_drop_count B τ n n
    rw [runMin_add_self B τ hneg] at hdrops
    have htot : #{v ∈ B | Matched B τ v} + #{v ∈ B | ¬Matched B τ v} = #B :=
      card_filter_add_card_filter_not _
    rw [hun] at htot
    omega


end Mei.CyclicMatching
