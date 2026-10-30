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
import Mathlib.Tactic.Positivity

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
The double-cycle lemmas `exists_mutual` and its matched variants produce a non-sink and a
sink that see each other under the corresponding token-count hypotheses. The slope comparison
`mul_sum_lt_of_forall_matched` and its reverse bound the two token totals when no such pair
exists. These results support vanishing (V) as well as the total-shadow count.
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

/-- Reindexing a sum over a cyclic interval by negation. -/
theorem sum_cyclicIcc_neg {M : Type*} [AddCommMonoid M] (f : Fin n → M) (a b : Fin n) :
    ∑ k ∈ cyclicIcc (-b) (-a), f k = ∑ k ∈ cyclicIcc a b, f (-k) :=
  sum_nbij' Neg.neg Neg.neg (fun _ hk ↦ neg_mem_cyclicIcc.mpr hk)
    (fun _ hk ↦ neg_mem_cyclicIcc.mpr (by rwa [neg_neg, neg_neg])) (fun k _ ↦ neg_neg k)
    (fun k _ ↦ neg_neg k) (fun k _ ↦ by rw [neg_neg])

/-- Membership in a cyclic interval in terms of positions: for `e ≤ e'` it is the ordinary
interval, and otherwise it wraps around the end. -/
theorem mem_cyclicIcc_iff_le_or_lt {e e' k : Fin n} :
    k ∈ cyclicIcc e e' ↔ e ≤ e' ∧ e ≤ k ∧ k ≤ e' ∨ e' < e ∧ (e ≤ k ∨ k ≤ e') := by
  rw [mem_cyclicIcc]
  rcases le_or_gt e k with hk | hk <;> rcases le_or_gt e e' with he | he
  · rw [Fin.coe_sub_iff_le.mpr hk, Fin.coe_sub_iff_le.mpr he]
    simp only [Fin.le_def, Fin.lt_def] at *
    omega
  · rw [Fin.coe_sub_iff_le.mpr hk, Fin.coe_sub_iff_lt.mpr he]
    simp only [Fin.le_def, Fin.lt_def] at *
    omega
  · rw [Fin.coe_sub_iff_lt.mpr hk, Fin.coe_sub_iff_le.mpr he]
    simp only [Fin.le_def, Fin.lt_def] at *
    omega
  · rw [Fin.coe_sub_iff_lt.mpr hk, Fin.coe_sub_iff_lt.mpr he]
    simp only [Fin.le_def, Fin.lt_def] at *
    omega

/-- A cyclic interval contains the cyclic intervals ending at its right end and starting inside
it. -/
theorem cyclicIcc_subset_of_mem {e e' k : Fin n} (hk : k ∈ cyclicIcc e e') :
    cyclicIcc k e' ⊆ cyclicIcc e e' := by
  intro x hx
  rw [mem_cyclicIcc] at hk hx ⊢
  rw [← val_sub_le_val_sub_iff e x e']
  exact ((val_sub_le_val_sub_iff k x e').mpr hx).trans ((val_sub_le_val_sub_iff e k e').mpr hk)

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

/-- The reflection of the non-sinks, `{k | -k ∉ B}`: the sinks of the reversed cycle. -/
def reflect : Finset (Fin n) := Bᶜ.map (Equiv.neg (Fin n)).toEmbedding

/-- Membership in the reflected non-sinks is non-membership at the negated position. -/
@[simp]
theorem mem_reflect {k : Fin n} : k ∈ reflect B ↔ -k ∉ B := by
  rw [reflect, mem_map_equiv, Equiv.neg_symm, Equiv.neg_apply, mem_compl]

/-- The complement of the reflected non-sinks consists of reflected sinks. -/
@[simp high]
theorem mem_compl_reflect {k : Fin n} : k ∈ (reflect B)ᶜ ↔ -k ∈ B := by
  rw [mem_compl, mem_reflect, not_not]

/-- Taking the complement after reflection gives the reflected sinks. -/
theorem compl_reflect : (reflect B)ᶜ = B.map (Equiv.neg (Fin n)).toEmbedding := by
  ext k
  rw [mem_compl_reflect, mem_map_equiv, Equiv.neg_symm, Equiv.neg_apply]

/-- Summing a reflected function over reflected non-sinks preserves its sum. -/
@[simp]
theorem sum_reflect {M : Type*} [AddCommMonoid M] (ρ : Fin n → M) :
    ∑ k ∈ reflect B, ρ (-k) = ∑ k ∈ Bᶜ, ρ k := by
  rw [reflect, sum_map]
  simp

/-- Summing a reflected function over reflected sinks preserves its sum. -/
@[simp]
theorem sum_compl_reflect {M : Type*} [AddCommMonoid M] (ρ : Fin n → M) :
    ∑ k ∈ (reflect B)ᶜ, ρ (-k) = ∑ k ∈ B, ρ k := by
  rw [compl_reflect, sum_map]
  simp

/-- Reflection preserves the number of non-sinks. -/
@[simp]
theorem card_reflect : #(reflect B) = #Bᶜ := card_map _

/-- The complement of the reflected non-sinks has as many elements as the sinks. -/
@[simp]
theorem card_compl_reflect : #(reflect B)ᶜ = #B := by rw [compl_reflect, card_map]

/-- Windows of the reversed cycle with reflected sinks are reversed windows with non-sinks as
sinks. -/
@[simp]
theorem sum_weight_reflect (ρ : Fin n → ℕ) (x y : Fin n) :
    ∑ k ∈ cyclicIcc x y, weight (reflect B) (ρ ∘ Neg.neg) k =
      ∑ k ∈ cyclicIcc (-y) (-x), weight Bᶜ ρ k := by
  rw [sum_cyclicIcc_neg]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [weight_def, mem_reflect, mem_compl, Function.comp_apply]

@[simp]
theorem sum_weight_compl_reflect (ρ : Fin n → ℕ) (x y : Fin n) :
    ∑ k ∈ cyclicIcc x y, weight (reflect B)ᶜ (ρ ∘ Neg.neg) k =
      ∑ k ∈ cyclicIcc (-y) (-x), weight B ρ k := by
  rw [sum_cyclicIcc_neg]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [weight_def, mem_compl_reflect, Function.comp_apply]

private theorem card_inter_reflect (x y : Fin n) :
    #(cyclicIcc x y ∩ reflect B) = #(cyclicIcc (-y) (-x) ∩ Bᶜ) := by
  simp_rw [← filter_mem_eq_inter, card_filter]
  rw [sum_cyclicIcc_neg]
  simp only [mem_reflect, mem_compl]

private theorem card_inter_compl_reflect (x y : Fin n) :
    #(cyclicIcc x y ∩ (reflect B)ᶜ) = #(cyclicIcc (-y) (-x) ∩ B) := by
  rw [compl_reflect]
  simpa only [reflect, compl_compl] using card_inter_reflect Bᶜ x y

/-- Reflection turns a forward-window offset comparison into a backward-window comparison. -/
private theorem reflect_forward_lt (h v e : Fin n) :
    (e - h).val < (v - h).val ↔ (-h - -e).val < (-h - -v).val := by
  have : NeZero n := ⟨h.pos.ne'⟩
  rw [neg_sub_neg, neg_sub_neg]

/-- A non-sink carrying `τ` tokens that is matched backwards for `(Bᶜ, σ)` becomes a matched
sink of the reversed cycle. -/
private theorem forall_matched_reflect (σ : Fin n → ℕ)
    (hm : ∀ h ∉ B, τ h ≠ 0 → ∃ v ∈ B,
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0) :
    ∀ v' ∈ reflect B, (τ ∘ Neg.neg) v' ≠ 0 → Matched (reflect B) (σ ∘ Neg.neg) v' := by
  intro v' hv' hτv
  have : NeZero n := ⟨v'.pos.ne'⟩
  obtain ⟨v, hv, hall⟩ := hm (-v') ((mem_reflect B).mp hv') hτv
  refine ⟨-v, by rw [mem_reflect, neg_neg, not_not]; exact hv, fun e' he' ↦ ?_⟩
  have := hall (-e') (by simpa only [neg_neg] using (reflect_forward_lt (-v) v' e').mp he')
  rwa [sum_weight_reflect, neg_neg]

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

/-- Several periods change the walk by a multiple of the total weight. -/
private theorem walk_add_mul (k j : ℕ) :
    walk B τ (k + j * n) = walk B τ k + j * ∑ i : Fin n, weight B τ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) * n = k + j * n + n by ring, walk_add_self, ih]
    push_cast
    ring

/-- With nonnegative total weight, the walk never goes below its minimum over one period. -/
private theorem walk_ge_of_nonneg (hA : 0 ≤ ∑ i : Fin n, weight B τ i) {m : ℕ}
    (hm : ∀ y < n, walk B τ m ≤ walk B τ y) (y : ℕ) : walk B τ m ≤ walk B τ y := by
  have hy : y = y % n + y / n * n := by rw [mul_comm]; exact (Nat.mod_add_div y n).symm
  rw [hy, walk_add_mul]
  have := hm (y % n) (Nat.mod_lt _ (NeZero.pos n))
  have : (0 : ℤ) ≤ (y / n : ℕ) * ∑ i : Fin n, weight B τ i := mul_nonneg (by positivity) hA
  linarith

omit [NeZero n] in
private theorem weight_compl (σ : Fin n → ℕ) (k : Fin n) :
    weight Bᶜ σ k = if k ∈ B then (σ k : ℤ) else -1 := by
  by_cases hk : k ∈ B <;> simp [weight, hk]

/-- The offset from `pos y` to `pos (y + t)` is `t`, for `t < n`. -/
private theorem val_pos_add_sub (y t : ℕ) (ht : t < n) : (pos (y + t) - pos y : Fin n).val = t := by
  rw [pos_add, add_sub_cancel_left]
  simp [pos, Nat.mod_eq_of_lt ht]

/-- Every position is reached from `pos y` after its offset. -/
private theorem pos_add_val_sub (y : ℕ) (e : Fin n) : pos (y + (e - pos y).val) = e := by
  rw [pos_add, pos_val, add_sub_cancel]

/-- A cyclic window read from time `y` is an increment of the walk. -/
private theorem sum_cyclicIcc_pos (y t : ℕ) (ht : t < n) :
    ∑ k ∈ cyclicIcc (pos y) (pos (y + t)), weight B τ k = walk B τ (y + t + 1) - walk B τ y := by
  rw [sum_cyclicIcc, val_pos_add_sub y t ht, add_assoc, walk_increment_pos, ← add_assoc]

/-- Recover a position by subtracting its backward offset from a lifted time. -/
private theorem pos_sub_val_sub (y : ℕ) (e : Fin n) (hy : (pos y - e).val ≤ y) :
    pos (y - (pos y - e).val) = e := by
  have hsum : (pos (y - (pos y - e).val) + pos (pos y - e).val : Fin n) = pos y := by
    rw [← pos_add, Nat.sub_add_cancel hy]
  rw [pos_val] at hsum
  exact (eq_sub_of_add_eq hsum).trans (sub_sub_cancel _ _)

/-- From a segment `[s, e]` on which the first walk stays strictly above its start and the
second walk does not decrease, starting at a non-sink, produce a mutually visible pair: the
sink is reached when the second walk first rises above its value after the first step. -/
private theorem mutual_of_segment (σ : Fin n → ℕ) {s e : ℕ} (hse2 : s + 1 < e)
    (hen : e ≤ s + n) (habove : ∀ y, s < y → y < e → walk B τ s < walk B τ y)
    (hβe : walk Bᶜ σ s ≤ walk Bᶜ σ e) (hsB : pos s ∉ B) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  set β := walk Bᶜ σ with hβ
  have hβs1 : β (s + 1) = β s - 1 := by
    rw [hβ, walk_succ, weight_of_mem Bᶜ σ (mem_compl.mpr hsB)]
    ring
  -- The first time after `s + 1` that `β` rises above its value at `s + 1`.
  set G := (Ioc (s + 1) e).filter fun y ↦ β (s + 1) < β y
  have hGne : G.Nonempty := ⟨e, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hse2, le_rfl⟩, by omega⟩⟩
  set y₀ := G.min' hGne
  obtain ⟨hy₀I, hy₀β⟩ := mem_filter.mp (G.min'_mem hGne)
  obtain ⟨hy₀l, hy₀r⟩ := mem_Ioc.mp hy₀I
  set k := y₀ - 1
  have hk1 : k + 1 = y₀ := by omega
  have hbelow : ∀ z, s + 1 ≤ z → z ≤ k → β z < β (k + 1) := by
    intro z hz₁ hz₂
    rw [hk1]
    rcases eq_or_lt_of_le hz₁ with rfl | hz₁
    · exact hy₀β
    · by_contra hle
      have hzG : z ∈ G := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hz₁, by omega⟩, by
        have := not_lt.mp hle; linarith [hy₀β]⟩
      exact absurd (G.min'_le z hzG) (by omega)
  have hkB : pos k ∈ B := by
    have h₁ := hbelow k (by omega) le_rfl
    rw [hβ, walk_succ, weight_compl] at h₁
    by_contra hk
    simp only [hk, ↓reduceIte] at h₁
    omega
  have hkn : k - s < n := by omega
  have hvh : (pos k - pos s : Fin n).val = k - s := by
    simpa only [Nat.add_sub_of_le (show s ≤ k by omega)] using val_pos_add_sub s (k - s) hkn
  refine ⟨pos s, hsB, pos k, hkB, fun e' he' ↦ ?_, fun e' he' ↦ ?_⟩
  · rw [hvh] at he'
    rw [← pos_add_val_sub s e', sum_cyclicIcc_pos B τ s _ (e' - pos s).isLt]
    have h2 := habove (s + (e' - pos s).val + 1) (by omega) (by omega)
    exact sub_ne_zero.mpr (ne_of_gt h2)
  · rw [hvh] at he'
    set u := (pos k - e').val with hu
    have he'k : pos (k - u) = e' := pos_sub_val_sub k e' (by omega)
    have hwin := sum_cyclicIcc_pos Bᶜ σ (k - u) u (by omega)
    rw [show k - u + u = k by omega, he'k] at hwin
    rw [hwin]
    have h2 := hbelow (k - u) (by omega) (by omega)
    exact sub_ne_zero.mpr (ne_of_gt h2)

/-- **Double cycle lemma.** Put `τ` tokens on the non-sinks and `σ` tokens on the sinks `B`.
If there are at least as many `τ` tokens as sinks and at least as many `σ` tokens as non-sinks,
then some non-sink `h` and sink `v` see each other: every window from `h` stopping before `v`
has nonzero weight for `(B, τ)`, and every window ending at `v` and starting after `h` has
nonzero weight for `(Bᶜ, σ)`. -/
theorem exists_mutual (σ : Fin n → ℕ) (hτ : #B ≤ ∑ k ∈ Bᶜ, τ k)
    (hσ : #Bᶜ ≤ ∑ k ∈ B, σ k) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  -- The two walks and their total increments.
  have hA : 0 ≤ ∑ i : Fin n, weight B τ i := by
    rw [sum_weight]
    exact sub_nonneg.mpr (by exact_mod_cast hτ)
  have hAσ : 0 ≤ ∑ i : Fin n, weight Bᶜ σ i := by
    rw [sum_weight, compl_compl]
    exact sub_nonneg.mpr (by exact_mod_cast hσ)
  set α := walk B τ with hα
  set β := walk Bᶜ σ with hβ
  -- A global minimum of `α` and the first position attaining it.
  obtain ⟨m0, hm0, hmin⟩ := (range n).exists_min_image α ⟨0, by simp [NeZero.pos n]⟩
  have hglob : ∀ y, α m0 ≤ α y := walk_ge_of_nonneg B τ hA
    (fun y hy ↦ hmin y (mem_range.mpr hy))
  set Z := (range n).filter fun y ↦ α y = α m0 with hZ
  have hZne : Z.Nonempty := ⟨m0, by simp [Z, hm0]⟩
  set m1 := Z.min' hZne
  have hm1 : m1 ∈ Z := Z.min'_mem hZne
  -- Among the minima, choose one where `β` is smallest.
  obtain ⟨s, hsZ, hsβ⟩ := Z.exists_min_image β hZne
  have hsn : s < n := mem_range.mp (mem_filter.mp hsZ).1
  have hsα : α s = α m0 := (mem_filter.mp hsZ).2
  have hm1s : m1 ≤ s := Z.min'_le s hsZ
  have hm1n : m1 < n := mem_range.mp (mem_filter.mp hm1).1
  have hβper : β (m1 + n) = β m1 + ∑ i : Fin n, weight Bᶜ σ i := walk_add_self Bᶜ σ m1
  -- The next return of `α` to its minimum, or one period after `m1`.
  set F := (Ioc s (m1 + n)).filter fun y ↦ α y ≤ α m0
  set e := if hF : F.Nonempty then F.min' hF else m1 + n with he_def
  have hse : s < e ∧ e ≤ m1 + n := by
    by_cases hF : F.Nonempty
    · have := mem_Ioc.mp (mem_filter.mp (F.min'_mem hF)).1
      rw [he_def, dite_eq_left hF]
      exact this
    · rw [he_def, dite_eq_right hF]
      omega
  have habove : ∀ y, s < y → y < e → α m0 < α y := by
    intro y h₁ h₂
    by_contra hle
    have hyF : y ∈ F := mem_filter.mpr ⟨mem_Ioc.mpr ⟨h₁, by omega⟩, not_lt.mp hle⟩
    have hF : F.Nonempty := ⟨y, hyF⟩
    have : e ≤ y := by rw [he_def, dite_eq_left hF]; exact F.min'_le y hyF
    omega
  have hβe : β s ≤ β e := by
    by_cases hF : F.Nonempty
    · have heF := F.min'_mem hF
      have hee : e = F.min' hF := by rw [he_def, dite_eq_left hF]
      rw [← hee] at heF
      obtain ⟨heI, heα⟩ := mem_filter.mp heF
      have heα' : α e = α m0 := le_antisymm heα (hglob e)
      rcases lt_or_ge e n with hen | hen
      · exact hsβ e (mem_filter.mpr ⟨mem_range.mpr hen, heα'⟩)
      · set r := e - n with hr_def
        have her : e = r + n := by omega
        have hper : α (r + n) = α r + ∑ i : Fin n, weight B τ i := walk_add_self B τ r
        rw [her] at heα' heI ⊢
        have hrα : α r = α m0 := le_antisymm (by linarith [hglob r]) (hglob r)
        have hrZ : r ∈ Z := mem_filter.mpr ⟨mem_range.mpr (by omega), hrα⟩
        have hr : r = m1 := le_antisymm (by have := (mem_Ioc.mp heI).2; omega) (Z.min'_le r hrZ)
        rw [hr, hβper]
        linarith [hsβ m1 hm1]
    · have hee : e = m1 + n := by rw [he_def, dite_eq_right hF]
      rw [hee, hβper]
      linarith [hsβ m1 hm1]
  -- The first step from `s` is a non-sink carrying tokens.
  have hsB : pos s ∉ B := by
    intro hmem
    have := hglob (s + 1)
    rw [hα, walk_succ, weight_of_mem B τ hmem, ← hα, hsα] at this
    omega
  have hβs1 : β (s + 1) = β s - 1 := by
    rw [hβ, walk_succ, weight_of_mem Bᶜ σ (mem_compl.mpr hsB)]
    ring
  have hse2 : s + 1 < e := by
    by_contra h
    have : e = s + 1 := by omega
    rw [this, hβs1] at hβe
    omega
  exact mutual_of_segment B τ σ hse2 (by omega)
    (fun y h₁ h₂ ↦ by have := habove y h₁ h₂; rw [← hsα] at this; exact this) hβe hsB

/-- A time at which the first walk is at its running minimum. -/
private def IsBase (y : ℕ) : Prop := ∀ x ≤ y, walk B τ y ≤ walk B τ x

/-- A sink stepped from a running minimum after the first period is unmatched, so it carries
no `σ` tokens when every token-carrying sink is matched. -/
private theorem sigma_eq_zero_of_isBase (σ : Fin n → ℕ)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) {y : ℕ} (hy : n ≤ y) (hb : IsBase B τ y)
    (hyB : pos y ∈ B) : σ (pos y) = 0 := by
  by_contra hσ
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := (matched_iff B τ hyB).mp (hm _ hyB hσ)
  have hval : (pos y : Fin n).val = y % n := by simp [pos]
  rw [hval] at ha₁ ha₂ ha₃
  have hy' : y = y % n + n + (y / n - 1) * n := by
    have h₁ := Nat.mod_add_div y n
    have h₂ : 1 ≤ y / n := (Nat.le_div_iff_mul_le (NeZero.pos n)).mpr (by omega)
    rw [Nat.mul_comm] at h₁
    calc y = y % n + y / n * n := h₁.symm
      _ = _ := by
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h₂
        rw [ht, add_comm 1 t, Nat.add_sub_cancel, add_mul, one_mul]
        ring
  have h₁ := walk_add_mul B τ a (y / n - 1)
  have h₂ := walk_add_mul B τ (y % n + n) (y / n - 1)
  rw [← hy'] at h₂
  have := hb (a + (y / n - 1) * n) (by omega)
  linarith

/-- A running minimum followed by a sink step is again a running minimum. -/
private theorem isBase_succ {y : ℕ} (hb : IsBase B τ y) (hyB : pos y ∈ B) :
    IsBase B τ (y + 1) := by
  intro x hx
  rw [walk_succ, weight_of_mem B τ hyB]
  rcases Nat.lt_or_ge x (y + 1) with h | h
  · have := hb x (by omega)
    linarith
  · rw [show x = y + 1 by omega, walk_succ, weight_of_mem B τ hyB]

/-- A run of sink steps preserves the running-minimum property. -/
private theorem isBase_add_of_sinks {c : ℕ} (hb : IsBase B τ c) :
    ∀ d, (∀ j, c ≤ j → j < c + d → pos j ∈ B) → IsBase B τ (c + d) := by
  intro d
  induction d with
  | zero => intro; simpa using hb
  | succ d ih =>
    intro hsink
    rw [← add_assoc]
    exact isBase_succ B τ (ih fun j h₁ h₂ ↦ hsink j h₁ (by omega))
      (hsink _ (by omega) (by omega))

/-- From a running minimum, a stretch of unmatched sinks does not move the second walk. -/
private theorem walk_compl_eq_of_sinks (σ : Fin n → ℕ)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) {c : ℕ} (hc : n ≤ c) (hb : IsBase B τ c) :
    ∀ d, (∀ j, c ≤ j → j < c + d → pos j ∈ B) → walk Bᶜ σ (c + d) = walk Bᶜ σ c := by
  intro d
  induction d with
  | zero => intro; rfl
  | succ d ih =>
    intro hsink
    have hbase := isBase_add_of_sinks B τ hb d (fun j h₁ h₂ ↦ hsink j h₁ (by omega))
    have hB := hsink (c + d) (by omega) (by omega)
    rw [← add_assoc, walk_succ, ih fun j h₁ h₂ ↦ hsink j h₁ (by omega),
      weight_of_notMem Bᶜ σ (notMem_compl.mpr hB),
      sigma_eq_zero_of_isBase B τ σ hm (by omega) hbase hB]
    simp

/-- The first return of the first walk to the level of a running minimum `a`, before a later
running minimum `b`, is again a running minimum. -/
private theorem exists_first_return {a b : ℕ} (hab : a < b) (hba : IsBase B τ a)
    (hbb : IsBase B τ b) :
    ∃ c, a < c ∧ c ≤ b ∧ walk B τ c ≤ walk B τ a ∧
      (∀ y, a < y → y < c → walk B τ a < walk B τ y) ∧ IsBase B τ c := by
  set F := (Ioc a b).filter fun y ↦ walk B τ y ≤ walk B τ a
  have hF : F.Nonempty := ⟨b, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hab, le_rfl⟩, hbb a hab.le⟩⟩
  obtain ⟨c, hcF, hcmin⟩ : ∃ c ∈ F, ∀ y ∈ F, c ≤ y :=
    ⟨F.min' hF, F.min'_mem hF, fun y hy ↦ F.min'_le y hy⟩
  obtain ⟨hcI, hcα⟩ := mem_filter.mp hcF
  obtain ⟨hac, hcb⟩ := mem_Ioc.mp hcI
  have hbetween : ∀ y, a < y → y < c → walk B τ a < walk B τ y := by
    intro y h₁ h₂
    by_contra hle
    have hyF : y ∈ F := mem_filter.mpr ⟨mem_Ioc.mpr ⟨h₁, by omega⟩, not_lt.mp hle⟩
    exact absurd (hcmin y hyF) (by omega)
  refine ⟨c, hac, hcb, hcα, hbetween, fun x hx ↦ ?_⟩
  rcases Nat.lt_or_ge a x with h | h
  · rcases lt_or_eq_of_le hx with h' | rfl
    · have := hbetween x h h'; linarith
    · exact le_rfl
  · exact le_trans hcα (hba x h)

/-- When the total weight is negative, some time in the second period and the same time one
period later are running minima. -/
private theorem exists_base_period (hA : ∑ i : Fin n, weight B τ i < 0) :
    ∃ a, n ≤ a ∧ IsBase B τ a ∧ IsBase B τ (a + n) := by
  obtain ⟨a, haI, hamin⟩ := (Icc n (n + n)).exists_min_image (walk B τ)
    ⟨n, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨ha₁, ha₂⟩ := mem_Icc.mp haI
  have hper (x : ℕ) := walk_add_self B τ x
  have hba : IsBase B τ a := by
    intro x hx
    rcases Nat.lt_or_ge x n with h | h
    · have := hamin (x + n) (mem_Icc.mpr ⟨by omega, by omega⟩)
      linarith [hper x]
    · exact hamin x (mem_Icc.mpr ⟨h, by omega⟩)
  refine ⟨a, ha₁, hba, fun x hx ↦ ?_⟩
  rcases Nat.lt_or_ge a x with h | h
  · obtain ⟨t, rfl⟩ : ∃ t, x = t + n := ⟨x - n, by omega⟩
    have := hba t (by omega)
    linarith [hper t, hper a]
  · have := hba x h
    linarith [hper a]

/-- Between two running minima across which the second walk does not decrease and which
contain a non-sink, there is an excursion of the first walk over which the second walk does not
decrease. -/
private theorem exists_segment (σ : Fin n → ℕ) (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) :
    ∀ d a b, b - a = d → n ≤ a → a ≤ b → IsBase B τ a → IsBase B τ b →
      walk Bᶜ σ a ≤ walk Bᶜ σ b → (∃ j, a ≤ j ∧ j < b ∧ pos j ∉ B) →
      ∃ s e, a ≤ s ∧ e ≤ b ∧ s + 1 < e ∧
        (∀ y, s < y → y < e → walk B τ s < walk B τ y) ∧ walk Bᶜ σ s ≤ walk Bᶜ σ e ∧
        pos s ∉ B := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro a b hd ha hab hba hbb hβ ⟨j, hj₁, hj₂, hjB⟩
  -- The next return of the first walk to the level at `a`.
  obtain ⟨c, hac, hcb, hcα, hbetween, hcb'⟩ :=
    exists_first_return B τ (show a < b by omega) hba hbb
  -- If `[c, b)` had no non-sink, the second walk would not move there.
  have hHc : walk Bᶜ σ c < walk Bᶜ σ b → ∃ j, c ≤ j ∧ j < b ∧ pos j ∉ B := by
    intro hlt
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    have := walk_compl_eq_of_sinks B τ σ hm (by omega) hcb' (b - c)
      (fun j h₁ h₂ ↦ hno j h₁ (by omega))
    rw [show c + (b - c) = b by omega] at this
    omega
  have hrec : walk Bᶜ σ c < walk Bᶜ σ a → ∃ s e, a ≤ s ∧ e ≤ b ∧ s + 1 < e ∧
      (∀ y, s < y → y < e → walk B τ s < walk B τ y) ∧ walk Bᶜ σ s ≤ walk Bᶜ σ e ∧
      pos s ∉ B := by
    intro hlt
    have hd' : b - c < d := hd ▸ Nat.sub_lt_sub_left (hac.trans_le hcb) hac
    have hnc : n ≤ c := ha.trans hac.le
    obtain ⟨s, e, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih (b - c) hd' c b rfl hnc hcb hcb' hbb
      (hlt.le.trans hβ) (hHc (hlt.trans_le hβ))
    exact ⟨s, e, hac.le.trans h₁, h₂, h₃, h₄, h₅, h₆⟩
  by_cases haB : pos a ∈ B
  · -- A sink step: an unmatched sink, so the second walk stays put.
    have hc1 : c = a + 1 := by
      by_contra hne
      have := hbetween (a + 1) (by omega) (by omega)
      rw [walk_succ, weight_of_mem B τ haB] at this
      omega
    have hβc : walk Bᶜ σ c = walk Bᶜ σ a := by
      rw [hc1, walk_succ, weight_of_notMem Bᶜ σ (notMem_compl.mpr haB),
        sigma_eq_zero_of_isBase B τ σ hm ha hba haB]
      simp
    have hjc : c ≤ j := by
      rcases eq_or_lt_of_le hj₁ with rfl | h
      · exact absurd haB hjB
      · omega
    have hlt : b - c < d := hd ▸ Nat.sub_lt_sub_left (hac.trans_le hcb) hac
    have hnc : n ≤ c := ha.trans hac.le
    obtain ⟨s, e, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih (b - c) hlt c b rfl hnc hcb hcb' hbb
      (hβc ▸ hβ) ⟨j, hjc, hj₂, hjB⟩
    exact ⟨s, e, hac.le.trans h₁, h₂, h₃, h₄, h₅, h₆⟩
  · have hβa1 : walk Bᶜ σ (a + 1) = walk Bᶜ σ a - 1 := by
      rw [walk_succ, weight_of_mem Bᶜ σ (mem_compl.mpr haB)]
      ring
    by_cases hτa : τ (pos a) = 0
    · -- A non-sink without tokens: the second walk drops.
      have hc1 : c = a + 1 := by
        by_contra hne
        have := hbetween (a + 1) (by omega) (by omega)
        rw [walk_succ, weight_of_notMem B τ haB, hτa] at this
        simp at this
      exact hrec (by rw [hc1, hβa1]; omega)
    · -- An excursion of the first walk.
      have hca : a + 1 < c := by
        by_contra h
        have hc1 : c = a + 1 := by omega
        rw [hc1, walk_succ, weight_of_notMem B τ haB] at hcα
        have : (0 : ℤ) < τ (pos a) := by exact_mod_cast Nat.pos_of_ne_zero hτa
        linarith
      rcases le_or_gt (walk Bᶜ σ a) (walk Bᶜ σ c) with hle | hlt
      · exact ⟨a, c, le_rfl, hcb, hca, hbetween, hle, haB⟩
      · exact hrec hlt

omit [NeZero n] in
/-- **Double cycle lemma, matched form.** If every sink carrying `σ` tokens is matched for
`(B, τ)`, there is a non-sink, and there are at least as many `σ` tokens as non-sinks, then some
non-sink `h` and sink `v` see each other as in `exists_mutual`. -/
theorem exists_mutual_of_forall_matched (σ : Fin n → ℕ) (hBc : Bᶜ.Nonempty)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) (hσ : #Bᶜ ≤ ∑ k ∈ B, σ k) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  have : NeZero n := ⟨hBc.choose.pos.ne'⟩
  by_cases hτ : #B ≤ ∑ k ∈ Bᶜ, τ k
  · exact exists_mutual B τ σ hτ hσ
  have hA : ∑ i : Fin n, weight B τ i < 0 := by
    rw [sum_weight]; exact sub_neg.mpr (by exact_mod_cast not_le.mp hτ)
  have hAσ : 0 ≤ ∑ i : Fin n, weight Bᶜ σ i := by
    rw [sum_weight, compl_compl]; exact sub_nonneg.mpr (by exact_mod_cast hσ)
  -- A running minimum `a` in the second period, and the same point one period later.
  obtain ⟨a, ha₁, hba, hbb⟩ := exists_base_period B τ hA
  have hβ : walk Bᶜ σ a ≤ walk Bᶜ σ (a + n) := by
    linarith [walk_add_self Bᶜ σ a]
  obtain ⟨k, hk⟩ := hBc
  have hj : ∃ j, a ≤ j ∧ j < a + n ∧ pos j ∉ B := by
    refine ⟨a + (k - pos a).val, by omega, by have := (k - pos a).isLt; omega, ?_⟩
    rw [pos_add_val_sub]
    exact mem_compl.mp hk
  obtain ⟨s, e, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_segment B τ σ hm n a (a + n) (by omega) ha₁
    (by omega) hba hbb hβ hj
  exact mutual_of_segment B τ σ h₃ (by omega) h₄ h₅ h₆

omit [NeZero n] in
/-- **Double cycle lemma, reversed matched form.** If every non-sink carrying `τ` tokens is
matched backwards for `(Bᶜ, σ)`, there is a sink, and there are at least as many `τ` tokens as
sinks, then some non-sink `h` and sink `v` see each other as in `exists_mutual`. -/
theorem exists_mutual_of_forall_matched_rev (σ : Fin n → ℕ) (hB : B.Nonempty)
    (hm : ∀ h ∉ B, τ h ≠ 0 → ∃ v ∈ B,
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0)
    (hτ : #B ≤ ∑ k ∈ Bᶜ, τ k) :
    ∃ h ∉ B, ∃ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0 := by
  have : NeZero n := ⟨hB.choose.pos.ne'⟩
  -- Reflect the cycle: the reflected non-sinks are the sinks, with the roles of `τ` and `σ`
  -- exchanged.
  obtain ⟨h', hh', v', hv', hfwd, hbwd⟩ := exists_mutual_of_forall_matched (reflect B)
    (σ ∘ Neg.neg) (τ ∘ Neg.neg) (by
      obtain ⟨k, hk⟩ := hB
      exact ⟨-k, by rw [mem_compl_reflect, neg_neg]; exact hk⟩)
    (forall_matched_reflect B τ σ hm) (by
      simpa only [card_compl_reflect, Function.comp_apply, sum_reflect] using hτ)
  rw [mem_reflect, not_not] at hh'
  refine ⟨-v', (mem_reflect B).mp hv', -h', hh', fun e he ↦ ?_, fun e he ↦ ?_⟩
  · have := hbwd (-e) (by simpa only [neg_neg] using (reflect_forward_lt (-v') (-h') e).mp he)
    rwa [sum_weight_compl_reflect, neg_neg] at this
  · have := hfwd (-e) (by
      apply (reflect_forward_lt h' v' (-e)).mpr
      simpa only [neg_neg] using he)
    rwa [sum_weight_reflect, neg_neg] at this

/-- The `τ` tokens on the non-sinks between times `x` and `y` of the periodic extension. -/
private def tokens (x y : ℕ) : ℤ := (walk B τ y - walk B τ x) - (walk B 0 y - walk B 0 x)

private theorem tokens_add (x y z : ℕ) : tokens B τ x y + tokens B τ y z = tokens B τ x z := by
  unfold tokens
  ring

private theorem tokens_self (x : ℕ) : tokens B τ x x = 0 := by
  unfold tokens
  ring

private theorem tokens_succ (x : ℕ) :
    tokens B τ x (x + 1) = if pos x ∈ B then 0 else (τ (pos x) : ℤ) := by
  unfold tokens
  rw [walk_succ, walk_succ]
  by_cases h : pos x ∈ B
  · simp [h]
  · simp [h]

private theorem tokens_add_self (x : ℕ) : tokens B τ x (x + n) = ∑ k ∈ Bᶜ, τ k := by
  unfold tokens
  rw [walk_add_self, walk_add_self, sum_weight, sum_weight]
  simp only [Pi.zero_apply, sum_const_zero, Nat.cast_zero]
  ring

/-- The second walk cannot rise above the end of an excursion before its first step. -/
private theorem walk_compl_le_first_of_excursion (σ : Fin n → ℕ)
    (hcomp : ∀ h ∉ B, ∀ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) →
      ∃ e, (v - e).val < (v - h).val ∧ ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k = 0)
    {a c : ℕ} (hcn : c ≤ a + n) (haB : pos a ∉ B)
    (habove : ∀ y, a < y → y < c → walk B τ a < walk B τ y) :
    ∀ x, a < x → x ≤ c → walk Bᶜ σ c ≤ walk Bᶜ σ x →
      walk Bᶜ σ c ≤ walk Bᶜ σ (a + 1) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro hax hxc hXx
  rcases eq_or_lt_of_le (show a + 1 ≤ x by omega) with rfl | hx
  · exact hXx
  by_cases hle : walk Bᶜ σ c ≤ walk Bᶜ σ (x - 1)
  · exact ih (x - 1) (by omega) (by omega) (by omega) hle
  have hstepX : walk Bᶜ σ x = walk Bᶜ σ (x - 1) + weight Bᶜ σ (pos (x - 1)) := by
    rw [← walk_succ, show x - 1 + 1 = x by omega]
  have hvB : pos (x - 1) ∈ B := by
    by_contra hnot
    rw [weight_of_mem Bᶜ σ (mem_compl.mpr hnot)] at hstepX
    linarith [not_le.mp hle]
  rw [weight_of_notMem Bᶜ σ (notMem_compl.mpr hvB)] at hstepX
  have hvh : (pos (x - 1) - pos a : Fin n).val = x - 1 - a := by
    have := val_pos_add_sub (n := n) a (x - 1 - a) (by omega)
    rwa [show a + (x - 1 - a) = x - 1 by omega] at this
  obtain ⟨e, he, hsum⟩ := hcomp (pos a) haB (pos (x - 1)) hvB fun e he ↦ by
    rw [hvh] at he
    rw [← pos_add_val_sub a e, sum_cyclicIcc_pos B τ a _ (e - pos a).isLt]
    have := habove (a + (e - pos a).val + 1) (by omega) (by omega)
    exact sub_ne_zero.mpr (ne_of_gt this)
  rw [hvh] at he
  set u := (pos (x - 1) - e).val with hu
  have hpu : pos u = pos (x - 1) - e := pos_val _
  have hey : pos (x - 1 - u) = e := pos_sub_val_sub (x - 1) e (by omega)
  have hwin := sum_cyclicIcc_pos Bᶜ σ (x - 1 - u) u (by omega)
  rw [show x - 1 - u + u = x - 1 by omega, hey, hsum, show x - 1 + 1 = x by omega] at hwin
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, Nat.sub_zero] at hwin
    have : (0 : ℤ) < σ (pos (x - 1)) := by linarith [not_le.mp hle]
    linarith
  exact ih (x - 1 - u) (by omega) (by omega) (by omega) (by linarith)

/-- Counts in a lifted window are differences of the zero-token walk. -/
private theorem card_window_eq_neg_walk_zero_sub (a t : ℕ) (ht : t < n) :
    (#(cyclicIcc (pos a) (pos (a + t)) ∩ B) : ℤ) =
      -(walk B 0 (a + t + 1) - walk B 0 a) := by
  have h := sum_cyclicIcc_pos B 0 a t ht
  rw [sum_weight_eq] at h
  simp only [Pi.zero_apply, sum_const_zero, Nat.cast_zero, zero_sub] at h
  linarith

/-- On an excursion of the first walk from a non-sink `a` back to its level at `c`, if no
non-sink and sink see each other, then the `σ` tokens are fewer than the non-sinks, and a slope
bound on windows gives `α σ < β τ` there. -/
private theorem excursion_lt (σ : Fin n → ℕ) (α β : ℕ)
    (hchr : ∀ h ∉ B, ∀ e ∈ B, α * #(cyclicIcc h e ∩ Bᶜ) < α + β * #(cyclicIcc h e ∩ B))
    (hcomp : ∀ h ∉ B, ∀ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) →
      ∃ e, (v - e).val < (v - h).val ∧ ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k = 0)
    {a c : ℕ} (hac : a + 1 < c) (hcn : c ≤ a + n) (haB : pos a ∉ B)
    (habove : ∀ y, a < y → y < c → walk B τ a < walk B τ y) (hc : walk B τ c ≤ walk B τ a) :
    (α : ℤ) * tokens Bᶜ σ a c < β * tokens B τ a c := by
  -- The last step returns the first walk to its starting level, at a sink.
  have hc1 := habove (c - 1) (by omega) (by omega)
  have hstep : walk B τ c = walk B τ (c - 1) + weight B τ (pos (c - 1)) := by
    rw [← walk_succ, show c - 1 + 1 = c by omega]
  have hcB : pos (c - 1) ∈ B := by
    by_contra hnot
    have := weight_nonneg B τ hnot
    linarith
  have hceq : walk B τ c = walk B τ a := by
    have := neg_one_le_weight B τ (pos (c - 1))
    omega
  -- Going back from `c`, the second walk never ends above its value at `c` before `a + 1`.
  have hXc := walk_compl_le_first_of_excursion B τ σ hcomp hcn haB habove c
    (by omega) le_rfl le_rfl
  have hXa : walk Bᶜ σ (a + 1) = walk Bᶜ σ a - 1 := by
    rw [walk_succ, weight_of_mem Bᶜ σ (mem_compl.mpr haB)]
    ring
  -- The counts of sinks and non-sinks on the window from `a` to `c - 1`.
  have ht : c - 1 - a < n := by omega
  have hpc : (pos (a + (c - 1 - a)) : Fin n) = pos (c - 1) := by
    rw [show a + (c - 1 - a) = c - 1 by omega]
  have hV := card_window_eq_neg_walk_zero_sub B a (c - 1 - a) ht
  have hH := card_window_eq_neg_walk_zero_sub Bᶜ a (c - 1 - a) ht
  rw [hpc, show a + (c - 1 - a) + 1 = c by omega] at hV hH
  have hchrZ : (α : ℤ) * #(cyclicIcc (pos a) (pos (c - 1)) ∩ Bᶜ) <
      α + β * #(cyclicIcc (pos a) (pos (c - 1)) ∩ B) := by
    exact_mod_cast hchr (pos a) haB (pos (c - 1)) hcB
  have hP : tokens Bᶜ σ a c ≤ #(cyclicIcc (pos a) (pos (c - 1)) ∩ Bᶜ) - 1 := by
    unfold tokens
    linarith
  have hQ : tokens B τ a c = #(cyclicIcc (pos a) (pos (c - 1)) ∩ B) := by
    unfold tokens
    linarith
  have := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg (α : ℕ) : (0 : ℤ) ≤ α)
  rw [hQ]
  linarith

/-- Between running minima `a ≤ b` at most a period apart, the comparison of `excursion_lt`
holds for the tokens, strictly when there are `τ` tokens. -/
private theorem segment_le (σ : Fin n → ℕ) (α β : ℕ)
    (hchr : ∀ h ∉ B, ∀ e ∈ B, α * #(cyclicIcc h e ∩ Bᶜ) < α + β * #(cyclicIcc h e ∩ B))
    (hcomp : ∀ h ∉ B, ∀ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) →
      ∃ e, (v - e).val < (v - h).val ∧ ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k = 0)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) :
    ∀ d a b, b - a = d → n ≤ a → a ≤ b → b ≤ a + n → IsBase B τ a → IsBase B τ b →
      (α : ℤ) * tokens Bᶜ σ a b ≤ β * tokens B τ a b ∧
        (0 < tokens B τ a b → (α : ℤ) * tokens Bᶜ σ a b < β * tokens B τ a b) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro a b hd ha hab hbn hba hbb
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp [tokens_self]
  obtain ⟨c, hac, hcb, hcα, hbetween, hcb'⟩ := exists_first_return B τ hab hba hbb
  have hd' : b - c < d := hd ▸ Nat.sub_lt_sub_left hab hac
  obtain ⟨ih₁, ih₂⟩ := ih (b - c) hd' c b rfl (ha.trans hac.le) hcb (by omega) hcb' hbb
  rw [← tokens_add Bᶜ σ a c b, ← tokens_add B τ a c b]
  by_cases hca : a + 1 < c
  · have haB : pos a ∉ B := by
      intro haB
      have := hbetween (a + 1) (by omega) hca
      rw [walk_succ, weight_of_mem B τ haB] at this
      omega
    have hlt := excursion_lt B τ σ α β hchr hcomp hca (by omega) haB hbetween hcα
    exact ⟨by linarith, fun _ ↦ by linarith⟩
  · have hc1 : c = a + 1 := by omega
    subst hc1
    have h0 : tokens Bᶜ σ a (a + 1) = 0 ∧ tokens B τ a (a + 1) = 0 := by
      rw [tokens_succ, tokens_succ]
      by_cases haB : pos a ∈ B
      · simp [haB, sigma_eq_zero_of_isBase B τ σ hm ha hba haB]
      · rw [walk_succ, weight_of_notMem B τ haB] at hcα
        simp only [mem_compl, haB, not_false_eq_true, ↓reduceIte, true_and, Nat.cast_eq_zero]
        omega
    rw [h0.1, h0.2, zero_add, zero_add]
    exact ⟨ih₁, ih₂⟩

omit [NeZero n] in
/-- **Slope comparison.** Suppose every window from a non-sink to a sink satisfies
`α · #non-sinks < α + β · #sinks`, no non-sink `h` and sink `v` see each other as in
`exists_mutual`, every sink carrying `σ` tokens is matched for `(B, τ)`, and there are fewer
`τ` tokens than sinks but at least one. Then `α ∑_B σ < β ∑_{Bᶜ} τ`. -/
theorem mul_sum_lt_of_forall_matched (σ : Fin n → ℕ) (α β : ℕ)
    (hchr : ∀ h ∉ B, ∀ e ∈ B, α * #(cyclicIcc h e ∩ Bᶜ) < α + β * #(cyclicIcc h e ∩ B))
    (hcomp : ∀ h ∉ B, ∀ v ∈ B,
      (∀ e, (e - h).val < (v - h).val → ∑ k ∈ cyclicIcc h e, weight B τ k ≠ 0) →
      ∃ e, (v - e).val < (v - h).val ∧ ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k = 0)
    (hm : ∀ v ∈ B, σ v ≠ 0 → Matched B τ v) (hτ : ∑ k ∈ Bᶜ, τ k < #B)
    (hτ0 : ∑ k ∈ Bᶜ, τ k ≠ 0) :
    α * ∑ k ∈ B, σ k < β * ∑ k ∈ Bᶜ, τ k := by
  have : NeZero n := ⟨(card_pos.mp (by omega : 0 < #B)).choose.pos.ne'⟩
  have hA : ∑ i : Fin n, weight B τ i < 0 := by
    rw [sum_weight]; exact sub_neg.mpr (by exact_mod_cast hτ)
  obtain ⟨a, ha, hba, hbb⟩ := exists_base_period B τ hA
  obtain ⟨-, h⟩ := segment_le B τ σ α β hchr hcomp hm n a (a + n) (by omega) ha (by omega)
    le_rfl hba hbb
  rw [tokens_add_self, tokens_add_self, compl_compl] at h
  exact_mod_cast h (by exact_mod_cast Nat.pos_of_ne_zero hτ0)

omit [NeZero n] in
/-- **Slope comparison, reversed.** The reflection of `mul_sum_lt_of_forall_matched`: the
windows are read backwards from sinks, and every non-sink carrying `τ` tokens is matched
backwards for `(Bᶜ, σ)`. -/
theorem mul_sum_lt_of_forall_matched_rev (σ : Fin n → ℕ) (α β : ℕ)
    (hchr : ∀ h ∉ B, ∀ v ∈ B, α * #(cyclicIcc h v ∩ B) < α + β * #(cyclicIcc h v ∩ Bᶜ))
    (hcomp : ∀ h ∉ B, ∀ v ∈ B,
      (∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0) →
      ∃ e, (e - h).val < (v - h).val ∧ ∑ k ∈ cyclicIcc h e, weight B τ k = 0)
    (hm : ∀ h ∉ B, τ h ≠ 0 → ∃ v ∈ B,
      ∀ e, (v - e).val < (v - h).val → ∑ k ∈ cyclicIcc e v, weight Bᶜ σ k ≠ 0)
    (hσ : ∑ k ∈ B, σ k < #Bᶜ) (hσ0 : ∑ k ∈ B, σ k ≠ 0) :
    α * ∑ k ∈ Bᶜ, τ k < β * ∑ k ∈ B, σ k := by
  have : NeZero n := ⟨(card_pos.mp (by omega : 0 < #Bᶜ)).choose.pos.ne'⟩
  have h := mul_sum_lt_of_forall_matched (reflect B) (σ ∘ Neg.neg) (τ ∘ Neg.neg) α β
    (fun h' hh' e' he' ↦ by
      rw [card_inter_compl_reflect, card_inter_reflect]
      exact hchr (-e') ((mem_reflect B).mp he') (-h')
        ((mem_compl_reflect B).mp (mem_compl.mpr hh')))
    (fun h' hh' v' hv' hfwd ↦ by
      rw [mem_reflect, not_not] at hh'
      obtain ⟨e, he, hsum⟩ := hcomp (-v') ((mem_reflect B).mp hv') (-h') hh' fun e he ↦ by
        have := hfwd (-e) (by
          apply (reflect_forward_lt h' v' (-e)).mpr
          simpa only [neg_neg] using he)
        rwa [sum_weight_reflect, neg_neg] at this
      refine ⟨-e, by simpa only [neg_neg] using (reflect_forward_lt (-v') (-h') e).mp he, ?_⟩
      rw [sum_weight_compl_reflect, neg_neg]
      exact hsum)
    (forall_matched_reflect B τ σ hm) (by
      simpa only [card_reflect, Function.comp_apply, sum_compl_reflect] using hσ)
    (by simpa only [Function.comp_apply, sum_compl_reflect] using hσ0)
  simpa only [Function.comp_apply, sum_reflect, sum_compl_reflect] using h

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
