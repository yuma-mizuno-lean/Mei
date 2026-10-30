/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Tactic.Abel

/-!
# Ordering finite products by exchanges of adjacent factors

Let `e : F → G` evaluate factors in a monoid, let `deg : F → ℕ` be a degree, and let
`bad x y` mark an adjacent pair `x y` as being in the wrong order. Suppose that factors of
degree above a cutoff `k` evaluate to `1`, that `bad` is asymmetric, and that every bad
pair of degree at most `k` can be exchanged at the cost of inserting factors of strictly
larger degree:
`e x * e y = e y * (M.map e).prod * e x` with `deg x, deg y < deg m` for `m ∈ M`.
Then `List.exists_isChain_prod_map_eq_of_exchange` rewrites every finite product to one
with no bad adjacent pair, using only factors of degree at most `k`.

Repeated exchanges terminate. Call a bad pair `(a, b)` of a list, with `a` before `b`,
an inversion, and weight it by `k + 1 - max (deg a) (deg b)`. An exchange removes the
inversion `(x, y)`. The new inversions all involve an inserted factor, so they have strictly
smaller weight. Thus the multiset of weights decreases in the Dershowitz–Manna order
(`Multiset.wellFounded_isDershowitzMannaLT`), although the list may grow. Factors of degree
above `k` are deleted first, using `List.prod_map_filter_of_ne`.

This proves the termination of Nakanishi's Ordering Algorithm for products of dilogarithm
elements, in which the pentagon relation exchanges an anti-ordered pair `Ψ[n'] Ψ[n]` into
`Ψ[n] Ψ[n' + n] Ψ[n']` (Nakanishi, *Cluster algebras and scattering diagrams, Part III*,
§5.2, arXiv:2111.00800v6). There termination is argued by bounding the number of factors
created in each degree; here the Dershowitz–Manna order replaces that count. The statement
is independent of the exchange used.
-/

public section

namespace List

variable {F G : Type*} [Monoid G]

section Inversions

variable (bad : F → F → Prop) [DecidableRel bad]

/-- The pairs `(a, b)` with `a ∈ l₁`, `b ∈ l₂` and `bad a b`, with multiplicity. -/
private def crossInv (l₁ l₂ : List F) : Multiset (F × F) :=
  ((l₁ : Multiset F) ×ˢ (l₂ : Multiset F)).filter fun p => bad p.1 p.2

/-- The inversions of a list: the pairs `(a, b)` with `a` before `b` and `bad a b`. -/
private def inversions : List F → Multiset (F × F)
  | [] => 0
  | a :: l => crossInv bad [a] l + inversions l

private theorem crossInv_append_left (l₁ l₂ l₃ : List F) :
    crossInv bad (l₁ ++ l₂) l₃ = crossInv bad l₁ l₃ + crossInv bad l₂ l₃ := by
  simp [crossInv, ← Multiset.coe_add, Multiset.add_product, Multiset.filter_add]

private theorem crossInv_append_right (l₁ l₂ l₃ : List F) :
    crossInv bad l₁ (l₂ ++ l₃) = crossInv bad l₁ l₂ + crossInv bad l₁ l₃ := by
  simp [crossInv, ← Multiset.coe_add, Multiset.product_add, Multiset.filter_add]

private theorem mem_crossInv {l₁ l₂ : List F} {p : F × F} (hp : p ∈ crossInv bad l₁ l₂) :
    p.1 ∈ l₁ ∧ p.2 ∈ l₂ := by
  simp only [crossInv, Multiset.mem_filter, Multiset.mem_product, Multiset.mem_coe] at hp
  exact hp.1

private theorem crossInv_singleton_of_not {a b : F} (h : ¬ bad a b) :
    crossInv bad [a] [b] = 0 := by
  simp [crossInv, h]

private theorem crossInv_singleton_of_bad {a b : F} (h : bad a b) :
    crossInv bad [a] [b] = {(a, b)} := by
  simp [crossInv, h]

private theorem inversions_singleton (a : F) : inversions bad [a] = 0 := by
  simp [inversions, crossInv]

private theorem inversions_append (l₁ l₂ : List F) :
    inversions bad (l₁ ++ l₂) =
      inversions bad l₁ + inversions bad l₂ + crossInv bad l₁ l₂ := by
  induction l₁ with
  | nil => simp [inversions, crossInv]
  | cons a l₁ ih =>
    rw [cons_append, inversions, ih, crossInv_append_right, inversions,
      ← singleton_append (l := l₁), crossInv_append_left]
    abel

private theorem mem_inversions {l : List F} {p : F × F} (hp : p ∈ inversions bad l) :
    p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [inversions] at hp
  | cons a l ih =>
    rcases Multiset.mem_add.mp hp with hp | hp
    · obtain ⟨h₁, h₂⟩ := mem_crossInv bad hp
      exact ⟨mem_cons.mpr (.inl (mem_singleton.mp h₁)), mem_cons_of_mem a h₂⟩
    · exact (ih hp).imp (mem_cons_of_mem a) (mem_cons_of_mem a)

/-- Exchanging a bad adjacent pair `x y` for `y M x` removes the inversion `(x, y)`, keeps
every other inversion, and adds only inversions containing a factor of `M`. -/
private theorem exists_inversions_exchange {x y : F} (hxy : bad x y) (hyx : ¬ bad y x)
    (A M B : List F) :
    ∃ X Z : Multiset (F × F), inversions bad (A ++ x :: y :: B) = X + {(x, y)} ∧
      inversions bad (A ++ y :: (M ++ x :: B)) = X + Z ∧
      ∀ p ∈ Z, (p.1 ∈ M ∨ p.2 ∈ M) ∧ p.1 ∈ A ++ y :: (M ++ x :: B) ∧
        p.2 ∈ A ++ y :: (M ++ x :: B) := by
  refine ⟨inversions bad A + inversions bad B + crossInv bad [x] B + crossInv bad [y] B +
      crossInv bad A [x] + crossInv bad A [y] + crossInv bad A B,
    inversions bad M + crossInv bad M [x] + crossInv bad [y] M + crossInv bad M B +
      crossInv bad A M, ?_, ?_, ?_⟩
  · -- `inversions_append` splits append blocks, not cons cells. Expose `[x]` and `[y]`
    -- so it separates their mutual inversion from those involving `A` or `B`.
    rw [show A ++ x :: y :: B = A ++ ([x] ++ [y] ++ B) from rfl]
    simp only [inversions_append, inversions_singleton, crossInv_append_left,
      crossInv_append_right, crossInv_singleton_of_bad bad hxy]
    abel
  · -- Expose `[y]`, `M`, and `[x]` as append blocks for `inversions_append`; the
    -- cons form hides these boundaries, and the appends also need reassociation.
    rw [show A ++ y :: (M ++ x :: B) = A ++ ([y] ++ M ++ [x] ++ B) by simp]
    simp only [inversions_append, inversions_singleton, crossInv_append_left,
      crossInv_append_right, crossInv_singleton_of_not bad hyx]
    abel
  · intro p hp
    simp only [Multiset.mem_add] at hp
    rcases hp with (((hp | hp) | hp) | hp) | hp
    · obtain ⟨h₁, h₂⟩ := mem_inversions bad hp
      exact ⟨.inl h₁, by simp [h₁], by simp [h₂]⟩
    · obtain ⟨h₁, h₂⟩ := mem_crossInv bad hp
      rw [mem_singleton] at h₂
      exact ⟨.inl h₁, by simp [h₁], by simp [h₂]⟩
    · obtain ⟨h₁, h₂⟩ := mem_crossInv bad hp
      rw [mem_singleton] at h₁
      exact ⟨.inr h₂, by simp [h₁], by simp [h₂]⟩
    · obtain ⟨h₁, h₂⟩ := mem_crossInv bad hp
      exact ⟨.inl h₁, by simp [h₁], by simp [h₂]⟩
    · obtain ⟨h₁, h₂⟩ := mem_crossInv bad hp
      exact ⟨.inr h₂, by simp [h₁], by simp [h₂]⟩

end Inversions

/-- **Exchange ordering.** Suppose that factors of degree above `k` evaluate to `1`, that
`bad` is asymmetric, and that each bad adjacent pair `x y` of degree at most `k` can be
exchanged as `e x * e y = e y * (M.map e).prod * e x`, inserting only factors of degree
larger than both `deg x` and `deg y`. Then every finite product equals a product of
factors of degree at most `k` with no bad adjacent pair. -/
theorem exists_isChain_prod_map_eq_of_exchange (l : List F) (e : F → G) (deg : F → ℕ)
    (bad : F → F → Prop) (k : ℕ) (hbad : ∀ x y, bad x y → ¬ bad y x)
    (hhigh : ∀ x, k < deg x → e x = 1)
    (hex : ∀ x y, bad x y → deg x ≤ k → deg y ≤ k → ∃ M : List F,
      (∀ m ∈ M, deg x < deg m ∧ deg y < deg m) ∧ e x * e y = e y * (M.map e).prod * e x) :
    ∃ l' : List F, l'.IsChain (fun x y => ¬ bad x y) ∧ (∀ x ∈ l', deg x ≤ k) ∧
      (l'.map e).prod = (l.map e).prod := by
  classical
  suffices H : ∀ l : List F, (∀ x ∈ l, deg x ≤ k) → ∃ l' : List F,
      l'.IsChain (fun x y => ¬ bad x y) ∧ (∀ x ∈ l', deg x ≤ k) ∧
        (l'.map e).prod = (l.map e).prod by
    obtain ⟨l', h₁, h₂, h₃⟩ := H (l.filter fun x => deg x ≤ k) (by simp)
    exact ⟨l', h₁, h₂, h₃.trans (prod_map_filter_of_ne l fun x _ hx => by
      by_contra hk; exact hx (hhigh x (by simpa using hk)))⟩
  -- The weight of an inversion; it is positive and decreases as the degrees grow.
  let ω : F × F → ℕ := fun p => k + 1 - max (deg p.1) (deg p.2)
  intro l
  induction l using (InvImage.wf (fun l => (inversions bad l).map ω)
    Multiset.wellFounded_isDershowitzMannaLT).induction with
  | _ l IH =>
  intro hL
  by_cases hc : l.IsChain fun x y => ¬ bad x y
  · exact ⟨l, hc, hL, rfl⟩
  obtain ⟨x, y, A, B, rfl, hxy⟩ : ∃ x y A B, l = A ++ x :: y :: B ∧ bad x y := by
    rw [isChain_iff_forall_rel_of_append_cons_cons] at hc
    push Not at hc
    exact hc
  have hx : deg x ≤ k := hL x (by simp)
  have hy : deg y ≤ k := hL y (by simp)
  obtain ⟨M, hMdeg, hM⟩ := hex x y hxy hx hy
  -- Exchange `x y` for `y M' x`, where `M'` keeps the factors of `M` of degree at most `k`.
  set M' := M.filter fun m => deg m ≤ k
  have hM'deg : ∀ m ∈ M', deg x < deg m ∧ deg y < deg m ∧ deg m ≤ k := fun m hm => by
    rw [mem_filter, decide_eq_true_eq] at hm
    exact ⟨(hMdeg m hm.1).1, (hMdeg m hm.1).2, hm.2⟩
  have hL' : ∀ z ∈ A ++ y :: (M' ++ x :: B), deg z ≤ k := by
    intro z hz
    simp only [mem_append, mem_cons] at hz
    rcases hz with hz | rfl | hz | rfl | hz
    · exact hL z (by simp [hz])
    · exact hy
    · exact (hM'deg z hz).2.2
    · exact hx
    · exact hL z (by simp [hz])
  -- Every changed inversion contains an inserted factor, so it has smaller weight.
  obtain ⟨X, Z, hinv, hinv', hZ⟩ := exists_inversions_exchange bad hxy (hbad x y hxy) A M' B
  have hZω : ∀ p ∈ Z, ω p < ω (x, y) := by
    intro p hp
    obtain ⟨hm, h₁, h₂⟩ := hZ p hp
    have h₁ := hL' _ h₁
    have h₂ := hL' _ h₂
    rcases hm with hm | hm <;>
    · have := hM'deg _ hm
      simp only [ω]
      omega
  obtain ⟨l', hc', hdeg', hprod'⟩ := IH (A ++ y :: (M' ++ x :: B))
    ⟨X.map ω, Z.map ω, {ω (x, y)}, by simp, by simp only [hinv', Multiset.map_add],
      by simp only [hinv, Multiset.map_add, Multiset.map_singleton],
      fun q hq => by
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hq
        exact ⟨ω (x, y), Multiset.mem_singleton_self _, hZω p hp⟩⟩
    hL'
  refine ⟨l', hc', hdeg', hprod'.trans ?_⟩
  have hM'prod : (M'.map e).prod = (M.map e).prod := prod_map_filter_of_ne M fun m _ hm => by
    by_contra hk; exact hm (hhigh m (by simpa using hk))
  simp only [map_append, map_cons, prod_append, prod_cons, hM'prod]
  rw [← mul_assoc (e x), hM]
  simp only [mul_assoc]

end List
