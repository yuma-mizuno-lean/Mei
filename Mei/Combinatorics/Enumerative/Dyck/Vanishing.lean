/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Shadow
public import Mei.Combinatorics.Enumerative.Dyck.Geometry

/-!
# The vanishing conditions (V) for shadowed compatible grading sums

A grading of the maximal Dyck path of `(d₁, d₂)` is compatible exactly when no horizontal edge
`h` and vertical edge `v` lie in each other's local shadows. We prove the vanishing conditions
(V) of the rank-two polynomial formula: off `(0, 0)`,

* `cplus_eq_zero`: `C₊(p, q) = 0` when `d₁ q ≤ d₂ p`;
* `cminus_eq_zero`: `C₋(p, q) = 0` when `d₂ p ≤ d₁ q`.

Outside the rectangle `p < d₁`, `q < d₂` this follows from the double cycle lemmas of
`Mei.CyclicMatching`, which produce a pair of edges in each other's shadows:

* `not_compatible_of_le`: `p ≥ d₁` and `q ≥ d₂`;
* `not_compatible_of_verticalSupport_subset`: `p ≥ d₁`, and the vertical support lies in the
  total horizontal shadow; this gives `cplus_eq_zero_of_le`, `C₊(p, q) = 0` for `p ≥ d₁`;
* `not_compatible_of_horizontalSupport_subset`: the dual, giving `cminus_eq_zero_of_le`.

Inside the rectangle we use the shape of the path. Every prefix with `x` horizontal and `y`
vertical steps satisfies `d₁ y ≤ d₂ x < d₁ y + d₁ + d₂`
(`Mei.mul_count_take_maximalDyckPath_le_and_lt`), so a subpath from a horizontal to a vertical
edge has
`d₂ #H < d₂ + d₁ #V` (`mul_card_horizontal_lt`) and `d₁ #V < d₁ + d₂ #H`
(`mul_card_vertical_lt`). The slope comparison `Mei.CyclicMatching.mul_sum_lt_of_forall_matched`
then gives `d₂ p < d₁ q` for every grading counted by `C₊(p, q)` with `q < d₂`, and dually.
Combining both regions, every nonzero grading counted by `C₊` has `d₂ p < d₁ q`
(`mul_verticalTotal_lt_mul_horizontalTotal`) and every nonzero grading counted by `C₋` has
`d₁ q < d₂ p` (`mul_horizontalTotal_lt_mul_verticalTotal`).

## References

The two vanishing statements formalize Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, Lemma 5.23
(https://arxiv.org/html/2503.03719v1#S5.SS4). As in that proof, compatibility contradicts the
maximal-path slope bound. Here the argument is organized through general cyclic-walk
double-cycle and slope-comparison lemmas, with explicit zero-dimensional cases.
-/

public section

open DyckStep Finset Mei.CyclicMatching Polynomial

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ} (γ : Edge d₁ d₂ → ℕ)

/-- A horizontal edge and a vertical edge that see each other, in the form produced by the double
cycle lemmas, witness incompatibility. -/
private theorem not_compatible_of_exists
    (H : ∃ h ∉ verticalEdges d₁ d₂, ∃ v ∈ verticalEdges d₁ d₂,
      (∀ e, (e - h).val < (v - h).val →
        ∑ k ∈ cyclicIcc h e, CyclicMatching.weight (verticalEdges d₁ d₂) γ k ≠ 0) ∧
      ∀ e, (v - e).val < (v - h).val →
        ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (verticalEdges d₁ d₂)ᶜ γ k ≠ 0) :
    ¬Compatible γ := by
  obtain ⟨h, hh, v, hv, hfwd, hbwd⟩ := H
  rw [compatible_iff_forall_not_mem_shadow]
  have hhH : h ∈ horizontalEdges d₁ d₂ := mem_horizontalEdges_of_notMem_verticalEdges hh
  refine fun hall ↦ hall h hhH v hv ⟨?_, ?_⟩
  · rw [mem_horizontalShadow]
    exact ⟨hv, fun e he hbal ↦ hfwd e he ((verticalBalanced_iff γ h e).mp hbal)⟩
  · rw [mem_verticalShadow]
    refine ⟨hhH, fun e he hbal ↦ ?_⟩
    rw [horizontalBalanced_iff, ← compl_verticalEdges] at hbal
    exact hbwd e he hbal

/-- **Compatible gradings are small in some direction.** If `p ≥ d₁` and `q ≥ d₂`, with
`(d₁, d₂) ≠ (0, 0)`, the grading is not compatible. -/
theorem not_compatible_of_le (hd : 0 < d₁ + d₂) (hp : d₁ ≤ verticalTotal γ)
    (hq : d₂ ≤ horizontalTotal γ) : ¬Compatible γ := by
  have : NeZero (d₁ + d₂) := ⟨hd.ne'⟩
  exact not_compatible_of_exists γ (exists_mutual (verticalEdges d₁ d₂) γ γ
    (by rw [card_verticalEdges, compl_verticalEdges, ← horizontalTotal_eq]; exact hq)
    (by rw [compl_verticalEdges, card_horizontalEdges, ← verticalTotal_eq]; exact hp))

/-- A supported vertical grade is matched by the horizontal grading. -/
private theorem matched_of_verticalSupport_subset
    (hs : verticalSupport γ ⊆ totalHorizontalShadow γ) :
    ∀ v ∈ verticalEdges d₁ d₂, γ v ≠ 0 → Matched (verticalEdges d₁ d₂) γ v := by
  intro v hv hγ
  have := hs ((mem_verticalSupport γ).mpr ⟨hv, hγ⟩)
  rw [totalHorizontalShadow_eq, mem_filter] at this
  exact this.2

/-- A supported horizontal grade is matched in the reversed direction. -/
private theorem matchedRev_of_horizontalSupport_subset
    (hs : horizontalSupport γ ⊆ totalVerticalShadow γ) :
    ∀ h ∉ verticalEdges d₁ d₂, γ h ≠ 0 → ∃ v ∈ verticalEdges d₁ d₂,
      ∀ e, (v - e).val < (v - h).val →
        ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (verticalEdges d₁ d₂)ᶜ γ k ≠ 0 := by
  intro h hh hγ
  have hhH := mem_horizontalEdges_of_notMem_verticalEdges hh
  obtain ⟨v, hv, hsh⟩ := (mem_totalVerticalShadow γ).mp
    (hs ((mem_horizontalSupport γ).mpr ⟨hhH, hγ⟩))
  refine ⟨v, hv, fun e he hsum ↦ ((mem_verticalShadow γ).mp hsh).2 e he ?_⟩
  rw [horizontalBalanced_iff, ← compl_verticalEdges]
  exact hsum

/-- An empty total horizontal shadow forces a supported vertical total to vanish. -/
private theorem verticalTotal_eq_zero_of_subset_empty
    (hs : verticalSupport γ ⊆ totalHorizontalShadow γ) (he : totalHorizontalShadow γ = ∅) :
    verticalTotal γ = 0 := by
  rw [verticalTotal_eq]
  refine sum_eq_zero fun v hv ↦ by_contra fun hγ ↦ ?_
  have := hs ((mem_verticalSupport γ).mpr ⟨hv, hγ⟩)
  rw [he] at this
  exact notMem_empty v this

/-- An empty total vertical shadow forces a supported horizontal total to vanish. -/
private theorem horizontalTotal_eq_zero_of_subset_empty
    (hs : horizontalSupport γ ⊆ totalVerticalShadow γ) (he : totalVerticalShadow γ = ∅) :
    horizontalTotal γ = 0 := by
  rw [horizontalTotal_eq]
  refine sum_eq_zero fun h hh ↦ by_contra fun hγ ↦ ?_
  have := hs ((mem_horizontalSupport γ).mpr ⟨hh, hγ⟩)
  rw [he] at this
  exact notMem_empty h this

/-- If `p ≥ d₁ > 0` and every vertical edge of nonzero grade lies in the total horizontal
shadow, the grading is not compatible. -/
theorem not_compatible_of_verticalSupport_subset (hd₁ : 0 < d₁) (hp : d₁ ≤ verticalTotal γ)
    (hs : verticalSupport γ ⊆ totalHorizontalShadow γ) : ¬Compatible γ := by
  have : NeZero (d₁ + d₂) := ⟨by omega⟩
  refine not_compatible_of_exists γ (exists_mutual_of_forall_matched (verticalEdges d₁ d₂) γ γ
    ?_ (matched_of_verticalSupport_subset γ hs) ?_)
  · rw [compl_verticalEdges, ← card_pos, card_horizontalEdges]
    exact hd₁
  · rw [compl_verticalEdges, card_horizontalEdges, ← verticalTotal_eq]
    exact hp

/-- If `q ≥ d₂ > 0` and every horizontal edge of nonzero grade lies in the total vertical
shadow, the grading is not compatible. -/
theorem not_compatible_of_horizontalSupport_subset (hd₂ : 0 < d₂)
    (hq : d₂ ≤ horizontalTotal γ) (hs : horizontalSupport γ ⊆ totalVerticalShadow γ) :
    ¬Compatible γ := by
  have : NeZero (d₁ + d₂) := ⟨by omega⟩
  refine not_compatible_of_exists γ (exists_mutual_of_forall_matched_rev (verticalEdges d₁ d₂) γ
    γ ?_ (matchedRev_of_horizontalSupport_subset γ hs) ?_)
  · rw [← card_pos, card_verticalEdges]
    exact hd₂
  · rw [card_verticalEdges, compl_verticalEdges, ← horizontalTotal_eq]
    exact hq

variable {S : Type*} [CommSemiring S] (P₁ P₂ : S[X])

/-- **(V) for `C₊` in the region `p ≥ d₁`.** Off `(0, 0)`, `C₊(p, q) = 0` when `p ≥ d₁`. -/
@[simp]
theorem cplus_eq_zero_of_le {p q : ℕ} (hp : d₁ ≤ p) (h0 : (p, q) ≠ (0, 0)) :
    cplus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cplus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  rcases Nat.eq_zero_or_pos d₁ with hd₁ | hd₁
  · subst hd₁
    -- Without horizontal edges both totals vanish.
    have hq0 := horizontalTotal_zero_left γ
    have hp0 := verticalTotal_eq_zero_of_subset_empty γ hs (by
      rw [← card_eq_zero, card_totalHorizontalShadow, hq0, _root_.min_zero])
    exact h0 (by rw [hp0, hq0])
  · exact not_compatible_of_verticalSupport_subset γ hd₁ hp hs hc

/-- **(V) for `C₋` in the region `q ≥ d₂`.** Off `(0, 0)`, `C₋(p, q) = 0` when `q ≥ d₂`. -/
@[simp]
theorem cminus_eq_zero_of_le {p q : ℕ} (hq : d₂ ≤ q) (h0 : (p, q) ≠ (0, 0)) :
    cminus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cminus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  rcases Nat.eq_zero_or_pos d₂ with hd₂ | hd₂
  · subst hd₂
    -- Without vertical edges both totals vanish.
    have hp0 := verticalTotal_zero_right γ
    have hq0 := horizontalTotal_eq_zero_of_subset_empty γ hs (by
      rw [← card_eq_zero, card_totalVerticalShadow, hp0, _root_.min_zero])
    exact h0 (by rw [hp0, hq0])
  · exact not_compatible_of_horizontalSupport_subset γ hd₂ hq hs hc

/-- In a compatible grading, a vertical edge `v` in the local shadow of a horizontal edge `h`
is separated from it by a horizontally balanced final subpath. -/
private theorem exists_balanced_of_compatible {γ : Edge d₁ d₂ → ℕ} (hc : Compatible γ)
    {h : Edge d₁ d₂} (hh : h ∉ verticalEdges d₁ d₂) {v : Edge d₁ d₂} (hv : v ∈ verticalEdges d₁ d₂)
    (hfwd : ∀ e, (e - h).val < (v - h).val →
      ∑ k ∈ cyclicIcc h e, CyclicMatching.weight (verticalEdges d₁ d₂) γ k ≠ 0) :
    ∃ e, (v - e).val < (v - h).val ∧
      ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (verticalEdges d₁ d₂)ᶜ γ k = 0 := by
  have hhH : h ∈ horizontalEdges d₁ d₂ := mem_horizontalEdges_of_notMem_verticalEdges hh
  have hsh : v ∈ horizontalShadow γ h := (mem_horizontalShadow γ).mpr
    ⟨hv, fun e he hbal ↦ hfwd e he ((verticalBalanced_iff γ h e).mp hbal)⟩
  have hnot : h ∉ verticalShadow γ v := fun hm ↦
    (compatible_iff_forall_not_mem_shadow γ).mp hc h hhH v hv ⟨hsh, hm⟩
  rw [mem_verticalShadow] at hnot
  push Not at hnot
  obtain ⟨e, he, hbal⟩ := hnot hhH
  exact ⟨e, he, by rw [compl_verticalEdges, ← horizontalBalanced_iff]; exact hbal⟩

/-- In a compatible grading, a horizontal edge `h` in the local shadow of a vertical edge `v` is
separated from it by a vertically balanced initial subpath. -/
private theorem exists_balanced_of_compatible' {γ : Edge d₁ d₂ → ℕ} (hc : Compatible γ)
    {h : Edge d₁ d₂} (hh : h ∉ verticalEdges d₁ d₂) {v : Edge d₁ d₂} (hv : v ∈ verticalEdges d₁ d₂)
    (hbwd : ∀ e, (v - e).val < (v - h).val →
      ∑ k ∈ cyclicIcc e v, CyclicMatching.weight (verticalEdges d₁ d₂)ᶜ γ k ≠ 0) :
    ∃ e, (e - h).val < (v - h).val ∧
      ∑ k ∈ cyclicIcc h e, CyclicMatching.weight (verticalEdges d₁ d₂) γ k = 0 := by
  have hhH : h ∈ horizontalEdges d₁ d₂ := mem_horizontalEdges_of_notMem_verticalEdges hh
  have hsh : h ∈ verticalShadow γ v := (mem_verticalShadow γ).mpr
    ⟨hhH, fun e he hbal ↦ hbwd e he (by
      rw [compl_verticalEdges, ← horizontalBalanced_iff]; exact hbal)⟩
  have hnot : v ∉ horizontalShadow γ h := fun hm ↦
    (compatible_iff_forall_not_mem_shadow γ).mp hc h hhH v hv ⟨hm, hsh⟩
  rw [mem_horizontalShadow] at hnot
  push Not at hnot
  obtain ⟨e, he, hbal⟩ := hnot hv
  exact ⟨e, he, (verticalBalanced_iff γ h e).mp hbal⟩

/-- **Slope of the gradings counted by `C₊`.** A nonzero compatible grading whose nonzero
vertical support lies in the total horizontal shadow has `d₂ p < d₁ q`. -/
theorem mul_verticalTotal_lt_mul_horizontalTotal {γ : Edge d₁ d₂ → ℕ} (hc : Compatible γ)
    (hs : verticalSupport γ ⊆ totalHorizontalShadow γ) (hγ : γ ≠ 0) :
    d₂ * verticalTotal γ < d₁ * horizontalTotal γ := by
  by_contra hpq
  push Not at hpq
  have h0 : (verticalTotal γ, horizontalTotal γ) ≠ (0, 0) := fun h ↦
    hγ (eq_zero_of_totals_eq_zero γ (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2)
  rcases le_or_gt d₁ (verticalTotal γ) with hp | hp
  · rcases Nat.eq_zero_or_pos d₁ with hd₁ | hd₁
    · subst hd₁
      -- Without horizontal edges both totals vanish.
      have hq0 := horizontalTotal_zero_left γ
      have hp0 := verticalTotal_eq_zero_of_subset_empty γ hs (by
        rw [← card_eq_zero, card_totalHorizontalShadow, hq0, _root_.min_zero])
      exact h0 (by rw [hp0, hq0])
    · exact not_compatible_of_verticalSupport_subset γ hd₁ hp hs hc
  have hd : 0 < d₁ + d₂ := by omega
  have : NeZero (d₁ + d₂) := ⟨hd.ne'⟩
  have hq : horizontalTotal γ < d₂ := by
    by_contra hq
    push Not at hq
    have h₁ : d₁ * d₂ ≤ d₂ * verticalTotal γ := (Nat.mul_le_mul_left d₁ hq).trans hpq
    have hd₂ : d₂ = 0 := Nat.eq_zero_of_le_zero (by nlinarith)
    subst hd₂
    have hp0 := verticalTotal_zero_right γ
    rw [hp0, mul_zero, Nat.le_zero, Nat.mul_eq_zero] at hpq
    exact h0 (by rw [hp0, hpq.resolve_left (by omega)])
  -- With no horizontal grade, the total horizontal shadow and hence `p` vanish.
  have hq0 : horizontalTotal γ ≠ 0 := by
    intro hq0
    have hempty : totalHorizontalShadow γ = ∅ := by
      rw [← card_eq_zero, card_totalHorizontalShadow, hq0, _root_.min_zero]
    have hp0 := verticalTotal_eq_zero_of_subset_empty γ hs hempty
    exact h0 (by rw [hp0, hq0])
  have hlt := mul_sum_lt_of_forall_matched (verticalEdges d₁ d₂) γ γ d₂ d₁
    (fun h hh e he ↦ by
      rw [compl_verticalEdges]
      exact mul_card_horizontal_lt h e he)
    (fun h hh v hv hfwd ↦ exists_balanced_of_compatible hc hh hv hfwd)
    (matched_of_verticalSupport_subset γ hs)
    (by rw [compl_verticalEdges, ← horizontalTotal_eq, card_verticalEdges]; exact hq)
    (by rw [compl_verticalEdges, ← horizontalTotal_eq]; exact hq0)
  rw [← verticalTotal_eq, compl_verticalEdges, ← horizontalTotal_eq] at hlt
  omega

/-- **Slope of the gradings counted by `C₋`.** A nonzero compatible grading whose nonzero
horizontal support lies in the total vertical shadow has `d₁ q < d₂ p`. -/
theorem mul_horizontalTotal_lt_mul_verticalTotal {γ : Edge d₁ d₂ → ℕ} (hc : Compatible γ)
    (hs : horizontalSupport γ ⊆ totalVerticalShadow γ) (hγ : γ ≠ 0) :
    d₁ * horizontalTotal γ < d₂ * verticalTotal γ := by
  by_contra hpq
  push Not at hpq
  have h0 : (verticalTotal γ, horizontalTotal γ) ≠ (0, 0) := fun h ↦
    hγ (eq_zero_of_totals_eq_zero γ (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2)
  rcases le_or_gt d₂ (horizontalTotal γ) with hq | hq
  · rcases Nat.eq_zero_or_pos d₂ with hd₂ | hd₂
    · subst hd₂
      -- Without vertical edges both totals vanish.
      have hp0 := verticalTotal_zero_right γ
      have hq0 := horizontalTotal_eq_zero_of_subset_empty γ hs (by
        rw [← card_eq_zero, card_totalVerticalShadow, hp0, _root_.min_zero])
      exact h0 (by rw [hp0, hq0])
    · exact not_compatible_of_horizontalSupport_subset γ hd₂ hq hs hc
  have hd : 0 < d₁ + d₂ := by omega
  have : NeZero (d₁ + d₂) := ⟨hd.ne'⟩
  have hp : verticalTotal γ < d₁ := by
    by_contra hp
    push Not at hp
    have h₁ : d₂ * d₁ ≤ d₁ * horizontalTotal γ := (Nat.mul_le_mul_left d₂ hp).trans hpq
    have hd₁ : d₁ = 0 := Nat.eq_zero_of_le_zero (by nlinarith)
    subst hd₁
    have hq0 := horizontalTotal_zero_left γ
    rw [hq0, mul_zero, Nat.le_zero, Nat.mul_eq_zero] at hpq
    exact h0 (by rw [hq0, hpq.resolve_left (by omega)])
  -- With no vertical grade, the total vertical shadow and hence `q` vanish.
  have hp0 : verticalTotal γ ≠ 0 := by
    intro hp0
    have hempty : totalVerticalShadow γ = ∅ := by
      rw [← card_eq_zero, card_totalVerticalShadow, hp0, _root_.min_zero]
    have hq0 := horizontalTotal_eq_zero_of_subset_empty γ hs hempty
    exact h0 (by rw [hp0, hq0])
  have hlt := mul_sum_lt_of_forall_matched_rev (verticalEdges d₁ d₂) γ γ d₁ d₂
    (fun h hh v hv ↦ by
      rw [compl_verticalEdges]
      exact mul_card_vertical_lt h (mem_horizontalEdges_of_notMem_verticalEdges hh) v)
    (fun h hh v hv hbwd ↦ exists_balanced_of_compatible' hc hh hv hbwd)
    (matchedRev_of_horizontalSupport_subset γ hs)
    (by rw [← verticalTotal_eq, compl_verticalEdges, card_horizontalEdges]; exact hp)
    (by rw [← verticalTotal_eq]; exact hp0)
  rw [← verticalTotal_eq, compl_verticalEdges, ← horizontalTotal_eq] at hlt
  omega

/-- **(V) for `C₊`.** Off `(0, 0)`, `C₊(p, q) = 0` when `d₁ q ≤ d₂ p`. -/
@[simp]
theorem cplus_eq_zero {p q : ℕ} (h0 : (p, q) ≠ (0, 0)) (hpq : d₁ * q ≤ d₂ * p) :
    cplus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cplus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  refine (mul_verticalTotal_lt_mul_horizontalTotal hc hs fun hγ ↦ h0 ?_).not_ge hpq
  rw [hγ, verticalTotal_zero, horizontalTotal_zero]

/-- **(V) for `C₋`.** Off `(0, 0)`, `C₋(p, q) = 0` when `d₂ p ≤ d₁ q`. -/
@[simp]
theorem cminus_eq_zero {p q : ℕ} (h0 : (p, q) ≠ (0, 0)) (hpq : d₂ * p ≤ d₁ * q) :
    cminus d₁ d₂ P₁ P₂ p q = 0 := by
  rw [cminus_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, not_and]
  rintro - ⟨hc, rfl, rfl, hs⟩
  refine (mul_horizontalTotal_lt_mul_verticalTotal hc hs fun hγ ↦ h0 ?_).not_ge hpq
  rw [hγ, verticalTotal_zero, horizontalTotal_zero]

end Mei.MaximalDyckPath
