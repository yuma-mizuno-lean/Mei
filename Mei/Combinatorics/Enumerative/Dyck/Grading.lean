/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Basic
public import Mei.Combinatorics.Enumerative.CyclicMatching
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Tactic.FinCases

/-!
# Compatible gradings of maximal Dyck paths

A grading of the maximal Dyck path of `(d₁, d₂)` assigns a natural number to every edge; we
write `γ_V` for its values on vertical edges and `γ_H` for those on horizontal edges, with
totals `p = ∑ γ_V` and `q = ∑ γ_H`. Subpaths include both endpoint edges and wrap cyclically
from the last edge to the first; they are the cyclic intervals `Mei.CyclicMatching.cyclicIcc`.

* `Compatible`: for every horizontal edge `h` and vertical edge `v`, some proper initial
  subpath `he` of `hv` has as many vertical edges as the horizontal grade sum on it, or some
  proper final subpath `ev` of `hv` has as many horizontal edges as the vertical grade sum on
  it. One-edge subpaths are allowed.
* `horizontalShadow γ h`: the local shadow of a horizontal edge `h`, namely the vertical edges
  of the shortest subpath starting at `h` whose vertical edge count equals its horizontal grade
  sum, or all vertical edges if there is no such subpath. `verticalShadow` is dual, using
  subpaths ending at a vertical edge. The total shadows are the unions of local shadows.
* `Shadowed`: a compatible grading whose nonzero horizontal support lies in the total vertical
  shadow, or whose nonzero vertical support lies in the total horizontal shadow.
* `Tight`: a shadowed grading with `p ≤ d₁`, `q ≤ d₂` and `p d₂ - q d₁ = ± gcd(p, q)`.
* `cplus` and `cminus`: for polynomials `P₁, P₂`, the sums of the weights
  `∏_v [x^{γ_V(v)}] P₁ ∏_h [y^{γ_H(h)}] P₂` of compatible gradings with totals `(p, q)` whose
  nonzero vertical support lies in the total horizontal shadow, respectively whose nonzero
  horizontal support lies in the total vertical shadow. Grades are bounded by the degrees.
* `shadowedSum` and `tightSum`: the weight sums of the shadowed, respectively tight, gradings
  with totals `(p, q)`. The tight sum is the shadowed sum when `p ≤ d₁`, `q ≤ d₂` and
  `|p d₂ - q d₁| = gcd(p, q)` (`tightSum_eq_shadowedSum`), and zero otherwise
  (`tightSum_eq_zero`).

When `P₁` and `P₂` have constant coefficient `1`, `C₊`, `C₋` and the shadowed sum equal `1` at
`(p, q) = (0, 0)`, the only contribution being the zero grading.

These are the gradings of Lee–Li–Zelevinsky and Rupel used by Burcroff–Lee–Mou for the
coefficients of rank-two wall functions.
-/

public section

open DyckStep Finset Polynomial
open Mei.CyclicMatching (cyclicIcc mem_cyclicIcc cyclicIcc_self cyclicIcc_subset_of_mem)
open Fin (val_sub_eq_zero_iff val_sub_self)

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ}

section Grading

variable (γ : Edge d₁ d₂ → ℕ)

/-- The total grade `p` of the vertical edges. -/
def verticalTotal : ℕ := ∑ v ∈ verticalEdges d₁ d₂, γ v

/-- The total grade `q` of the horizontal edges. -/
def horizontalTotal : ℕ := ∑ h ∈ horizontalEdges d₁ d₂, γ h

/-- The vertical edges with nonzero grade. -/
def verticalSupport : Finset (Edge d₁ d₂) := {v ∈ verticalEdges d₁ d₂ | γ v ≠ 0}

/-- The horizontal edges with nonzero grade. -/
def horizontalSupport : Finset (Edge d₁ d₂) := {h ∈ horizontalEdges d₁ d₂ | γ h ≠ 0}

theorem verticalTotal_eq : verticalTotal γ = ∑ v ∈ verticalEdges d₁ d₂, γ v := (rfl)

theorem horizontalTotal_eq : horizontalTotal γ = ∑ h ∈ horizontalEdges d₁ d₂, γ h := (rfl)

/-- With no horizontal edges, every grading has zero horizontal total. -/
@[simp]
theorem horizontalTotal_zero_left (γ : Edge 0 d₂ → ℕ) : horizontalTotal γ = 0 := by
  have hH : horizontalEdges 0 d₂ = ∅ := by rw [← card_eq_zero, card_horizontalEdges]
  rw [horizontalTotal_eq, hH, sum_empty]

/-- With no vertical edges, every grading has zero vertical total. -/
@[simp]
theorem verticalTotal_zero_right (γ : Edge d₁ 0 → ℕ) : verticalTotal γ = 0 := by
  have hV : verticalEdges d₁ 0 = ∅ := by rw [← card_eq_zero, card_verticalEdges]
  rw [verticalTotal_eq, hV, sum_empty]

/-- The zero grading has zero vertical total. -/
@[simp]
theorem verticalTotal_zero : verticalTotal (0 : Edge d₁ d₂ → ℕ) = 0 := by
  simp [verticalTotal]

/-- The zero grading has zero horizontal total. -/
@[simp]
theorem horizontalTotal_zero : horizontalTotal (0 : Edge d₁ d₂ → ℕ) = 0 := by
  simp [horizontalTotal]

/-- The zero grading has empty vertical support. -/
@[simp]
theorem verticalSupport_zero : verticalSupport (0 : Edge d₁ d₂ → ℕ) = ∅ := by
  simp [verticalSupport]

/-- The zero grading has empty horizontal support. -/
@[simp]
theorem horizontalSupport_zero : horizontalSupport (0 : Edge d₁ d₂ → ℕ) = ∅ := by
  simp [horizontalSupport]

@[simp]
theorem mem_verticalSupport {e : Edge d₁ d₂} :
    e ∈ verticalSupport γ ↔ e ∈ verticalEdges d₁ d₂ ∧ γ e ≠ 0 := by
  simp [verticalSupport]

@[simp]
theorem mem_horizontalSupport {e : Edge d₁ d₂} :
    e ∈ horizontalSupport γ ↔ e ∈ horizontalEdges d₁ d₂ ∧ γ e ≠ 0 := by
  simp [horizontalSupport]

/-- On the subpath `ee'`, the number of vertical edges equals the horizontal grade sum. -/
def VerticalBalanced (e e' : Edge d₁ d₂) : Prop :=
  #(cyclicIcc e e' ∩ verticalEdges d₁ d₂) = ∑ h ∈ cyclicIcc e e' ∩ horizontalEdges d₁ d₂, γ h

/-- The defining condition for `VerticalBalanced`. -/
theorem verticalBalanced_iff_card_eq_sum (e e' : Edge d₁ d₂) :
    VerticalBalanced γ e e' ↔
      #(cyclicIcc e e' ∩ verticalEdges d₁ d₂) =
        ∑ h ∈ cyclicIcc e e' ∩ horizontalEdges d₁ d₂, γ h := Iff.rfl

/-- On the subpath `ee'`, the number of horizontal edges equals the vertical grade sum. -/
def HorizontalBalanced (e e' : Edge d₁ d₂) : Prop :=
  #(cyclicIcc e e' ∩ horizontalEdges d₁ d₂) = ∑ v ∈ cyclicIcc e e' ∩ verticalEdges d₁ d₂, γ v

/-- The defining condition for `HorizontalBalanced`. -/
theorem horizontalBalanced_iff_card_eq_sum (e e' : Edge d₁ d₂) :
    HorizontalBalanced γ e e' ↔
      #(cyclicIcc e e' ∩ horizontalEdges d₁ d₂) =
        ∑ v ∈ cyclicIcc e e' ∩ verticalEdges d₁ d₂, γ v := Iff.rfl

instance (e e' : Edge d₁ d₂) : Decidable (VerticalBalanced γ e e') :=
  decidable_of_iff _ (verticalBalanced_iff_card_eq_sum γ e e').symm

instance (e e' : Edge d₁ d₂) : Decidable (HorizontalBalanced γ e e') :=
  decidable_of_iff _ (horizontalBalanced_iff_card_eq_sum γ e e').symm

/-- A grading is compatible if for every horizontal edge `h` and vertical edge `v`, some proper
initial subpath `he` of `hv` is vertically balanced, or some proper final subpath `ev` of `hv`
is horizontally balanced. -/
def Compatible : Prop :=
  ∀ h ∈ horizontalEdges d₁ d₂, ∀ v ∈ verticalEdges d₁ d₂,
    (∃ e, (e - h).val < (v - h).val ∧ VerticalBalanced γ h e) ∨
      ∃ e, (v - e).val < (v - h).val ∧ HorizontalBalanced γ e v

/-- The defining condition for `Compatible`. -/
theorem compatible_iff :
    Compatible γ ↔
      ∀ h ∈ horizontalEdges d₁ d₂, ∀ v ∈ verticalEdges d₁ d₂,
        (∃ e, (e - h).val < (v - h).val ∧ VerticalBalanced γ h e) ∨
          ∃ e, (v - e).val < (v - h).val ∧ HorizontalBalanced γ e v := Iff.rfl

instance : Decidable (Compatible γ) :=
  decidable_of_iff _ (compatible_iff γ).symm

/-- Offsets `(e - h)` of the vertically balanced subpaths `he` starting at `h`. -/
private def verticalBalancedOffsets (h : Edge d₁ d₂) : Finset ℕ :=
  (univ.filter fun e ↦ VerticalBalanced γ h e).image fun e ↦ (e - h).val

/-- Offsets `(v - e)` of the horizontally balanced subpaths `ev` ending at `v`. -/
private def horizontalBalancedOffsets (v : Edge d₁ d₂) : Finset ℕ :=
  (univ.filter fun e ↦ HorizontalBalanced γ e v).image fun e ↦ (v - e).val

/-- The local shadow of a horizontal edge `h`: the vertical edges of the shortest vertically
balanced subpath starting at `h`, or all vertical edges if there is none. -/
def horizontalShadow (h : Edge d₁ d₂) : Finset (Edge d₁ d₂) :=
  if hS : (verticalBalancedOffsets γ h).Nonempty then
    {k ∈ verticalEdges d₁ d₂ | (k - h).val ≤ (verticalBalancedOffsets γ h).min' hS}
  else verticalEdges d₁ d₂

/-- The local shadow of a vertical edge `v`: the horizontal edges of the shortest horizontally
balanced subpath ending at `v`, or all horizontal edges if there is none. -/
def verticalShadow (v : Edge d₁ d₂) : Finset (Edge d₁ d₂) :=
  if hS : (horizontalBalancedOffsets γ v).Nonempty then
    {k ∈ horizontalEdges d₁ d₂ | (v - k).val ≤ (horizontalBalancedOffsets γ v).min' hS}
  else horizontalEdges d₁ d₂

/-- The total horizontal shadow, a set of vertical edges. -/
def totalHorizontalShadow : Finset (Edge d₁ d₂) :=
  (horizontalEdges d₁ d₂).biUnion (horizontalShadow γ)

/-- The total vertical shadow, a set of horizontal edges. -/
def totalVerticalShadow : Finset (Edge d₁ d₂) :=
  (verticalEdges d₁ d₂).biUnion (verticalShadow γ)

/-- A vertical edge lies in the local shadow of `h` exactly when no vertically balanced
subpath from `h` stops before it. -/
theorem mem_horizontalShadow {h k : Edge d₁ d₂} :
    k ∈ horizontalShadow γ h ↔
      k ∈ verticalEdges d₁ d₂ ∧ ∀ e, (e - h).val < (k - h).val → ¬VerticalBalanced γ h e := by
  unfold horizontalShadow
  split_ifs with hS
  · rw [mem_filter]
    refine and_congr_right fun _ ↦ ?_
    rw [Finset.le_min'_iff, verticalBalancedOffsets, Finset.forall_mem_image]
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hbound e hlt hbal
      exact (not_le_of_gt hlt) (hbound hbal)
    · intro hnone e hbal
      exact le_of_not_gt fun hlt ↦ hnone e hlt hbal
  · refine ⟨fun hk ↦ ⟨hk, fun e _ hbal ↦ hS ?_⟩, And.left⟩
    exact ⟨_, mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, hbal⟩, rfl⟩⟩

/-- A horizontal edge lies in the local shadow of `v` exactly when no horizontally balanced
subpath ending at `v` starts after it. -/
theorem mem_verticalShadow {v k : Edge d₁ d₂} :
    k ∈ verticalShadow γ v ↔
      k ∈ horizontalEdges d₁ d₂ ∧ ∀ e, (v - e).val < (v - k).val → ¬HorizontalBalanced γ e v := by
  unfold verticalShadow
  split_ifs with hS
  · rw [mem_filter]
    refine and_congr_right fun _ ↦ ?_
    rw [Finset.le_min'_iff, horizontalBalancedOffsets, Finset.forall_mem_image]
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hbound e hlt hbal
      exact (not_le_of_gt hlt) (hbound hbal)
    · intro hnone e hbal
      exact le_of_not_gt fun hlt ↦ hnone e hlt hbal
  · refine ⟨fun hk ↦ ⟨hk, fun e _ hbal ↦ hS ?_⟩, And.left⟩
    exact ⟨_, mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, hbal⟩, rfl⟩⟩

theorem mem_totalHorizontalShadow {k : Edge d₁ d₂} :
    k ∈ totalHorizontalShadow γ ↔ ∃ h ∈ horizontalEdges d₁ d₂, k ∈ horizontalShadow γ h := by
  simp [totalHorizontalShadow]

theorem mem_totalVerticalShadow {k : Edge d₁ d₂} :
    k ∈ totalVerticalShadow γ ↔ ∃ v ∈ verticalEdges d₁ d₂, k ∈ verticalShadow γ v := by
  simp [totalVerticalShadow]

/-- A local shadow of a horizontal edge consists of vertical edges. -/
theorem horizontalShadow_subset (h : Edge d₁ d₂) :
    horizontalShadow γ h ⊆ verticalEdges d₁ d₂ := by
  unfold horizontalShadow
  split_ifs
  · exact Finset.filter_subset _ _
  · exact subset_rfl

/-- A local shadow of a vertical edge consists of horizontal edges. -/
theorem verticalShadow_subset (v : Edge d₁ d₂) :
    verticalShadow γ v ⊆ horizontalEdges d₁ d₂ := by
  unfold verticalShadow
  split_ifs
  · exact Finset.filter_subset _ _
  · exact subset_rfl

/-- The total horizontal shadow consists of vertical edges. -/
theorem totalHorizontalShadow_subset : totalHorizontalShadow γ ⊆ verticalEdges d₁ d₂ :=
  Finset.biUnion_subset.mpr fun h _ ↦ horizontalShadow_subset γ h

/-- The total vertical shadow consists of horizontal edges. -/
theorem totalVerticalShadow_subset : totalVerticalShadow γ ⊆ horizontalEdges d₁ d₂ :=
  Finset.biUnion_subset.mpr fun v _ ↦ verticalShadow_subset γ v

/-- A horizontal edge of grade zero has empty local shadow. -/
@[simp]
theorem horizontalShadow_eq_empty {h : Edge d₁ d₂} (hh : h ∈ horizontalEdges d₁ d₂)
    (h0 : γ h = 0) : horizontalShadow γ h = ∅ := by
  have hmem : 0 ∈ verticalBalancedOffsets γ h := by
    refine Finset.mem_image.mpr ⟨h, ?_, val_sub_self h⟩
    rw [Finset.mem_filter, VerticalBalanced, cyclicIcc_self, Finset.singleton_inter_of_notMem
      (notMem_verticalEdges_of_mem hh), Finset.singleton_inter_of_mem hh,
      Finset.sum_singleton, h0]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hS : (verticalBalancedOffsets γ h).Nonempty := ⟨0, hmem⟩
  have hmin : (verticalBalancedOffsets γ h).min' hS = 0 :=
    Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hmem)
  rw [horizontalShadow, dite_eq_left hS, hmin, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  rw [Finset.mem_filter, Nat.le_zero, val_sub_eq_zero_iff] at hk
  obtain ⟨hkv, rfl⟩ := hk
  exact notMem_verticalEdges_of_mem hh hkv

/-- A vertical edge of grade zero has empty local shadow. -/
@[simp]
theorem verticalShadow_eq_empty {v : Edge d₁ d₂} (hv : v ∈ verticalEdges d₁ d₂)
    (h0 : γ v = 0) : verticalShadow γ v = ∅ := by
  have hmem : 0 ∈ horizontalBalancedOffsets γ v := by
    refine Finset.mem_image.mpr ⟨v, ?_, val_sub_self v⟩
    rw [Finset.mem_filter, HorizontalBalanced, cyclicIcc_self, Finset.singleton_inter_of_notMem
      (notMem_horizontalEdges_of_mem hv), Finset.singleton_inter_of_mem hv,
      Finset.sum_singleton, h0]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hS : (horizontalBalancedOffsets γ v).Nonempty := ⟨0, hmem⟩
  have hmin : (horizontalBalancedOffsets γ v).min' hS = 0 :=
    Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hmem)
  rw [verticalShadow, dite_eq_left hS, hmin, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  rw [Finset.mem_filter, Nat.le_zero, val_sub_eq_zero_iff] at hk
  obtain ⟨hkh, rfl⟩ := hk
  exact notMem_horizontalEdges_of_mem hv hkh

/-- The zero grading has empty total horizontal shadow. -/
@[simp]
theorem totalHorizontalShadow_zero : totalHorizontalShadow (0 : Edge d₁ d₂ → ℕ) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨h, hh, hk⟩ := (mem_totalHorizontalShadow _).mp hk
  rw [horizontalShadow_eq_empty (0 : Edge d₁ d₂ → ℕ) hh rfl] at hk
  exact Finset.notMem_empty k hk

/-- The zero grading has empty total vertical shadow. -/
@[simp]
theorem totalVerticalShadow_zero : totalVerticalShadow (0 : Edge d₁ d₂ → ℕ) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨v, hv, hk⟩ := (mem_totalVerticalShadow _).mp hk
  rw [verticalShadow_eq_empty (0 : Edge d₁ d₂ → ℕ) hv rfl] at hk
  exact Finset.notMem_empty k hk

/-- A compatible grading is shadowed if its nonzero horizontal support lies in the total
vertical shadow, or its nonzero vertical support lies in the total horizontal shadow. -/
def Shadowed : Prop :=
  Compatible γ ∧ (horizontalSupport γ ⊆ totalVerticalShadow γ ∨
    verticalSupport γ ⊆ totalHorizontalShadow γ)

/-- The defining condition for `Shadowed`. -/
theorem shadowed_iff :
    Shadowed γ ↔ Compatible γ ∧
      (horizontalSupport γ ⊆ totalVerticalShadow γ ∨
        verticalSupport γ ⊆ totalHorizontalShadow γ) := Iff.rfl

instance : Decidable (Shadowed γ) :=
  decidable_of_iff _ (shadowed_iff γ).symm

/-- A shadowed grading is tight if `p ≤ d₁`, `q ≤ d₂` and `p d₂ - q d₁ = ± gcd(p, q)`. -/
def Tight : Prop :=
  Shadowed γ ∧ verticalTotal γ ≤ d₁ ∧ horizontalTotal γ ≤ d₂ ∧
    ((verticalTotal γ * d₂ : ℤ) - horizontalTotal γ * d₁).natAbs =
      (verticalTotal γ).gcd (horizontalTotal γ)

/-- The defining condition for `Tight`. -/
theorem tight_iff :
    Tight γ ↔ Shadowed γ ∧ verticalTotal γ ≤ d₁ ∧ horizontalTotal γ ≤ d₂ ∧
      ((verticalTotal γ * d₂ : ℤ) - horizontalTotal γ * d₁).natAbs =
        (verticalTotal γ).gcd (horizontalTotal γ) := Iff.rfl

instance : Decidable (Tight γ) :=
  decidable_of_iff _ (tight_iff γ).symm

/-- The zero grading is compatible: the one-edge subpath at each horizontal edge is
vertically balanced. -/
@[simp]
theorem compatible_zero : Compatible (0 : Edge d₁ d₂ → ℕ) := by
  intro h hh v hv
  left
  refine ⟨h, ?_, ?_⟩
  · rw [val_sub_self]
    refine Nat.pos_of_ne_zero fun hvh ↦ ?_
    rw [val_sub_eq_zero_iff] at hvh
    subst hvh
    exact notMem_verticalEdges_of_mem hh hv
  · rw [VerticalBalanced, cyclicIcc_self, Finset.singleton_inter_of_notMem
      (notMem_verticalEdges_of_mem hh)]
    simp

/-- A grading with vanishing totals is zero. -/
theorem eq_zero_of_totals_eq_zero (h₁ : verticalTotal γ = 0) (h₂ : horizontalTotal γ = 0) :
    γ = 0 := by
  rw [verticalTotal, Finset.sum_eq_zero_iff] at h₁
  rw [horizontalTotal, Finset.sum_eq_zero_iff] at h₂
  funext e
  rcases mem_horizontalEdges_or_mem_verticalEdges e with he | he
  · exact h₂ e he
  · exact h₁ e he

end Grading

/-- On the path `UDD`, grading the first and last edges by one gives a nondegenerate
shadowed, tight grading. Both totals are one, and `p d₂ - q d₁ = 1`. The horizontal
support lies in the total vertical shadow; the vertical support does not lie in the
horizontal shadow. -/
theorem exists_tight_one_two :
    ∃ γ : Edge 1 2 → ℕ, verticalTotal γ = 1 ∧ horizontalTotal γ = 1 ∧
      Shadowed γ ∧ Tight γ ∧ ¬verticalSupport γ ⊆ totalHorizontalShadow γ := by
  have hH : horizontalEdges 1 2 = {0} := by
    ext e
    fin_cases e <;> simp [mem_horizontalEdges, step_def,
      maximalDyckPath_of_ne_zero (d₁ := 1) 2 (by decide), List.range_succ]
  have hV : verticalEdges 1 2 = {1, 2} := by
    ext e
    fin_cases e <;> simp [mem_verticalEdges, step_def,
      maximalDyckPath_of_ne_zero (d₁ := 1) 2 (by decide), List.range_succ]
  have hI (e e' : Edge 1 2) :
      cyclicIcc e e' = ({k | (k - e).val ≤ (e' - e).val} : Finset (Edge 1 2)) := by
    ext k
    simp only [mem_cyclicIcc, mem_filter, mem_univ, true_and]
  let γ : Edge 1 2 → ℕ := fun e ↦ if e.val = 1 then 0 else 1
  have hp : verticalTotal γ = 1 := by
    rw [verticalTotal_eq, hV]
    decide
  have hq : horizontalTotal γ = 1 := by
    rw [horizontalTotal_eq, hH]
    decide
  have hc : Compatible γ := by
    simp only [compatible_iff, verticalBalanced_iff_card_eq_sum,
      horizontalBalanced_iff_card_eq_sum, hH, hV, hI]
    decide
  have hs : horizontalSupport γ ⊆ totalVerticalShadow γ := by
    intro k hk
    have hk0 : k = 0 := by
      simpa only [hH, mem_singleton] using (mem_horizontalSupport γ).mp hk |>.1
    subst k
    simp only [mem_totalVerticalShadow, mem_verticalShadow,
      horizontalBalanced_iff_card_eq_sum, hH, hV, hI]
    decide
  have hn : ¬verticalSupport γ ⊆ totalHorizontalShadow γ := by
    intro hsub
    have hm : (2 : Edge 1 2) ∈ verticalSupport γ := by
      rw [mem_verticalSupport, hV]
      decide
    have hnot : (2 : Edge 1 2) ∉ totalHorizontalShadow γ := by
      simp only [mem_totalHorizontalShadow, mem_horizontalShadow,
        verticalBalanced_iff_card_eq_sum, hH, hV, hI]
      decide
    exact hnot (hsub hm)
  have hshadow : Shadowed γ := (shadowed_iff γ).mpr ⟨hc, Or.inl hs⟩
  have ht : Tight γ := by
    rw [tight_iff]
    refine ⟨hshadow, ?_, ?_, ?_⟩
    · rw [hp]
    · rw [hq]
      decide
    · rw [hp, hq]
      decide
  exact ⟨γ, hp, hq, hshadow, ht, hn⟩

/-- On the path `UUD`, grading the first and last edges by one gives a nondegenerate
shadowed, tight grading. Both totals are one, and `p d₂ - q d₁ = -1`. Here the vertical
support lies in the total horizontal shadow; the horizontal support does not lie in
the vertical shadow. Thus this example uses the other alternative in `Shadowed`. -/
theorem exists_tight_two_one :
    ∃ γ : Edge 2 1 → ℕ, verticalTotal γ = 1 ∧ horizontalTotal γ = 1 ∧
      Shadowed γ ∧ Tight γ ∧ ¬horizontalSupport γ ⊆ totalVerticalShadow γ := by
  have hH : horizontalEdges 2 1 = {0, 1} := by
    ext e
    fin_cases e <;> simp [mem_horizontalEdges, step_def,
      maximalDyckPath_of_ne_zero (d₁ := 2) 1 (by decide), List.range_succ]
  have hV : verticalEdges 2 1 = {2} := by
    ext e
    fin_cases e <;> simp [mem_verticalEdges, step_def,
      maximalDyckPath_of_ne_zero (d₁ := 2) 1 (by decide), List.range_succ]
  have hI (e e' : Edge 2 1) :
      cyclicIcc e e' = ({k | (k - e).val ≤ (e' - e).val} : Finset (Edge 2 1)) := by
    ext k
    simp only [mem_cyclicIcc, mem_filter, mem_univ, true_and]
  let γ : Edge 2 1 → ℕ := fun e ↦ if e.val = 1 then 0 else 1
  have hp : verticalTotal γ = 1 := by
    rw [verticalTotal_eq, hV]
    decide
  have hq : horizontalTotal γ = 1 := by
    rw [horizontalTotal_eq, hH]
    decide
  have hc : Compatible γ := by
    simp only [compatible_iff, verticalBalanced_iff_card_eq_sum,
      horizontalBalanced_iff_card_eq_sum, hH, hV, hI]
    decide
  have hs : verticalSupport γ ⊆ totalHorizontalShadow γ := by
    intro k hk
    have hk2 : k = 2 := by
      simpa only [hV, mem_singleton] using (mem_verticalSupport γ).mp hk |>.1
    subst k
    simp only [mem_totalHorizontalShadow, mem_horizontalShadow,
      verticalBalanced_iff_card_eq_sum, hH, hV, hI]
    decide
  have hn : ¬horizontalSupport γ ⊆ totalVerticalShadow γ := by
    intro hsub
    have hm : (0 : Edge 2 1) ∈ horizontalSupport γ := by
      rw [mem_horizontalSupport, hH]
      decide
    have hnot : (0 : Edge 2 1) ∉ totalVerticalShadow γ := by
      simp only [mem_totalVerticalShadow, mem_verticalShadow,
        horizontalBalanced_iff_card_eq_sum, hH, hV, hI]
      decide
    exact hnot (hsub hm)
  have hshadow : Shadowed γ := (shadowed_iff γ).mpr ⟨hc, Or.inr hs⟩
  have ht : Tight γ := by
    rw [tight_iff]
    refine ⟨hshadow, ?_, ?_, ?_⟩
    · rw [hp]
      decide
    · rw [hq]
    · rw [hp, hq]
      decide
  exact ⟨γ, hp, hq, hshadow, ht, hn⟩

section Truncation

/-- Horizontal balance on `ev` only depends on the vertical grades on `ev`. -/
theorem horizontalBalanced_congr {γ γ' : Edge d₁ d₂ → ℕ} {e v : Edge d₁ d₂}
    (hV : ∀ k ∈ cyclicIcc e v ∩ verticalEdges d₁ d₂, γ k = γ' k) :
    HorizontalBalanced γ e v ↔ HorizontalBalanced γ' e v := by
  rw [horizontalBalanced_iff_card_eq_sum, horizontalBalanced_iff_card_eq_sum, sum_congr rfl hV]

/-- Horizontal balance only depends on the vertical grades. -/
theorem horizontalBalanced_congr' {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k) (e v : Edge d₁ d₂) :
    HorizontalBalanced γ e v ↔ HorizontalBalanced γ' e v :=
  horizontalBalanced_congr fun k hk ↦ hV k (mem_inter.mp hk).2

/-- Vertical balance on `he` only depends on the horizontal grades on `he`. -/
theorem verticalBalanced_congr' {γ γ' : Edge d₁ d₂ → ℕ} {h e : Edge d₁ d₂}
    (hH : ∀ k ∈ cyclicIcc h e ∩ horizontalEdges d₁ d₂, γ k = γ' k) :
    VerticalBalanced γ h e ↔ VerticalBalanced γ' h e := by
  rw [verticalBalanced_iff_card_eq_sum, verticalBalanced_iff_card_eq_sum, sum_congr rfl hH]

/-- Vertical balance only depends on the horizontal grades. -/
theorem verticalBalanced_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k) (h e : Edge d₁ d₂) :
    VerticalBalanced γ h e ↔ VerticalBalanced γ' h e :=
  verticalBalanced_congr' fun k hk ↦ hH k (mem_inter.mp hk).2

/-- The local horizontal shadows only depend on the horizontal grades. -/
theorem horizontalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k) (h : Edge d₁ d₂) :
    horizontalShadow γ h = horizontalShadow γ' h := by
  ext k
  simp only [mem_horizontalShadow, verticalBalanced_congr hH]

/-- The local vertical shadows only depend on the vertical grades. -/
theorem verticalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k) (v : Edge d₁ d₂) :
    verticalShadow γ v = verticalShadow γ' v := by
  ext k
  simp only [mem_verticalShadow, horizontalBalanced_congr' hV]

theorem totalHorizontalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k) :
    totalHorizontalShadow γ = totalHorizontalShadow γ' := by
  ext k
  simp only [mem_totalHorizontalShadow, horizontalShadow_congr hH]

theorem totalVerticalShadow_congr {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k) :
    totalVerticalShadow γ = totalVerticalShadow γ' := by
  ext k
  simp only [mem_totalVerticalShadow, verticalShadow_congr hV]

/-- **Compatibility only sees the shadowed vertical grades.** Two gradings with the same
horizontal grades that agree on the total horizontal shadow are compatible together. -/
theorem compatible_congr_of_horizontal {γ γ' : Edge d₁ d₂ → ℕ}
    (hH : ∀ k ∈ horizontalEdges d₁ d₂, γ k = γ' k)
    (hV : ∀ k ∈ totalHorizontalShadow γ, γ k = γ' k) : Compatible γ ↔ Compatible γ' := by
  rw [compatible_iff, compatible_iff]
  refine forall₂_congr fun h hh ↦ forall₂_congr fun v hv ↦ ?_
  simp only [verticalBalanced_congr hH]
  by_cases hA : ∃ e, (e - h).val < (v - h).val ∧ VerticalBalanced γ' h e
  · exact iff_of_true (Or.inl hA) (Or.inl hA)
  have hsh : v ∈ horizontalShadow γ h := (mem_horizontalShadow γ).mpr
    ⟨hv, fun e he hb ↦ hA ⟨e, he, (verticalBalanced_congr hH h e).mp hb⟩⟩
  refine or_congr_right (exists_congr fun e ↦ and_congr_right fun he ↦
    horizontalBalanced_congr fun k hk ↦ hV k ?_)
  have hev : e ∈ cyclicIcc h v := by
    rw [mem_cyclicIcc, ← Fin.val_sub_le_val_sub_iff]
    exact he.le
  have hkv := mem_cyclicIcc.mp (cyclicIcc_subset_of_mem hev (mem_inter.mp hk).1)
  rw [mem_horizontalShadow] at hsh
  rw [mem_totalHorizontalShadow]
  exact ⟨h, hh, (mem_horizontalShadow γ).mpr
    ⟨(mem_inter.mp hk).2, fun e' he' ↦ hsh.2 e' (lt_of_lt_of_le he' hkv)⟩⟩

/-- **Compatibility only sees the shadowed horizontal grades.** Two gradings with the same
vertical grades that agree on the total vertical shadow are compatible together. -/
theorem compatible_congr_of_vertical {γ γ' : Edge d₁ d₂ → ℕ}
    (hV : ∀ k ∈ verticalEdges d₁ d₂, γ k = γ' k)
    (hH : ∀ k ∈ totalVerticalShadow γ, γ k = γ' k) : Compatible γ ↔ Compatible γ' := by
  rw [compatible_iff, compatible_iff]
  refine forall₂_congr fun h hh ↦ forall₂_congr fun v hv ↦ ?_
  simp only [horizontalBalanced_congr' hV]
  by_cases hB : ∃ e, (v - e).val < (v - h).val ∧ HorizontalBalanced γ' e v
  · exact iff_of_true (Or.inr hB) (Or.inr hB)
  have hsh : h ∈ verticalShadow γ v := (mem_verticalShadow γ).mpr
    ⟨hh, fun e he hb ↦ hB ⟨e, he, (horizontalBalanced_congr' hV e v).mp hb⟩⟩
  refine or_congr_left (exists_congr fun e ↦ and_congr_right fun he ↦
    verticalBalanced_congr' fun k hk ↦ hH k ?_)
  have hkv : (v - k).val ≤ (v - h).val := by
    rw [Fin.val_sub_le_val_sub_iff]
    exact (mem_cyclicIcc.mp (mem_inter.mp hk).1).trans he.le
  rw [mem_verticalShadow] at hsh
  rw [mem_totalVerticalShadow]
  exact ⟨v, hv, (mem_verticalShadow γ).mpr
    ⟨(mem_inter.mp hk).2, fun e' he' ↦ hsh.2 e' (lt_of_lt_of_le he' hkv)⟩⟩

end Truncation

section Weights

variable (d₁ d₂) in
/-- Gradings with vertical grades at most `ℓ₁` and horizontal grades at most `ℓ₂`. -/
def gradings (ℓ₁ ℓ₂ : ℕ) : Finset (Edge d₁ d₂ → ℕ) :=
  Fintype.piFinset fun e ↦ range ((if step e = D then ℓ₁ else ℓ₂) + 1)

@[simp]
theorem mem_gradings {ℓ₁ ℓ₂ : ℕ} {γ : Edge d₁ d₂ → ℕ} :
    γ ∈ gradings d₁ d₂ ℓ₁ ℓ₂ ↔ ∀ e, γ e ≤ if step e = D then ℓ₁ else ℓ₂ := by
  simp [gradings]

variable {S : Type*} [CommSemiring S] (P₁ P₂ : S[X])

/-- The weight `∏_v [x^{γ_V(v)}] P₁ ∏_h [y^{γ_H(h)}] P₂` of a grading. -/
def weight (γ : Edge d₁ d₂ → ℕ) : S :=
  (∏ v ∈ verticalEdges d₁ d₂, P₁.coeff (γ v)) * ∏ h ∈ horizontalEdges d₁ d₂, P₂.coeff (γ h)

/-- The grading weight is the product of the edge coefficients. -/
theorem weight_def (γ : Edge d₁ d₂ → ℕ) :
    weight P₁ P₂ γ =
      (∏ v ∈ verticalEdges d₁ d₂, P₁.coeff (γ v)) *
        ∏ h ∈ horizontalEdges d₁ d₂, P₂.coeff (γ h) := (rfl)

variable (d₁ d₂) in
/-- The weight sum of all compatible gradings with totals `(p, q)`. -/
def compatibleSum (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q, weight P₁ P₂ γ

theorem compatibleSum_def (p q : ℕ) :
    compatibleSum d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q, weight P₁ P₂ γ :=
  (rfl)

variable (d₁ d₂) in
/-- `C₊(p, q)`: the weight sum of the compatible gradings with totals `(p, q)` whose nonzero
vertical support lies in the total horizontal shadow. -/
def cplus (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q ∧ verticalSupport γ ⊆ totalHorizontalShadow γ, weight P₁ P₂ γ

variable (d₁ d₂) in
/-- `C₋(p, q)`: the weight sum of the compatible gradings with totals `(p, q)` whose nonzero
horizontal support lies in the total vertical shadow. -/
def cminus (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q ∧ horizontalSupport γ ⊆ totalVerticalShadow γ, weight P₁ P₂ γ

theorem cplus_def (p q : ℕ) :
    cplus d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q ∧ verticalSupport γ ⊆ totalHorizontalShadow γ, weight P₁ P₂ γ :=
  (rfl)

theorem cminus_def (p q : ℕ) :
    cminus d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Compatible γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q ∧ horizontalSupport γ ⊆ totalVerticalShadow γ, weight P₁ P₂ γ :=
  (rfl)

/-- The zero grading has weight one when both constant coefficients are one. -/
@[simp]
theorem weight_zero (h₁ : P₁.coeff 0 = 1) (h₂ : P₂.coeff 0 = 1) :
    weight P₁ P₂ (0 : Edge d₁ d₂ → ℕ) = 1 := by
  simp [weight, h₁, h₂]

/-- The only grading with totals `(0, 0)` satisfying a condition true of the zero grading. -/
private theorem filter_totals_zero {ℓ₁ ℓ₂ : ℕ} (C : (Edge d₁ d₂ → ℕ) → Prop) [DecidablePred C]
    (hC : C 0) :
    {γ ∈ gradings d₁ d₂ ℓ₁ ℓ₂ | Compatible γ ∧ verticalTotal γ = 0 ∧ horizontalTotal γ = 0 ∧
      C γ} = {0} := by
  ext γ
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, -, h₁, h₂, -⟩
    exact eq_zero_of_totals_eq_zero γ h₁ h₂
  · rintro rfl
    refine ⟨mem_gradings.mpr fun e ↦ Nat.zero_le _, compatible_zero, ?_, ?_, hC⟩
    · simp [verticalTotal]
    · simp [horizontalTotal]

/-- `C₊(0, 0) = 1` when both constant coefficients are one. -/
@[simp]
theorem cplus_zero_zero (h₁ : P₁.coeff 0 = 1) (h₂ : P₂.coeff 0 = 1) :
    cplus d₁ d₂ P₁ P₂ 0 0 = 1 := by
  rw [cplus, filter_totals_zero _ (by simp [verticalSupport]), Finset.sum_singleton,
    weight_zero _ _ h₁ h₂]

/-- `C₋(0, 0) = 1` when both constant coefficients are one. -/
@[simp]
theorem cminus_zero_zero (h₁ : P₁.coeff 0 = 1) (h₂ : P₂.coeff 0 = 1) :
    cminus d₁ d₂ P₁ P₂ 0 0 = 1 := by
  rw [cminus, filter_totals_zero _ (by simp [horizontalSupport]), Finset.sum_singleton,
    weight_zero _ _ h₁ h₂]

variable (d₁ d₂) in
/-- The weight sum of the shadowed gradings with totals `(p, q)`. -/
def shadowedSum (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Shadowed γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q, weight P₁ P₂ γ

theorem shadowedSum_def (p q : ℕ) :
    shadowedSum d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Shadowed γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q, weight P₁ P₂ γ :=
  (rfl)

variable (d₁ d₂) in
/-- The weight sum of the tight gradings with totals `(p, q)`. -/
def tightSum (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Tight γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q, weight P₁ P₂ γ

theorem tightSum_def (p q : ℕ) :
    tightSum d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Tight γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q, weight P₁ P₂ γ :=
  (rfl)

/-- The shadowed sum at `(0, 0)` is `1` when both constant coefficients are one. -/
@[simp]
theorem shadowedSum_zero_zero (h₁ : P₁.coeff 0 = 1) (h₂ : P₂.coeff 0 = 1) :
    shadowedSum d₁ d₂ P₁ P₂ 0 0 = 1 := by
  rw [shadowedSum, filter_congr (q := fun γ ↦ Compatible γ ∧ verticalTotal γ = 0 ∧
      horizontalTotal γ = 0 ∧ (horizontalSupport γ ⊆ totalVerticalShadow γ ∨
        verticalSupport γ ⊆ totalHorizontalShadow γ)) fun γ _ ↦ by rw [shadowed_iff]; tauto,
    filter_totals_zero _ (Or.inl (by simp [horizontalSupport])), Finset.sum_singleton,
    weight_zero _ _ h₁ h₂]

/-- The tight sum is the shadowed sum when `p ≤ d₁`, `q ≤ d₂` and `|p d₂ - q d₁| = gcd(p, q)`. -/
theorem tightSum_eq_shadowedSum {p q : ℕ} (hp : p ≤ d₁) (hq : q ≤ d₂)
    (hpq : ((p * d₂ : ℤ) - q * d₁).natAbs = p.gcd q) :
    tightSum d₁ d₂ P₁ P₂ p q = shadowedSum d₁ d₂ P₁ P₂ p q := by
  rw [tightSum_def, shadowedSum_def]
  refine sum_congr (filter_congr fun γ _ ↦ ?_) fun _ _ ↦ rfl
  rw [tight_iff]
  constructor
  · exact fun ⟨⟨hs, _⟩, hγ⟩ ↦ ⟨hs, hγ⟩
  · rintro ⟨hs, rfl, rfl⟩
    exact ⟨⟨hs, hp, hq, hpq⟩, rfl, rfl⟩

/-- The tight sum vanishes unless `p ≤ d₁`, `q ≤ d₂` and `|p d₂ - q d₁| = gcd(p, q)`. -/
@[simp]
theorem tightSum_eq_zero {p q : ℕ}
    (h : ¬(p ≤ d₁ ∧ q ≤ d₂ ∧ ((p * d₂ : ℤ) - q * d₁).natAbs = p.gcd q)) :
    tightSum d₁ d₂ P₁ P₂ p q = 0 := by
  rw [tightSum_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, tight_iff]
  rintro ⟨-, ⟨-, hp, hq, hpq⟩, rfl, rfl⟩
  exact h ⟨hp, hq, hpq⟩

end Weights

/-- A grading is compatible exactly when no horizontal edge and vertical edge lie in each
other's local shadows. -/
theorem compatible_iff_forall_not_mem_shadow (γ : Edge d₁ d₂ → ℕ) :
    Compatible γ ↔ ∀ h ∈ horizontalEdges d₁ d₂, ∀ v ∈ verticalEdges d₁ d₂,
      ¬(v ∈ horizontalShadow γ h ∧ h ∈ verticalShadow γ v) := by
  rw [compatible_iff]
  refine forall₂_congr fun h hh ↦ forall₂_congr fun v hv ↦ ?_
  rw [mem_horizontalShadow, mem_verticalShadow]
  simp only [hh, hv, true_and, not_and_or, not_forall, not_not, exists_prop]

end Mei.MaximalDyckPath
