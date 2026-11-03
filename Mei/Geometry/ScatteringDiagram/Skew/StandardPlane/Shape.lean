/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Basic
public import Mei.Data.List.Chain
public import Mei.Data.List.Filter
public import Mei.Data.List.Replicate
public import Mei.LinearAlgebra.SesquilinearForm.Alternating

/-!
# Ordered lists of plane degrees

A list of nonzero plane degrees whose adjacent pairs are ordered, `{m, m'} ≥ 0`, is sorted by
angle: the degrees on the ray of `e₁` come first, then those in the open quadrant, and the
degrees on the ray of `e₂` come last. If the boundary degrees of such a list are a permutation
of `e₂^A e₁^B`, the list is `e₁^B I e₂^A` for a list `I` of degrees in the open quadrant.
-/

public section

namespace Mei.StandardPlane

variable {w : Weight}

namespace PlaneDegree

/-- Every plane degree is a nonnegative combination of the two basis vectors. -/
theorem vec_mem_closure (m : PlaneDegree w) :
    m.vec ∈ AddSubmonoid.closure {(e₁ w).vec, (e₂ w).vec} := by
  refine (AddSubmonoid.mem_closure_pair _ _ _).mpr ⟨m.fst.toNat, m.snd.toNat, ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
    simp [Int.toNat_of_nonneg m.fst_nonneg, Int.toNat_of_nonneg m.snd_nonneg]

/-- The angular order `0 ≤ {m, m'}` is transitive on nonzero plane degrees. -/
theorem not_inverted_trans {a b c : PlaneDegree w} (hab : ¬ Inverted a b) (hbc : ¬ Inverted b c) :
    ¬ Inverted a c := by
  rw [inverted_iff_coefficientForm_lt] at hab hbc ⊢
  rw [not_lt] at hab hbc ⊢
  exact LinearMap.IsAlt.nonneg_trans_of_mem_closure_pair (E.isAlt_coefficientForm ℚ)
    a.vec_mem_closure b.vec_mem_closure c.vec_mem_closure b.ne_zero hab hbc

/-- The position of a plane degree in the angular order: `0` on the ray of `e₁`, `2` on the ray
of `e₂` and `1` in the open quadrant. -/
private def rank (m : PlaneDegree w) : ℕ := if m.snd = 0 then 0 else if m.fst = 0 then 2 else 1

private theorem rank_le_two (m : PlaneDegree w) : m.rank ≤ 2 := by
  unfold rank
  split_ifs <;> omega

private theorem rank_eq_zero_iff (m : PlaneDegree w) : m.rank = 0 ↔ m.snd = 0 := by
  unfold rank
  split_ifs <;> simp_all

private theorem rank_eq_two_iff (m : PlaneDegree w) : m.rank = 2 ↔ m.snd ≠ 0 ∧ m.fst = 0 := by
  unfold rank
  split_ifs <;> simp_all

private theorem rank_eq_one_iff (m : PlaneDegree w) : m.rank = 1 ↔ ¬ m.Boundary := by
  unfold rank
  rw [boundary_iff]
  split_ifs <;> simp_all

/-- Ordered pairs of plane degrees do not decrease the rank. -/
private theorem rank_le_of_not_inverted {a b : PlaneDegree w} (h : ¬ Inverted a b) :
    a.rank ≤ b.rank := by
  rw [inverted_iff] at h
  push Not at h
  have ha1 := a.fst_nonneg
  have ha2 := a.snd_nonneg
  have hb1 := b.fst_nonneg
  have hb2 := b.snd_nonneg
  have hbpos : b.snd = 0 → 0 < b.fst := fun e => by
    rcases b.fst_ne_zero_or with h | h
    · exact lt_of_le_of_ne hb1 (Ne.symm h)
    · exact absurd e h
  by_contra hlt
  push Not at hlt
  by_cases hb : b.snd = 0
  · have hr : b.rank = 0 := (rank_eq_zero_iff b).mpr hb
    have ha : a.snd ≠ 0 := fun e => by
      have := (rank_eq_zero_iff a).mpr e
      omega
    have := mul_pos (lt_of_le_of_ne ha2 (Ne.symm ha)) (hbpos hb)
    rw [hb] at h
    nlinarith
  · by_cases hb' : b.fst = 0
    · have : b.rank = 2 := (rank_eq_two_iff b).mpr ⟨hb, hb'⟩
      have := a.rank_le_two
      omega
    · have hr : b.rank = 1 := by
        unfold rank
        simp [hb, hb']
      have ha : a.rank = 2 := by
        have := a.rank_le_two
        omega
      obtain ⟨ha1', ha2'⟩ := (rank_eq_two_iff a).mp ha
      have := mul_pos (lt_of_le_of_ne ha2 (Ne.symm ha1')) (lt_of_le_of_ne hb1 (Ne.symm hb'))
      rw [ha2'] at h
      nlinarith

end PlaneDegree

/-- **Shape of an ordered list.** An ordered list of plane degrees whose boundary degrees are a
permutation of `e₂^A e₁^B` is `e₁^B I e₂^A`, where `I` consists of degrees of the open
quadrant. -/
theorem exists_eq_append_of_isChain (A B : ℕ) (l : List (PlaneDegree w))
    (hl : l.IsChain fun a b => ¬ PlaneDegree.Inverted a b)
    (hperm : (l.filter fun m => decide m.Boundary).Perm
      (List.replicate A (PlaneDegree.e₂ w) ++ List.replicate B (PlaneDegree.e₁ w))) :
    ∃ I : List (PlaneDegree w),
      l = List.replicate B (PlaneDegree.e₁ w) ++ I ++ List.replicate A (PlaneDegree.e₂ w) ∧
      ∀ m ∈ I, ¬ m.Boundary := by
  classical
  have hpw : l.Pairwise fun a b => ¬ PlaneDegree.Inverted a b :=
    hl.pairwise_of_forall_mem (p := fun _ => True) (fun _ _ => trivial)
      fun _ _ _ _ _ _ => PlaneDegree.not_inverted_trans
  have hsplit := List.eq_filter_append_of_pairwise PlaneDegree.rank PlaneDegree.rank_le_two l
    (hpw.imp fun h => PlaneDegree.rank_le_of_not_inverted h)
  obtain ⟨f₀, f₁, f₂, rfl, h₀, h₁, h₂⟩ : ∃ f₀ f₁ f₂ : List (PlaneDegree w), l = f₀ ++ f₁ ++ f₂ ∧
      (∀ m ∈ f₀, m.rank = 0) ∧ (∀ m ∈ f₁, m.rank = 1) ∧ (∀ m ∈ f₂, m.rank = 2) :=
    ⟨_, _, _, hsplit, fun m hm => by simpa using (List.mem_filter.mp hm).2,
      fun m hm => by simpa using (List.mem_filter.mp hm).2,
      fun m hm => by simpa using (List.mem_filter.mp hm).2⟩
  have hb₀ : ∀ m ∈ f₀, m.Boundary := fun m hm =>
    (PlaneDegree.boundary_iff m).mpr (Or.inr ((PlaneDegree.rank_eq_zero_iff m).mp (h₀ m hm)))
  have hb₂ : ∀ m ∈ f₂, m.Boundary := fun m hm =>
    (PlaneDegree.boundary_iff m).mpr (Or.inl ((PlaneDegree.rank_eq_two_iff m).mp (h₂ m hm)).2)
  have hb₁ : ∀ m ∈ f₁, ¬ m.Boundary := fun m hm => (PlaneDegree.rank_eq_one_iff m).mp (h₁ m hm)
  refine ⟨f₁, ?_, hb₁⟩
  have hfilter : (f₀ ++ f₁ ++ f₂).filter (fun m => decide m.Boundary) = f₀ ++ f₂ := by
    have e₀ : f₀.filter (fun m => decide m.Boundary) = f₀ :=
      List.filter_eq_self.mpr (by simpa using hb₀)
    have e₁ : f₁.filter (fun m => decide m.Boundary) = [] :=
      List.filter_eq_nil_iff.mpr (by simpa using hb₁)
    have e₂ : f₂.filter (fun m => decide m.Boundary) = f₂ :=
      List.filter_eq_self.mpr (by simpa using hb₂)
    rw [List.filter_append, List.filter_append, e₀, e₁, e₂, List.append_nil]
  rw [hfilter] at hperm
  -- The elements of `f₀` and `f₂` are copies of `e₁` and `e₂`.
  have hmem : ∀ m ∈ f₀ ++ f₂, m = PlaneDegree.e₂ w ∨ m = PlaneDegree.e₁ w := fun m hm => by
    have := hperm.subset hm
    simp only [List.mem_append, List.mem_replicate] at this
    tauto
  have hf₀ : f₀ = List.replicate f₀.length (PlaneDegree.e₁ w) := by
    refine List.eq_replicate_iff.mpr ⟨rfl, fun m hm => ?_⟩
    rcases hmem m (List.mem_append_left _ hm) with rfl | rfl
    · simpa using (PlaneDegree.rank_eq_zero_iff _).mp (h₀ _ hm)
    · rfl
  have hf₂ : f₂ = List.replicate f₂.length (PlaneDegree.e₂ w) := by
    refine List.eq_replicate_iff.mpr ⟨rfl, fun m hm => ?_⟩
    rcases hmem m (List.mem_append_right _ hm) with rfl | rfl
    · rfl
    · simpa using ((PlaneDegree.rank_eq_two_iff _).mp (h₂ _ hm)).2
  have hne : PlaneDegree.e₁ w ≠ PlaneDegree.e₂ w := fun h => by
    simpa using congrArg PlaneDegree.fst h
  have hperm' : (List.replicate f₀.length (PlaneDegree.e₁ w) ++
      List.replicate f₂.length (PlaneDegree.e₂ w)).Perm
      (List.replicate A (PlaneDegree.e₂ w) ++ List.replicate B (PlaneDegree.e₁ w)) := by
    rw [← hf₀, ← hf₂]
    exact hperm
  obtain ⟨hB, hA⟩ := List.eq_and_eq_of_perm_replicate_append_replicate hne hperm'
  subst hA hB
  rw [← hf₀, ← hf₂]

end Mei.StandardPlane
