/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Faces of polyhedra are determined by active inequalities

A nonempty convex extreme subset of a polyhedron is obtained by making a
subset of any finite defining family of inequalities equalities. Consequently
a polyhedron has only finitely many convex extreme subsets and exposed subsets.
The argument allows unbounded polyhedra, lineality and redundant inequalities.
-/

public section

open Set Filter Topology

variable {V ι : Type*}

section Algebra

variable [AddCommGroup V] [Module ℝ V]

namespace Convex

/-- A nonempty convex set has a point where each member of a finite family of
nonpositive affine functions vanishes exactly when it vanishes on the whole set. -/
theorem exists_mem_zero_iff_forall {F : Set V} (hF : Convex ℝ F) (hne : F.Nonempty)
    [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ)) (hg : ∀ j, ∀ x ∈ F, g j x ≤ 0) :
    ∃ p ∈ F, ∀ j, g j p = 0 ↔ ∀ x ∈ F, g j x = 0 := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ p ∈ F, ∀ j ∈ s, g j p = 0 ↔ ∀ x ∈ F, g j x = 0 by
    obtain ⟨p, hp, h⟩ := this Finset.univ
    exact ⟨p, hp, fun j => h j (Finset.mem_univ j)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, by simp⟩
  | @insert j s hjs ih =>
    obtain ⟨p, hp, hps⟩ := ih
    by_cases hj : ∀ x ∈ F, g j x = 0
    · refine ⟨p, hp, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact iff_of_true (hj p hp) hj
      · exact hps k hk
    · push Not at hj
      obtain ⟨q, hq, hqj⟩ := hj
      refine ⟨AffineMap.lineMap p q (1 / 2 : ℝ), hF.lineMap_mem hp hq (by norm_num), ?_⟩
      have hmid (k : ι) :
          g k (AffineMap.lineMap p q (1 / 2 : ℝ)) = (g k p + g k q) / 2 := by
        rw [(g k).apply_lineMap, AffineMap.lineMap_apply_ring]
        ring
      intro k hk
      constructor
      · intro hzero x hx
        have hpzero : g k p = 0 := by
          have h₁ := hg k p hp
          have h₂ := hg k q hq
          rw [hmid] at hzero
          linarith
        rcases Finset.mem_insert.mp hk with rfl | hk
        · have h₁ := hg k p hp
          have h₂ := hg k q hq
          have hmidzero := hzero
          rw [hmid] at hmidzero
          exfalso
          exact hqj (by linarith)
        · exact (hps k hk).mp hpzero x hx
      · intro hall
        rw [hmid, hall p hp, hall q hq]
        norm_num

end Convex

namespace AffineMap

/-- Matching the active inequalities at a point permits a small extrapolation
away from the matching point while preserving every defining inequality. -/
theorem exists_pos_lineMap_neg_forall_le [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ))
    {p x : V} (hp : ∀ j, g j p ≤ 0) (hx : ∀ j, g j p = 0 → g j x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j, g j (AffineMap.lineMap p x (-ε)) ≤ 0 := by
  have heach (j : ι) : ∀ᶠ ε : ℝ in 𝓝 0, g j (AffineMap.lineMap p x (-ε)) ≤ 0 := by
    by_cases hj : g j p = 0
    · exact Eventually.of_forall fun ε => by
        rw [(g j).apply_lineMap, AffineMap.lineMap_apply_ring, hj, hx j hj]
        simp
    · have hjlt : g j p < 0 := lt_of_le_of_ne (hp j) hj
      have hval (ε : ℝ) : g j (AffineMap.lineMap p x (-ε)) =
          (1 + ε) * g j p - ε * g j x := by
        rw [(g j).apply_lineMap, AffineMap.lineMap_apply_ring]
        ring
      have hc : Continuous (fun ε : ℝ => (1 + ε) * g j p - ε * g j x) :=
        ((continuous_const.add continuous_id).mul continuous_const).sub
          (continuous_id.mul continuous_const)
      have hlim : Tendsto (fun ε : ℝ => (1 + ε) * g j p - ε * g j x)
          (𝓝 0) (𝓝 (g j p)) := by simpa using hc.tendsto 0
      have he := hlim.eventually (eventually_lt_nhds hjlt)
      exact he.mono fun ε h => by rw [hval]; exact h.le
  have hall := eventually_all.mpr heach
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

end AffineMap

namespace IsExtreme

/-- A nonempty convex extreme subset of a finite intersection of affine
halfspaces is obtained by imposing equality in some of the defining rows. -/
theorem eq_setOf_active [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ)) {F : Set V}
    (hF : IsExtreme ℝ {x | ∀ j, g j x ≤ 0} F) (hconv : Convex ℝ F)
    (hne : F.Nonempty) :
    ∃ I : Finset ι, F = {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨p, hp, hpoint⟩ := hconv.exists_mem_zero_iff_forall hne g
    (fun j x hx => hF.subset hx j)
  let I := Finset.univ.filter (fun j => g j p = 0)
  refine ⟨I, Set.ext fun x => ⟨?_, ?_⟩⟩
  · intro hx
    refine ⟨hF.subset hx, ?_⟩
    intro j hj
    exact (hpoint j).mp (Finset.mem_filter.mp hj).2 x hx
  · rintro ⟨hx, hxI⟩
    obtain ⟨ε, hε, he⟩ := AffineMap.exists_pos_lineMap_neg_forall_le g
      (hF.subset hp) (fun j hj => hxI j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
    apply hF.left_mem_of_mem_openSegment hx he hp
    have hden : 0 < 1 + ε := by linarith
    refine ⟨ε / (1 + ε), 1 / (1 + ε), div_pos hε hden, div_pos zero_lt_one hden, ?_, ?_⟩
    · field_simp
      ring
    · rw [AffineMap.lineMap_apply_module, smul_add, smul_smul, smul_smul]
      have hpcoef : (1 / (1 + ε)) * (1 - -ε) = 1 := by
        field_simp
        ring
      have hxcoef : ε / (1 + ε) + (1 / (1 + ε)) * -ε = 0 := by ring
      calc
        _ = ((1 / (1 + ε)) * (1 - -ε)) • p +
            (ε / (1 + ε) + (1 / (1 + ε)) * -ε) • x := by module
        _ = p := by rw [hpcoef, hxcoef]; simp

end IsExtreme

namespace Mei.Convex

/-- A finite affine halfspace presentation has only finitely many convex
extreme subsets, including the empty subset. No topology is required on the ambient module. -/
theorem finite_convex_extreme_sets [Finite ι] (g : ι → (V →ᵃ[ℝ] ℝ)) :
    {F : Set V | Convex ℝ F ∧ IsExtreme ℝ {x | ∀ j, g j x ≤ 0} F}.Finite := by
  classical
  let := Fintype.ofFinite ι
  let faces : Finset ι → Set V :=
    fun I => {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0}
  apply ((Set.finite_range faces).insert ∅).subset
  intro F ⟨hconv, hF⟩
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact Set.mem_insert _ _
  · obtain ⟨I, hI⟩ := hF.eq_setOf_active g hconv hne
    exact Set.mem_insert_of_mem _ ⟨I, hI.symm⟩

end Mei.Convex

end Algebra

section Topology

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace IsExposed

/-- Every nonempty exposed subset of a polyhedron is an active-constraint face. -/
theorem eq_setOf_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) {F : Set V}
    (hF : IsExposed ℝ {x | ∀ j, g j x ≤ 0} F) (hne : F.Nonempty) :
    ∃ I : Finset ι, F = {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} :=
  hF.isExtreme.eq_setOf_active (fun j => (g j).toAffineMap)
    (hF.convex (TauCeti.isConvexPolyhedron_setOf_forall g).convex) hne

end IsExposed

namespace Mei.Convex

/-- A finite collection of active equalities exposes a face: the sum of their
affine functions is maximized exactly when every selected nonpositive row is zero. -/
theorem isExposed_setOf_active (g : ι → (V →ᴬ[ℝ] ℝ)) (I : Finset ι) :
    IsExposed ℝ {x | ∀ j, g j x ≤ 0}
      {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} := by
  classical
  intro hne
  obtain ⟨p, hp, hpI⟩ := hne
  let l : V →L[ℝ] ℝ := ∑ j ∈ I, (g j).contLinear
  have hl (x : V) : l x = (∑ j ∈ I, g j x) - ∑ j ∈ I, g j 0 := by
    dsimp [l]
    rw [sum_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simpa using (g j).contLinear_apply_vsub x 0
  have hpzero : ∑ j ∈ I, g j p = 0 := Finset.sum_eq_zero hpI
  refine ⟨l, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨hx, hxI⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [hl y, hl x, Finset.sum_eq_zero hxI]
    have hyzero : ∑ j ∈ I, g j y ≤ 0 := Finset.sum_nonpos fun j _ => hy j
    linarith
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, ?_⟩
    have hsum : ∑ j ∈ I, g j x = 0 := by
      have hle : ∑ j ∈ I, g j x ≤ 0 := Finset.sum_nonpos fun j _ => hx j
      have hge := hmax p hp
      rw [hl p, hl x, hpzero] at hge
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hx j)).mp hsum

/-- Active-constraint faces are polyhedra: each equality is imposed by the
original nonpositive row and its negation. -/
theorem isConvexPolyhedron_setOf_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) (I : Finset ι) :
    TauCeti.IsConvexPolyhedron {x | (∀ j, g j x ≤ 0) ∧ ∀ j ∈ I, g j x = 0} := by
  have h := (TauCeti.isConvexPolyhedron_setOf_forall g).inter
    (TauCeti.isConvexPolyhedron_setOf_forall (fun j : I => -g j.val))
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx, hxI⟩
    exact ⟨hx, fun j => by simp [hxI j.val j.property]⟩
  · rintro ⟨hx, hxI⟩
    refine ⟨hx, fun j hj => le_antisymm (hx j) ?_⟩
    have hnonneg := hxI ⟨j, hj⟩
    simpa using hnonneg

/-- A finite affine halfspace presentation has only finitely many exposed subsets. -/
theorem finite_exposed_sets [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) :
    {F : Set V | IsExposed ℝ {x | ∀ j, g j x ≤ 0} F}.Finite :=
  (finite_convex_extreme_sets (fun j => (g j).toAffineMap)).subset fun _ hF =>
    ⟨hF.convex (TauCeti.isConvexPolyhedron_setOf_forall g).convex, hF.isExtreme⟩

end Mei.Convex

namespace IsExtreme

/-- Every convex extreme subset of a polyhedron is exposed, including the empty subset. -/
theorem isExposed_of_isConvexPolyhedron {P F : Set V} (hF : IsExtreme ℝ P F)
    (hP : TauCeti.IsConvexPolyhedron P) (hconv : Convex ℝ F) : IsExposed ℝ P F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact isExposed_empty
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  obtain ⟨I, rfl⟩ := hF.eq_setOf_active (fun j => (g j).toAffineMap) hconv hne
  exact Mei.Convex.isExposed_setOf_active g I

/-- Every convex extreme subset of a polyhedron is itself a convex polyhedron. -/
theorem isConvexPolyhedron {P F : Set V} (hF : IsExtreme ℝ P F)
    (hP : TauCeti.IsConvexPolyhedron P) (hconv : Convex ℝ F) :
    TauCeti.IsConvexPolyhedron F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · have h := TauCeti.isConvexPolyhedron_setOf_forall
      (fun _ : Fin 1 => ContinuousAffineMap.const ℝ V 1)
    convert h using 1
    ext x
    norm_num
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  obtain ⟨I, rfl⟩ := hF.eq_setOf_active (fun j => (g j).toAffineMap) hconv hne
  exact Mei.Convex.isConvexPolyhedron_setOf_active g I

end IsExtreme

namespace TauCeti.IsConvexPolyhedron

/-- An arbitrary convex polyhedron has finitely many convex extreme subsets. -/
theorem finite_convex_extreme_sets {P : Set V} (hP : TauCeti.IsConvexPolyhedron P) :
    {F : Set V | Convex ℝ F ∧ IsExtreme ℝ P F}.Finite := by
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  exact Mei.Convex.finite_convex_extreme_sets (fun j => (g j).toAffineMap)

/-- An arbitrary convex polyhedron has finitely many exposed subsets. -/
theorem finite_exposed_sets {P : Set V} (hP : TauCeti.IsConvexPolyhedron P) :
    {F : Set V | IsExposed ℝ P F}.Finite := by
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  exact Mei.Convex.finite_exposed_sets g

end TauCeti.IsConvexPolyhedron

end Topology
