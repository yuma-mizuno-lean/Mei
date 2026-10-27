/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Face
public import Mei.Analysis.Convex.Exposed

/-!
# A second facet at a polyhedral ridge

Every nonempty ridge in a facet of a convex polyhedron is also contained in a
different facet. The two facets meet exactly in the ridge. This supplies the
existence of the second incidence needed to cancel iterated signed boundaries.
Unbounded polyhedra, lower-dimensional affine spans, lineality and redundant
inequalities are allowed.

The construction uses `IsExposed.eq_setOf_active` and
`Convex.exists_mem_zero_iff_forall` to work with the active rows at a point of
the ridge. A minimum of finitely many ratios produces another active face
containing the ridge and incomparable with the first facet. Dimension then
identifies it as a facet, using `IsExposed.eq_of_finrank_vectorSpan_eq`.
-/

public section

open Set Module

namespace IsExposed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P F Q : Set V}

/-- Given a nonempty face inside a proper exposed face of a polyhedron and a
point of the larger face outside the smaller one, there is an exposed face
containing the smaller face, missing that point, and extending outside the
larger face. No dimension hypothesis is needed. -/
theorem exists_incomparable_superset_of_isConvexPolyhedron
    (hF : IsExposed ℝ P F) (hP : TauCeti.IsConvexPolyhedron P)
    (hQ : IsExposed ℝ P Q) (hne : Q.Nonempty) (hQF : Q ⊆ F)
    (hproper : F ≠ P) {y : V} (hy : y ∈ F) (hyQ : y ∉ Q) :
    ∃ G, IsExposed ℝ P G ∧ Q ⊆ G ∧ y ∉ G ∧ ¬ G ⊆ F := by
  classical
  obtain ⟨m, g, hPg⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  have hrows {p : V} (hp : p ∈ P) : ∀ j, g j p ≤ 0 := by
    simpa only [hPg, mem_ofPred_eq] using hp
  -- Choose a point detecting exactly the rows that vanish on the entire face.
  obtain ⟨x, hx, hxzero⟩ := (hQ.convex hP.convex).exists_mem_zero_iff_forall hne
    (fun j => (g j).toAffineMap) (fun j p hp => hrows (hQ.subset hp) j)
  obtain ⟨I, hI⟩ := (hPg ▸ hQ).eq_setOf_active g hne
  have hS : (Finset.univ.filter (fun j => g j x = 0 ∧ g j y < 0)).Nonempty := by
    have hyP := hrows (hF.subset hy)
    have hnot : ¬ ∀ j ∈ I, g j y = 0 := by
      intro hall
      exact hyQ (hI ▸ ⟨hyP, hall⟩)
    push Not at hnot
    obtain ⟨j, hj, hjy⟩ := hnot
    have hjx := (hI ▸ hx).2 j hj
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjx,
      lt_of_le_of_ne (hyP j) hjy⟩⟩
  obtain ⟨z, hz, hzF⟩ := exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  -- Move from an exterior point backwards along the first face until an active
  -- row becomes zero, keeping all rows active at x nonpositive.
  obtain ⟨j, hj, hmin⟩ :=
    (Finset.univ.filter (fun j => g j x = 0 ∧ g j y < 0)).exists_min_image
      (fun j => g j z / g j y) hS
  obtain ⟨_, hjx, hjy⟩ := Finset.mem_filter.mp hj
  let t : ℝ := g j z / g j y
  let v : V := (z - x) - t • (y - x)
  have hval (a : Fin m) :
      (g a).contLinear v = g a z - g a x - t * (g a y - g a x) := by
    dsimp only [v]
    rw [map_sub, map_smul]
    simp only [← vsub_eq_sub, ContinuousAffineMap.contLinear_apply_vsub, smul_eq_mul]
  have hv (a : Fin m) (ha : g a x = 0) : (g a).contLinear v ≤ 0 := by
    rw [hval, ha, sub_zero, sub_zero]
    by_cases hay : g a y < 0
    · have hratio := hmin a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hay⟩)
      have hbound := (le_div_iff_of_neg hay).mp hratio
      linarith
    · have hayzero : g a y = 0 := le_antisymm (hrows (hF.subset hy) a) (le_of_not_gt hay)
      simp only [hayzero, mul_zero, sub_zero]
      exact hrows hz a
  have hvj : (g j).contLinear v = 0 := by
    rw [hval, hjx, sub_zero, sub_zero]
    dsimp only [t]
    rw [div_mul_cancel₀ _ hjy.ne]
    exact sub_self _
  obtain ⟨ε, hε, hstep⟩ := AffineMap.exists_pos_smul_add_forall_le
    (fun a => (g a).toAffineMap) (hrows (hQ.subset hx)) hv
  let p := ε • v + x
  -- A small step realizes that direction in P. The exposing functional of F
  -- stays strictly below its maximum, so the new face extends outside F.
  have hpzero : g j p = 0 := by
    simpa only [p, map_smul, hvj, smul_zero, vadd_eq_add, zero_add, hjx] using
      (g j).map_vadd x (ε • v)
  have hpF : p ∉ F := by
    obtain ⟨l, hl⟩ := hF ⟨x, hQF hx⟩
    have hxmax := hl ▸ hQF hx
    have hymax := hl ▸ hy
    have hly : l y = l x := le_antisymm (hxmax.2 y (hF.subset hy))
      (hymax.2 x (hQ.subset hx))
    have hlz : l z < l x := lt_of_le_of_ne (hxmax.2 z hz) (fun he => hzF (by
      rw [hl]
      exact ⟨hz, fun w hw => (hxmax.2 w hw).trans_eq he.symm⟩))
    have hlv : l v = l z - l x := by simp [v, map_sub, hly]
    intro hp
    have hpmax := hl ▸ hp
    have hxp := hpmax.2 x (hQ.subset hx)
    have hlp : l p = ε * (l z - l x) + l x := by
      simp only [p, map_add, map_smul, smul_eq_mul, hlv]
    nlinarith
  let G := {q | (∀ a, g a q ≤ 0) ∧ g j q = 0}
  have hG : IsExposed ℝ P G := by
    rw [hPg]
    simpa only [Finset.mem_singleton, forall_eq] using
      Mei.Convex.isExposed_setOf_active g {j}
  refine ⟨G, hG, fun q hq => ⟨hrows (hQ.subset hq), (hxzero j).mp hjx q hq⟩,
    fun hyG => hjy.ne hyG.2, fun hGF => hpF (hGF ⟨hstep, hpzero⟩)⟩

variable [FiniteDimensional ℝ V]

/-- A nonempty facet of a facet of a polyhedron is the intersection with a
second distinct facet of the original polyhedron. -/
theorem exists_second_facet_at_ridge (hF : IsExposed ℝ P F)
    (hQ : IsExposed ℝ F Q) (hP : TauCeti.IsConvexPolyhedron P) (hne : Q.Nonempty)
    (hFdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P))
    (hQdim : finrank ℝ (vectorSpan ℝ Q) + 1 = finrank ℝ (vectorSpan ℝ F)) :
    ∃ G, IsExposed ℝ P G ∧
      finrank ℝ (vectorSpan ℝ G) + 1 = finrank ℝ (vectorSpan ℝ P) ∧
      G ≠ F ∧ Q = F ∩ G := by
  have hQP := hF.trans_of_isConvexPolyhedron hQ hP
  have hproper : F ≠ P := by rintro rfl; omega
  have hQproper : Q ≠ F := by rintro rfl; omega
  obtain ⟨y, hy, hyQ⟩ := exists_of_ssubset (lt_of_le_of_ne hQ.subset hQproper)
  obtain ⟨G, hG, hQG, hyG, hGF⟩ :=
    hF.exists_incomparable_superset_of_isConvexPolyhedron hP hQP hne hQ.subset
      hproper hy hyQ
  have hGproper : G ≠ P := by rintro rfl; exact hyG (hF.subset hy)
  have hGlt : finrank ℝ (vectorSpan ℝ G) < finrank ℝ (vectorSpan ℝ P) := by
    have hle := Submodule.finrank_mono (vectorSpan_mono ℝ hG.subset)
    by_contra! hn
    exact hGproper (hG.eq_of_finrank_vectorSpan_eq (hne.mono hQG) (by omega))
  have hQlt : finrank ℝ (vectorSpan ℝ Q) < finrank ℝ (vectorSpan ℝ G) := by
    have hle := Submodule.finrank_mono (vectorSpan_mono ℝ hQG)
    by_contra! hn
    have he := (hQP.mono hG.subset hQG).eq_of_finrank_vectorSpan_eq hne (by omega)
    exact hGF (he ▸ hQ.subset)
  have hFG : Q = F ∩ G := by
    apply hQ.eq_of_subset_of_finrank_add_one hne hQdim
      ((hF.inter hG).mono hF.subset inter_subset_left)
      (subset_inter hQ.subset hQG)
    intro he
    exact hyG ((he.symm ▸ hy).2)
  exact ⟨G, hG, by omega, fun he => hGF (he ▸ Subset.rfl), hFG⟩

end IsExposed
