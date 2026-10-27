/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Face.Facet

/-!
# Local half-space models at facets

Near a relative interior point of a facet, a polyhedron agrees with the
inward closed half-space of any exposing functional, inside its affine span.
In the same neighborhood the facet agrees with the bounding hyperplane.
This supplies the local one-sided geometry for comparing a transverse
meridian with a signed boundary facet. Real offsets, unbounded polyhedra,
lower-dimensional affine spans and lineality are allowed.

These local models refine the global facet presentation of
`TauCeti.IsConvexPolyhedron.exists_facet_presentation`. The inward side is
independent of the exposing functional by the conormal proportionality of
`ContinuousLinearMap.sameRay_comp_vectorSpan_of_toExposed_eq`.
-/

public section

open Set Module Filter Topology

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {P : Set V}

/-- At a relative interior point of an exposed facet, membership in a
polyhedron is locally a single non-strict inequality inside its affine span.
The exposing functional is arbitrary. -/
theorem eventually_mem_iff_of_facet (hP : TauCeti.IsConvexPolyhedron P)
    (l : V →L[ℝ] ℝ)
    (hdim : finrank ℝ (vectorSpan ℝ (l.toExposed P)) + 1 =
      finrank ℝ (vectorSpan ℝ P))
    {p : V} (hp : p ∈ intrinsicInterior ℝ (l.toExposed P)) :
    ∀ᶠ y in 𝓝 p, y ∈ P ↔ y ∈ affineSpan ℝ P ∧ l y ≤ l p := by
  /- The facet presentation removes universally active equations and redundant non-facet rows.
  All rows active at the chosen point expose the same facet; their inward half-spaces agree
  by conormal proportionality. The remaining inequalities stay strict in a neighborhood. -/
  have hpF : p ∈ l.toExposed P := intrinsicInterior_subset hp
  have hF : IsExposed ℝ P (l.toExposed P) := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨ι, _, g, hpres, hfacets⟩ := hP.exists_facet_presentation
  have hbound (j : ι) : ∀ y ∈ P, g j y ≤ 0 := fun y hy => (hpres ▸ hy).2 j
  -- Every active row exposes this same facet, so it imposes the same side condition.
  have hactive (j : ι) (hj : g j p = 0) {y : V}
      (hyA : y ∈ affineSpan ℝ P) (hyl : l y ≤ l p) : g j y ≤ 0 := by
    let F := {x ∈ P | g j x = 0}
    have hsub : l.toExposed P ⊆ F := fun x hx =>
      ⟨hx.1, (g j).toAffineMap.eq_zero_on_of_mem_intrinsicInterior
        (fun x (hx : x ∈ l.toExposed P) => hbound j x hx.1) hp hj x hx⟩
    have hproper : F ≠ P := by
      intro he
      have hd : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P) :=
        (hfacets j).2.2
      rw [he] at hd
      omega
    have hsame : l.toExposed P = F :=
      hF.eq_of_subset_of_finrank_add_one ⟨p, hpF⟩ hdim (hfacets j).1 hsub hproper
    have hdiff (x : V) : (g j).contLinear (x - p) = g j x := by
      simpa only [vsub_eq_sub, hj, sub_zero] using (g j).contLinear_apply_vsub x p
    have hgp : p ∈ (g j).contLinear.toExposed P := by
      refine ⟨hpF.1, fun x hx => ?_⟩
      have he := hdiff x
      rw [map_sub] at he
      linarith [hbound j x hx]
    have hface : (g j).contLinear.toExposed P = F := by
      ext x
      rw [(g j).contLinear.mem_toExposed_iff_of_mem hgp]
      have he := hdiff x
      rw [map_sub] at he
      simp only [F, mem_ofPred_eq]
      constructor <;> rintro ⟨hx, hzero⟩ <;> refine ⟨hx, ?_⟩ <;> linarith
    have hr := l.sameRay_comp_vectorSpan_of_toExposed_eq (g j).contLinear
      ⟨p, hpF⟩ (hsame.trans hface.symm) hdim
    obtain ⟨c, hc, he⟩ := hr.exists_pos_left
      (l.comp_vectorSpan_ne_zero ⟨p, hpF⟩ (by intro he; rw [he] at hdim; omega))
      ((g j).contLinear.comp_vectorSpan_ne_zero ⟨p, hgp⟩
        (by rw [hface]; exact hproper))
    have hev := LinearMap.congr_fun he
      ⟨y - p, (by
        rw [← direction_affineSpan]
        exact (affineSpan ℝ P).vsub_mem_direction hyA (subset_affineSpan ℝ P hpF.1))⟩
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      ContinuousLinearMap.coe_coe, smul_eq_mul, map_sub] at hev
    have hgy := hdiff y
    rw [map_sub] at hgy
    nlinarith
  -- Inactive rows hold on a whole neighborhood; the finite intersection is still a neighborhood.
  have hnear (j : ι) : ∀ᶠ y in 𝓝 p,
      y ∈ affineSpan ℝ P → l y ≤ l p → g j y ≤ 0 := by
    by_cases hj : g j p = 0
    · exact Eventually.of_forall fun y hyA hyl => hactive j hj hyA hyl
    · have hstrict : g j p < 0 := lt_of_le_of_ne (hbound j p hpF.1) hj
      filter_upwards [(g j).continuous.continuousAt.eventually (gt_mem_nhds hstrict)]
        with y hy
      exact fun _ _ => hy.le
  filter_upwards [eventually_all.mpr hnear] with y hy
  constructor
  · intro hyP
    exact ⟨subset_affineSpan ℝ P hyP, hpF.2 y hyP⟩
  · rintro ⟨hyA, hyl⟩
    rw [hpres]
    exact ⟨hyA, fun j => hy j hyA hyl⟩

/-- An exposed facet and its parent have simultaneous hyperplane and inward
half-space models in a ball around every relative interior point of the facet. -/
theorem exists_ball_inter_eq_halfspace_of_facet (hP : TauCeti.IsConvexPolyhedron P)
    {F : Set V} (hF : IsExposed ℝ P F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P))
    {p : V} (hp : p ∈ intrinsicInterior ℝ F) :
    ∃ (l : V →L[ℝ] ℝ) (ε : ℝ), 0 < ε ∧ F = l.toExposed P ∧
      Metric.ball p ε ∩ P =
        Metric.ball p ε ∩ {y | y ∈ affineSpan ℝ P ∧ l y ≤ l p} ∧
      Metric.ball p ε ∩ F =
        Metric.ball p ε ∩ {y | y ∈ affineSpan ℝ P ∧ l y = l p} := by
  obtain ⟨l, hl₀⟩ := hF ⟨p, intrinsicInterior_subset hp⟩
  have hl : F = l.toExposed P := hl₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hP.eventually_mem_iff_of_facet l (hl ▸ hdim) (hl ▸ hp))
  have hpF : p ∈ l.toExposed P := hl ▸ intrinsicInterior_subset hp
  refine ⟨l, ε, hε, hl, ?_, ?_⟩
  · ext y
    exact and_congr_right fun hy => hball (Metric.mem_ball.mp hy)
  · ext y
    simp only [hl, l.mem_toExposed_iff_of_mem hpF, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hyP, hyl⟩
      exact ⟨hy, subset_affineSpan ℝ P hyP, hyl⟩
    · rintro ⟨hy, hyA, hyl⟩
      exact ⟨hy, (hball (Metric.mem_ball.mp hy)).mpr ⟨hyA, hyl.le⟩, hyl⟩

end TauCeti.IsConvexPolyhedron
