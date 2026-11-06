/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mei.Analysis.Convex.TangentCone
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Tangent cones of convex polyhedra

The positive tangent cone of a finite system of continuous affine inequalities is cut out
by the linear parts of the inequalities tight at the base point. The remaining inequalities
stay strict nearby, so a convex polyhedron locally agrees with the translate of its tangent
cone. No rationality, lattice, or finite-dimensionality assumption is needed.
The comparison also identifies relative boundaries, using the common affine direction
of the support and its tangent cone.
-/

public section

open Filter Topology Set

namespace Mei

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ι : Type*} [Finite ι]

/-- Near a solution of finitely many affine inequalities, only the tight inequalities constrain
membership, through their linear parts applied to the displacement. -/
theorem eventually_forall_affine_le_zero_iff (g : ι → (V →ᴬ[ℝ] ℝ)) {x : V}
    (hx : ∀ j, g j x ≤ 0) :
    ∀ᶠ y in 𝓝 x, (∀ j, g j y ≤ 0) ↔ ∀ j, g j x = 0 → (g j).contLinear (y - x) ≤ 0 := by
  have hloose : ∀ᶠ y in 𝓝 x, ∀ j, g j x < 0 → g j y < 0 :=
    eventually_all.mpr fun j => by
      by_cases hj : g j x < 0
      · exact ((g j).continuous.tendsto x).eventually (gt_mem_nhds hj) |>.mono
          fun y hy _ => hy
      · exact Eventually.of_forall fun y hlt => absurd hlt hj
  filter_upwards [hloose] with y hy
  have hlin (j) : (g j).contLinear (y - x) = g j y - g j x :=
    (g j).contLinear_apply_vsub y x
  constructor
  · intro hyP j hj
    simpa [hlin, hj] using hyP j
  · intro hv j
    rcases (hx j).lt_or_eq with hlt | heq
    · exact (hy j hlt).le
    · simpa [hlin, heq] using hv j heq

/-- The tangent cone of a finite affine-inequality solution set is defined by the linear parts
of exactly the inequalities tight at the base point. -/
theorem posTangentConeAt_setOf_forall_le_zero_eq (g : ι → (V →ᴬ[ℝ] ℝ)) {x : V}
    (hx : ∀ j, g j x ≤ 0) :
    posTangentConeAt {y | ∀ j, g j y ≤ 0} x =
      {v | ∀ j, g j x = 0 → (g j).contLinear v ≤ 0} := by
  ext v
  constructor
  · intro hv j hj
    have hmax : IsMaxOn (g j) {y | ∀ j, g j y ≤ 0} x := by
      intro y hy
      rw [hj]
      exact hy j
    exact hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (g j).hasFDerivWithinAt hv
  · intro hv
    apply mem_posTangentConeAt_of_frequently_mem
    have hlim : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using tendsto_const_nhds.add (hid.smul_const v)
    refine (hlim.eventually (eventually_forall_affine_le_zero_iff g hx) |>.and
      self_mem_nhdsWithin).mono (fun t ⟨ht, htpos⟩ => ?_) |>.frequently
    rw [Set.mem_ofPred_eq, ht, add_sub_cancel_left]
    intro j hj
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos htpos.le (hv j hj)

end Mei

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V} {x : V}

/-- Near a point of a convex polyhedron, membership is membership of the displacement in its
positive tangent cone. -/
theorem eventually_mem_iff_sub_mem_posTangentConeAt (hP : TauCeti.IsConvexPolyhedron P)
    (hx : x ∈ P) : ∀ᶠ y in 𝓝 x, y ∈ P ↔ y - x ∈ posTangentConeAt P x := by
  obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  rw [Mei.posTangentConeAt_setOf_forall_le_zero_eq g hx]
  exact Mei.eventually_forall_affine_le_zero_iff g hx

/-- A convex polyhedron and its tangent cone at one of its points have the same affine
direction, even in infinite-dimensional ambient spaces. -/
theorem direction_affineSpan_posTangentConeAt (hP : TauCeti.IsConvexPolyhedron P)
    (hx : x ∈ P) :
    (affineSpan ℝ (posTangentConeAt P x)).direction = (affineSpan ℝ P).direction := by
  have h0 : (0 : V) ∈ posTangentConeAt P x := by
    simpa using hP.convex.sub_mem_posTangentConeAt hx hx
  have hsub : posTangentConeAt P x ⊆ (affineSpan ℝ P).direction := by
    intro v hv
    have hlim : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
      have hc : Continuous fun t : ℝ => x + t • v := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨t, htlocal, htpos⟩ :=
      ((hlim.eventually (hP.eventually_mem_iff_sub_mem_posTangentConeAt hx)).and
        self_mem_nhdsWithin).exists
    have htP : x + t • v ∈ P := htlocal.mpr (by
      simpa using Mei.smul_mem_posTangentConeAt hv htpos.le)
    have hmem := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ P htP)
      (subset_affineSpan ℝ P hx)
    simpa [smul_smul, htpos.ne'] using (affineSpan ℝ P).direction.smul_mem t⁻¹ hmem
  refine le_antisymm ?_ ?_
  · rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    simpa using hsub hv
  · rw [direction_affineSpan, direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hx]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using vsub_mem_vectorSpan ℝ (hP.convex.sub_mem_posTangentConeAt hx hy) h0

end TauCeti.IsConvexPolyhedron

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  (W : ι → Set V) (hW : ∀ j, TauCeti.IsConvexPolyhedron (W j)) (x : V)

include hW

/-- Near the base point, membership in any member of a finite polyhedral family is
membership of the displacement in its tangent cone, and that member contains the base point. -/
theorem eventually_forall_mem_iff_sub_mem_posTangentConeAt :
    ∀ᶠ y in 𝓝 x, ∀ j, y ∈ W j ↔
      ∃ _ : x ∈ W j, y - x ∈ posTangentConeAt (W j) x := by
  refine eventually_all.mpr fun j => ?_
  by_cases hj : x ∈ W j
  · filter_upwards [(hW j).eventually_mem_iff_sub_mem_posTangentConeAt hj] with y hy
    exact ⟨fun h => ⟨hj, hy.mp h⟩, fun ⟨_, h⟩ => hy.mpr h⟩
  · filter_upwards [(hW j).isClosed.isOpen_compl.mem_nhds hj] with y hy
    exact iff_of_false hy fun ⟨hj', _⟩ => hj hj'

end Mei.Convex

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {P : Set V} {x : V}

open scoped Pointwise in
/-- Near a point of a convex polyhedron, its relative boundary agrees with the translate
of the relative boundary of its positive tangent cone. -/
theorem eventually_mem_intrinsicFrontier_iff_sub_mem_posTangentConeAt
    (hP : TauCeti.IsConvexPolyhedron P) (hx : x ∈ P) :
    ∀ᶠ y in 𝓝 x,
      y ∈ intrinsicFrontier ℝ P ↔ y - x ∈ intrinsicFrontier ℝ (posTangentConeAt P x) := by
  let e := ContinuousAffineEquiv.constVAdd ℝ V x
  have he (v : V) : e v = x + v := (rfl)
  have hzero : (0 : V) ∈ posTangentConeAt P x := by
    simpa using hP.convex.sub_mem_posTangentConeAt hx hx
  have hdir : (affineSpan ℝ (e '' posTangentConeAt P x)).direction =
      (affineSpan ℝ P).direction := by
    -- Translation leaves the vector span unchanged; the cone has the original direction.
    have himage : e '' posTangentConeAt P x = x +ᵥ posTangentConeAt P x := (rfl)
    rw [himage, direction_affineSpan, vectorSpan_vadd, ← direction_affineSpan,
      hP.direction_affineSpan_posTangentConeAt hx]
  have hspan := AffineSubspace.ext_of_direction_eq hdir
    ⟨x, subset_affineSpan ℝ _ ⟨0, hzero, by simp [he]⟩, subset_affineSpan ℝ _ hx⟩
  have hlocal : P =ᶠ[𝓝 x] e '' posTangentConeAt P x := by
    filter_upwards [hP.eventually_mem_iff_sub_mem_posTangentConeAt hx] with y hy
    apply propext
    refine hy.trans ⟨fun hv => ⟨y - x, hv, by simp [he]⟩, ?_⟩
    rintro ⟨v, hv, rfl⟩
    simpa only [he, add_sub_cancel_left] using hv
  filter_upwards [eventually_eventually_nhds.mpr hlocal] with y hy
  rw [Filter.EventuallyEqSet.mem_intrinsicFrontier_iff hy hspan.symm,
    e.intrinsicFrontier_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [he, add_sub_cancel_left] using hv
  · intro hv
    exact ⟨y - x, hv, by simp [he]⟩

end TauCeti.IsConvexPolyhedron
