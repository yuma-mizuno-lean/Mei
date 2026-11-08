/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Boundary
public import Mei.Geometry.Convex.Polyhedron.Tangent
public import Mei.LinearAlgebra.AffineSpace.Ray

/-!
# Boundaries of eventual polyhedral source admission

For a direction along which every defining inequality is nonincreasing,
eventual admission to a polyhedron depends precisely on its tangential rows.
After an affine parameterization of the ray bases, the boundary of this domain
is characterized by a tangential row that is active and nonconstant in the
parameters. Constant zero rows do not create boundary events. The result allows
empty and lower-dimensional sources, redundant inequalities and zero directions.
If any defining inequality increases strictly, the admission domain is empty.

The active-row argument reuses
`Mei.Convex.exists_nonzero_active_row_of_notMem_interior`. The scalar ray
criterion is shared with the rational-normal source-admission construction.
The admission domain is a convex polyhedron; its tangent cone at an admitted
base is defined by the tight tangential source rows. The base need not lie in
the source, since strictly decreasing inequalities eventually hold along the ray.
-/

public section

open Set Filter Topology

namespace ContinuousAffineMap

variable {V W ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [Finite ι]

variable [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]

/-- The boundary of eventual source admission consists exactly of admitted
parameters with a tight tangential inequality that varies with the parameters.
The affine base map need not be injective or surjective. -/
theorem mem_frontier_eventually_forall_apply_add_smul_le_comp_iff
    (g : ι → V →ᴬ[ℝ] ℝ) (X : W →ᴬ[ℝ] V) (w : V) (Q : W) :
    Q ∈ frontier {Y : W | ∀ᶠ t : ℝ in atTop, ∀ j, g j (X Y + t • w) ≤ 0} ↔
      (∀ᶠ t : ℝ in atTop, ∀ j, g j (X Q + t • w) ≤ 0) ∧
        ∃ j, (g j).linear w = 0 ∧ g j (X Q) = 0 ∧
          ((g j).comp X).toAffineMap.linear ≠ 0 := by
  by_cases hw : ∀ j, (g j).linear w ≤ 0
  · let J := {j : ι // (g j).linear w = 0}
    let G (j : J) := (g j.val).comp X
    have hdomain : {Y : W | ∀ᶠ t : ℝ in atTop, ∀ j, g j (X Y + t • w) ≤ 0} =
        {Y | ∀ j : J, G j Y ≤ 0} := by
      ext Y
      simp only [mem_ofPred_eq, ← ContinuousAffineMap.coe_toAffineMap]
      rw [AffineMap.eventually_forall_apply_add_smul_le_iff_of_nonpos
        (fun j => (g j).toAffineMap) w hw]
      exact ⟨fun h j => h j.val j.property, fun h j hj => h ⟨j, hj⟩⟩
    have hclosed : IsClosed {Y : W | ∀ j : J, G j Y ≤ 0} :=
      (TauCeti.isConvexPolyhedron_setOf_forall G).isClosed
    rw [hdomain, hclosed.frontier_eq]
    constructor
    · rintro ⟨hQ, hnot⟩
      obtain ⟨j, hj, hne⟩ := Mei.Convex.exists_nonzero_active_row_of_notMem_interior G hQ hnot
      refine ⟨?_, j.val, j.property, hj, hne⟩
      exact (AffineMap.eventually_forall_apply_add_smul_le_iff_of_nonpos
        (fun j => (g j).toAffineMap) w hw (X Q)).mpr
        (fun j hj => hQ ⟨j, hj⟩)
    · rintro ⟨hQ, j, hjw, hjQ, hne⟩
      have hmem : ∀ j : J, G j Q ≤ 0 :=
        fun j => (AffineMap.eventually_forall_apply_add_smul_le_iff_of_nonpos
          (fun j => (g j).toAffineMap) w hw (X Q)).mp
          hQ j.val j.property
      refine ⟨hmem, ?_⟩
      intro hint
      let j' : J := ⟨j, hjw⟩
      have hhalf : Q ∈ interior {Y : W | G j' Y ≤ 0} :=
        interior_mono (s := {Y : W | ∀ j : J, G j Y ≤ 0})
          (fun _ h => h j') hint
      have hopen : IsOpenMap (G j') := AffineMap.isOpenMap_linear_iff.mp
        (IsModuleTopology.isOpenMap_of_surjective (LinearMap.surjective hne))
      have hstrict := hopen.interior_preimage_subset_preimage_interior (s := Iic (0 : ℝ)) hhalf
      have hlt : G j' Q < 0 := by simpa only [interior_Iic, mem_preimage, mem_Iio] using hstrict
      exact (ne_of_lt hlt) hjQ
  · have hnone (Y : W) : ¬ (∀ᶠ t : ℝ in atTop, ∀ j, g j (X Y + t • w) ≤ 0) := by
      simp only [eventually_all, ← ContinuousAffineMap.coe_toAffineMap,
        AffineMap.eventually_apply_add_smul_le_iff]
      intro h
      exact hw fun j => (h j).elim le_of_lt (fun hzero => hzero.1.le)
    have he : {Y : W | ∀ᶠ t : ℝ in atTop, ∀ j, g j (X Y + t • w) ≤ 0} = ∅ :=
      eq_empty_iff_forall_notMem.mpr hnone
    simp only [he, frontier_empty, mem_empty_iff_false, hnone Q, false_and]

end ContinuousAffineMap

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {C : Set V}

/-- The bases of rays eventually admitted by a convex polyhedron form a convex
polyhedron. This includes empty sources and directions outside the recession
cone, for which there are no admitted bases. -/
theorem eventually_add_smul_mem (hC : TauCeti.IsConvexPolyhedron C) (w : V) :
    TauCeti.IsConvexPolyhedron {x : V | ∀ᶠ s : ℝ in atTop, x + s • w ∈ C} := by
  classical
  obtain ⟨n, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hC
  let G (j : Fin n) : V →ᴬ[ℝ] ℝ :=
    if (g j).linear w < 0 then ContinuousAffineMap.const ℝ V (-1 : ℝ)
    else if (g j).linear w = 0 then g j else ContinuousAffineMap.const ℝ V (1 : ℝ)
  have he : {x : V | ∀ᶠ s : ℝ in atTop, x + s • w ∈ {y | ∀ j, g j y ≤ 0}} =
      {x | ∀ j, G j x ≤ 0} := by
    ext x
    simp only [mem_ofPred_eq, eventually_all, ← ContinuousAffineMap.coe_toAffineMap,
      AffineMap.eventually_apply_add_smul_le_iff]
    apply forall_congr'
    intro j
    by_cases hneg : (g j).linear w < 0
    · simp [G, hneg]
    · by_cases hzero : (g j).linear w = 0 <;> simp [G, hneg, hzero]
  rw [he]
  exact TauCeti.isConvexPolyhedron_setOf_forall G

end TauCeti.IsConvexPolyhedron

namespace ContinuousAffineMap

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]

/-- At an admitted ray base, the tangent cone of the admission domain is cut out
by the source rows that are both tangent to the ray and tight at its base.
The base need not belong to the source itself. -/
theorem posTangentConeAt_eventually_forall_apply_add_smul_le_eq
    (g : ι → V →ᴬ[ℝ] ℝ) (w z : V)
    (hz : ∀ᶠ s : ℝ in atTop, ∀ j, g j (z + s • w) ≤ 0) :
    posTangentConeAt {x : V | ∀ᶠ s : ℝ in atTop, ∀ j, g j (x + s • w) ≤ 0} z =
      {q | ∀ j, (g j).linear w = 0 → g j z = 0 → (g j).contLinear q ≤ 0} := by
  have hrows : ∀ j, (g j).linear w < 0 ∨ (g j).linear w = 0 ∧ g j z ≤ 0 := by
    simpa only [eventually_all, ← ContinuousAffineMap.coe_toAffineMap,
      AffineMap.eventually_apply_add_smul_le_iff] using hz
  have hw : ∀ j, (g j).linear w ≤ 0 := fun j =>
    (hrows j).elim le_of_lt (fun h => h.1.le)
  let J := {j : ι // (g j).linear w = 0}
  have he : {x : V | ∀ᶠ s : ℝ in atTop, ∀ j, g j (x + s • w) ≤ 0} =
      {x | ∀ j : J, g j.val x ≤ 0} := by
    ext x
    simp only [mem_ofPred_eq, ← ContinuousAffineMap.coe_toAffineMap]
    rw [AffineMap.eventually_forall_apply_add_smul_le_iff_of_nonpos
        (fun j => (g j).toAffineMap) w hw]
    exact ⟨fun h j => h j.val j.property, fun h j hj => h ⟨j, hj⟩⟩
  rw [he, Mei.posTangentConeAt_setOf_forall_le_zero_eq (fun j : J => g j.val)
    (fun j => (hrows j.val).resolve_left (by simp [j.property]) |>.2)]
  ext q
  exact ⟨fun h j hj => h ⟨j, hj⟩, fun h j => h j.val j.property⟩

end ContinuousAffineMap
