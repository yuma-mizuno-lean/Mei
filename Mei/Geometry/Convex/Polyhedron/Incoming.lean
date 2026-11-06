/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Boundary
public import Mei.Topology.Algebra.ContinuousAffineMap

/-!
# Boundaries of eventual polyhedral source admission

For a direction along which every defining inequality is nonincreasing,
eventual admission to a polyhedron depends precisely on its tangential rows.
After an affine parameterization of the ray bases, the boundary of this domain
is characterized by a tangential row that is active and nonconstant in the
parameters. Constant zero rows do not create boundary events. The result allows
empty and lower-dimensional sources, redundant inequalities and zero directions.

The active-row argument reuses
`Mei.Convex.exists_nonzero_active_row_of_notMem_interior`. The scalar ray
criterion is shared with the rational-normal source-admission construction.
-/

public section

open Set Filter Topology

namespace ContinuousAffineMap

variable {V W ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [Finite ι]

/-- When all inequalities are nonincreasing along a ray, exactly the tangential
ones constrain eventual admission. Strictly decreasing rows impose no condition
on the base point. -/
theorem eventually_forall_apply_add_smul_le_iff_of_nonpos
    (g : ι → V →ᴬ[ℝ] ℝ) (w : V) (hw : ∀ j, (g j).linear w ≤ 0) (x : V) :
    (∀ᶠ t : ℝ in atTop, ∀ j, g j (x + t • w) ≤ 0) ↔
      ∀ j, (g j).linear w = 0 → g j x ≤ 0 := by
  rw [eventually_all]
  simp only [eventually_apply_add_smul_le_iff]
  constructor
  · intro hx j hj
    rcases hx j with hneg | ⟨_, hle⟩
    · exact (hneg.ne hj).elim
    · exact hle
  · intro hx j
    rcases (hw j).lt_or_eq with hneg | hzero
    · exact Or.inl hneg
    · exact Or.inr ⟨hzero, hx j hzero⟩

variable [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]

/-- The boundary of eventual source admission consists exactly of admitted
parameters with a tight tangential inequality that varies with the parameters.
The affine base map need not be injective or surjective. -/
theorem mem_frontier_eventually_forall_apply_add_smul_le_comp_iff
    (g : ι → V →ᴬ[ℝ] ℝ) (X : W →ᴬ[ℝ] V) (w : V)
    (hw : ∀ j, (g j).linear w ≤ 0) (Q : W) :
    Q ∈ frontier {Y : W | ∀ᶠ t : ℝ in atTop, ∀ j, g j (X Y + t • w) ≤ 0} ↔
      (∀ᶠ t : ℝ in atTop, ∀ j, g j (X Q + t • w) ≤ 0) ∧
        ∃ j, (g j).linear w = 0 ∧ g j (X Q) = 0 ∧
          ((g j).comp X).toAffineMap.linear ≠ 0 := by
  let J := {j : ι // (g j).linear w = 0}
  let G (j : J) := (g j.val).comp X
  have hdomain : {Y : W | ∀ᶠ t : ℝ in atTop, ∀ j, g j (X Y + t • w) ≤ 0} =
      {Y | ∀ j : J, G j Y ≤ 0} := by
    ext Y
    rw [mem_ofPred_eq, eventually_forall_apply_add_smul_le_iff_of_nonpos g w hw]
    exact ⟨fun h j => h j.val j.property, fun h j hj => h ⟨j, hj⟩⟩
  have hclosed : IsClosed {Y : W | ∀ j : J, G j Y ≤ 0} :=
    (TauCeti.isConvexPolyhedron_setOf_forall G).isClosed
  rw [hdomain, hclosed.frontier_eq]
  constructor
  · rintro ⟨hQ, hnot⟩
    obtain ⟨j, hj, hne⟩ := Mei.Convex.exists_nonzero_active_row_of_notMem_interior G hQ hnot
    refine ⟨?_, j.val, j.property, hj, hne⟩
    exact (eventually_forall_apply_add_smul_le_iff_of_nonpos g w hw (X Q)).mpr
      (fun j hj => hQ ⟨j, hj⟩)
  · rintro ⟨hQ, j, hjw, hjQ, hne⟩
    have hmem : ∀ j : J, G j Q ≤ 0 :=
      fun j => (eventually_forall_apply_add_smul_le_iff_of_nonpos g w hw (X Q)).mp
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

end ContinuousAffineMap
