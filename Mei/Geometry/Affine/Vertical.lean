/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Generic
public import Mei.Geometry.Affine.Transverse

/-!
# Exceptional endpoints and regular heights

For a finite arrangement of proper affine subspaces in `V × ℝ`, only those
whose directions contain the vertical vector can obstruct an entire vertical
line. Their projections are proper affine subspaces of `V`. Outside the resulting
endpoint arrangement there are only finitely many exceptional heights; inside
it every height is exceptional. Thus the endpoint criterion is exact, and good
heights can be chosen in every nonempty open interval.

This is the projection argument for choosing a regular height in a slice of a
module-probe diagram: boundary strata parallel to the height axis contribute
endpoint exceptions, while every other boundary stratum excludes at most one
height. It does not assert admissibility for a wall family without checking its
boundary and intersection strata.

We reuse `AffineSubspace.subsingleton_preimage_lineMap` for transverse fibers
and `ExceptionalArrangement` for the projected arrangement. The geometric use
follows Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3, arXiv:1503.06183v5.
-/

public section

open Set

namespace AffineSubspace

section Cylinder

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

/-- An affine subspace containing the vertical direction is the full cylinder
over its first-coordinate projection. Empty affine subspaces are allowed. -/
theorem eq_map_fst_prod_top (S : AffineSubspace k (V × k))
    (hS : (0, 1) ∈ S.direction) :
    S = (S.map (AffineMap.fst : V × k →ᵃ[k] V)).prod ⊤ := by
  ext p
  constructor
  · intro hp
    exact ⟨mem_map_of_mem _ hp, mem_top _ _ _⟩
  · rintro ⟨hp, _⟩
    obtain ⟨q, hq, hqp⟩ := mem_map.mp hp
    have hv := S.direction.smul_mem (p.2 - q.2) hS
    have he : (p.2 - q.2) • ((0, 1) : V × k) +ᵥ q = p := by
      ext <;> simp_all
    exact he ▸ S.vadd_mem_of_mem_direction hv hq

/-- Projection of a proper vertical cylinder is still proper. -/
theorem map_fst_ne_top_of_vertical_mem_direction (S : AffineSubspace k (V × k))
    (hne : S ≠ ⊤) (hS : (0, 1) ∈ S.direction) :
    S.map (AffineMap.fst : V × k →ᵃ[k] V) ≠ ⊤ := by
  intro htop
  exact hne ((S.eq_map_fst_prod_top hS).trans (by rw [htop, prod_top_top]))

end Cylinder

variable {k V : Type*} [DivisionRing k] [Infinite k] [AddCommGroup V] [Module k V]

/-- The heights meeting an affine subspace form a finite set exactly when the
vertical line is transverse or its endpoint misses the projected subspace. -/
theorem finite_vertical_fiber_iff (S : AffineSubspace k (V × k)) (x : V) :
    {t : k | (x, t) ∈ S}.Finite ↔
      (0, 1) ∉ S.direction ∨ x ∉ S.map (AffineMap.fst : V × k →ᵃ[k] V) := by
  constructor
  · intro hfin
    by_contra! h
    have hall : {t : k | (x, t) ∈ S} = univ := by
      ext t
      rw [S.eq_map_fst_prod_top h.1]
      simp [h.2]
    exact Set.infinite_univ (hall ▸ hfin)
  · rintro (htrans | hmiss)
    · have h := S.subsingleton_preimage_lineMap (x := (x, 0)) (y := (x, 1))
        (by simpa using htrans)
      apply h.finite.subset
      intro t ht
      simpa [AffineMap.lineMap_apply] using ht
    · exact (Set.finite_empty).subset fun t ht =>
        (hmiss (mem_map_of_mem _ ht)).elim

end AffineSubspace

namespace Mei.ExceptionalArrangement

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The endpoint exceptions obtained by projecting precisely the subspaces
whose directions contain the height axis. -/
noncomputable def verticalProjection (E : ExceptionalArrangement (V × ℝ)) :
    ExceptionalArrangement V := by
  classical
  exact
    ⟨(E.exceptions.filter fun S => (0, 1) ∈ S.direction).image
      (AffineSubspace.map (AffineMap.fst : V × ℝ →ᵃ[ℝ] V)), by
        intro T hT
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
        exact S.map_fst_ne_top_of_vertical_mem_direction
          (E.proper S (Finset.mem_filter.mp hS).1) (Finset.mem_filter.mp hS).2⟩

/-- The projected arrangement consists exactly of the projections of vertical
members of the original arrangement. -/
@[simp]
theorem mem_exceptions_verticalProjection (E : ExceptionalArrangement (V × ℝ))
    (T : AffineSubspace ℝ V) :
    T ∈ E.verticalProjection.exceptions ↔
      ∃ S ∈ E.exceptions, (0, 1) ∈ S.direction ∧ S.map (AffineMap.fst : V × ℝ →ᵃ[ℝ] V) = T := by
  classical
  simp only [verticalProjection, Finset.mem_image, Finset.mem_filter]
  aesop

/-- An endpoint is generic for the projected arrangement exactly when it misses
the projection of each vertical exception. -/
@[simp]
theorem isGeneric_verticalProjection_iff (E : ExceptionalArrangement (V × ℝ)) (x : V) :
    E.verticalProjection.IsGeneric x ↔
      ∀ S ∈ E.exceptions, (0, 1) ∈ S.direction → x ∉ S.map (AffineMap.fst : V × ℝ →ᵃ[ℝ] V) := by
  simp only [isGeneric_iff, mem_exceptions_verticalProjection]
  aesop

/-- A generic endpoint has only finitely many bad heights. Conversely, at an
exceptional endpoint every height meets an original exception. -/
theorem isGeneric_verticalProjection_iff_finite (E : ExceptionalArrangement (V × ℝ))
    (x : V) :
    E.verticalProjection.IsGeneric x ↔ {t : ℝ | ¬ E.IsGeneric (x, t)}.Finite := by
  rw [isGeneric_verticalProjection_iff]
  have hset : {t : ℝ | ¬ E.IsGeneric (x, t)} =
      ⋃ S ∈ E.exceptions, {t : ℝ | (x, t) ∈ S} := by
    ext t
    simp [isGeneric_iff]
  rw [hset]
  constructor
  · intro hx
    exact E.exceptions.finite_toSet.biUnion fun S hS =>
      (S.finite_vertical_fiber_iff x).mpr (by tauto)
  · intro hfin S hS hvertical
    have hf : {t : ℝ | (x, t) ∈ S}.Finite :=
      hfin.subset (subset_iUnion₂_of_subset S hS Subset.rfl)
    exact (S.finite_vertical_fiber_iff x).mp hf |>.resolve_left (not_not.mpr hvertical)

/-- A vertical line has a regular height exactly when its endpoint avoids the
projected arrangement. At an exceptional endpoint every height is forbidden. -/
@[simp]
theorem exists_isGeneric_vertical_iff (E : ExceptionalArrangement (V × ℝ)) (x : V) :
    (∃ t : ℝ, E.IsGeneric (x, t)) ↔ E.verticalProjection.IsGeneric x := by
  constructor
  · rintro ⟨t, ht⟩
    rw [isGeneric_verticalProjection_iff]
    intro S hS hvertical hproj
    apply (E.isGeneric_iff.mp ht) S hS
    rw [S.eq_map_fst_prod_top hvertical]
    exact ⟨hproj, AffineSubspace.mem_top _ _ _⟩
  · intro hx
    obtain ⟨t, ht⟩ := ((E.isGeneric_verticalProjection_iff_finite x).mp hx).infinite_compl.nonempty
    exact ⟨t, not_not.mp ht⟩

/-- Over any endpoint, regular heights form an open subset of the real
line. No topology or finite-dimensionality is needed on the endpoint space. -/
theorem isOpen_isGeneric_vertical (E : ExceptionalArrangement (V × ℝ)) {x : V} :
    IsOpen {t : ℝ | E.IsGeneric (x, t)} := by
  by_cases hx : E.verticalProjection.IsGeneric x
  · have hf := (E.isGeneric_verticalProjection_iff_finite x).mp hx
    simpa only [Set.compl_ofPred, not_not] using hf.isClosed.isOpen_compl
  · have hempty : {t : ℝ | E.IsGeneric (x, t)} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun ht => hx ((E.exists_isGeneric_vertical_iff x).mp ⟨t, ht⟩)
    rw [hempty]
    exact isOpen_empty

/-- Over a generic endpoint, regular heights are dense, so one can choose a
height in any prescribed nonempty open interval. The endpoint space needs no topology. -/
theorem dense_isGeneric_vertical (E : ExceptionalArrangement (V × ℝ)) {x : V}
    (hx : E.verticalProjection.IsGeneric x) : Dense {t : ℝ | E.IsGeneric (x, t)} := by
  have hf := (E.isGeneric_verticalProjection_iff_finite x).mp hx
  simpa only [← compl_eq_univ_sdiff, compl_ofPred, not_not] using (dense_univ.sdiff_finite hf)

end Mei.ExceptionalArrangement
